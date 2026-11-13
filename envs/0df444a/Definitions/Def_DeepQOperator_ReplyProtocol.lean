-- Prove2me | Definitions.Def_DeepQOperator_ReplyProtocol
-- name    : DeepQOperator_ReplyProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:03:18.28065+00:00
-- url     : https://prove2.me/theorems/889965ff-0389-4115-ba0b-3a13fad75c0f
-- title:
--   Scalar-reply protocols: fixed, adaptive and two-stage designs, hard reply budgets, worst-input regret
-- statement:
--   A **scalar-reply protocol** with parameter $\theta\in\mathbb R^\iota$ and a random seed $\omega$ from a seed space $(\Omega,\mu)$ proceeds in fields. At each history $h$ of previously received symbols it either stops or requests one field: an affine scalar $\alpha^{\mathsf T}\theta+\alpha_0$, a length $d\ge1$, and a **quantizer** that returns a symbol in $\{0,\dots,2^d-1\}$. The quantizer sees only that scalar, the seed, and the earlier symbols; the algorithm never sees the unquantized value. The final decision is a function of the seed and the received symbols. The seed is chosen independently of the input and includes the decision randomness.
--
--   1. The protocol has **hard reply budget** $B$ on an input set $S$ if, for every $\theta\in S$ and every seed, the lengths of the fields along the run sum to at most $B$.
--   2. It is **fixed** if the decision to ask a field, its affine map and its length depend on the history only through the number of earlier symbols, so that the whole list of fields is selected from the seed and every listed field is paid.
--   3. It is **at most two-stage** if, for some seed-dependent stage-one length $k(\omega)$, fields at positions below $k(\omega)$ depend only on the position, and later fields only on the first $k(\omega)$ symbols and the position.
--   4. It is **measurable** if every component is measurable in the seed and each quantizer is jointly measurable in the seed and the scalar.
--   5. For the family (6), it is **raw** if every requested scalar is a site of the raw dictionary, and it **uses uniform quantizers** if every field of length $d$ uses $j_d$ of (41).
--
--   The **worst-input expected regret** on (6) is
--   $$\sup_{\theta\in P_{cb}}\ \mathbb E_\omega\,\ell\big(A(\theta;\omega),\theta\big).$$
--
--   **Formalization Note** A protocol is a structure with the fields `ask`, `coef`, `const`, `len`, `quant`, `decide` and two validity proofs (asked lengths are $\ge1$; symbols are below $2^{\text{len}}$). Zero-bit fields are excluded because the paper removes them as constant. The run uses fuel $B$; under a hard budget $B$ it is the complete run. The fixed class lets a quantizer read earlier symbols (the larger class). The regret is a supremum of lower Lebesgue integrals in $[0,\infty]$. `IsBudgetNode` describes the internal nodes of the reply tree truncated at the budget (Appendix E.5).
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), §3.1 p.4, Appendix A p.13, §5 eq. (20) p.8 (PDF pp.7, 16, 11)

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_Quantizer

open MeasureTheory

namespace DeepQOperator

/-!
# Scalar-reply protocols: fixed and adaptive designs, hard reply budgets, worst-input regret

Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), §3.1 p.4 (PDF p.7), Appendix A p.13
(PDF p.16), §5 eq. (20) p.8 (PDF p.11), Appendix E.3–E.4 p.25 (PDF p.28).

A query returns a symbol in an alphabet of size at most `2^d` and costs `d` bits. The symbol is a
measurable function of that scalar value, the shared random seed, and the previously received
symbols; the algorithm never sees the unquantized value. An adaptive design chooses the next
affine map, quantizer and length from earlier symbols and the seed; a fixed design chooses its
whole list from the seed alone and pays for every field. The sum of lengths is at most `B` on every
input and random path. The seed is independent of the input and includes the final-decision
randomness.

**Formalization Note.**
* A protocol over a parameter index type `ι` and a seed type `Ω` is given by its behaviour at
  every history `h : List ℕ` of earlier symbols: whether to ask a further field (`ask`), the field's
  affine map (`coef`, `const`), its length (`len`), its quantizer (`quant`, which receives only the
  field's scalar `αᵀθ + α₀`, the seed and `h`), and the final decision (`decide`, which receives only
  the seed and the symbols). `ask = false` is stopping.
* Every asked field has length `≥ 1` and its symbols lie in `{0, …, 2^len - 1}`. The paper allows
  `d = 0`; a zero-bit field is constant and is removed (App. A: "A zero-bit reply is constant and can
  be removed"), so lengths `≥ 1` lose no protocol. An alphabet of size at most `2^d` is a subset of
  `{0, …, 2^d - 1}`.
* `runFrom P θ ω k h` runs at most `k` further fields from history `h`. With a hard budget `B`
  (`HardBudgetOn P S B`: for every `θ ∈ S`, every seed `ω` and every `k` the charged lengths along
  the run total at most `B`) the run asks at most `B` fields, so `transcript P B θ ω` (fuel `B`) is the
  complete transcript and `decision P B θ ω` the final action.
* `IsFixed`: the map, length and the decision to ask a field depend on the history only through its
  length, so the list of fields is fixed by the seed, and every field of the list is asked and paid.
  The quantizer of a field may still read earlier symbols (App. A's general rule); this is the larger
  of the two readings of "preselects its … individual quantizers", hence the stronger lower bound.
* `IsAtMostTwoStage`: there is a seed-dependent stage-one length `k ω`; fields at positions
  `< k ω` depend only on the position, and later fields only on the first `k ω` symbols and the
  position (the quantizer included).
* `IsMeasurable`: for every history, every component is measurable in the seed and the quantizer is
  jointly measurable in (seed, scalar) (§5: "Query and decoding maps are jointly measurable").
* `worstRegret`: `sup_{θ ∈ P_cb} E_ω ℓ(A(θ; ω), θ)` as an `ℝ≥0∞`-valued lower Lebesgue integral and a
  supremum; it need not be attained.
-/

/-- A scalar-reply protocol with parameter coordinates `ι` and seed space `Ω`. -/
structure ReplyProtocol (ι : Type) (Ω : Type*) where
  /-- whether a further field is requested at this history (`false` = stop) -/
  ask : Ω → List ℕ → Bool
  /-- the coefficient vector `α` of the requested affine scalar `αᵀθ + α₀` -/
  coef : Ω → List ℕ → ι → ℝ
  /-- the constant `α₀` of the requested affine scalar -/
  const : Ω → List ℕ → ℝ
  /-- the charged length `d` of the requested field -/
  len : Ω → List ℕ → ℕ
  /-- the field's quantizer: seed, earlier symbols, and the field's own scalar value -/
  quant : Ω → List ℕ → ℝ → ℕ
  /-- the final decision (`true` is `+`) from the seed and the received symbols -/
  decide : Ω → List ℕ → Bool
  len_pos : ∀ ω h, ask ω h = true → 1 ≤ len ω h
  quant_lt : ∀ ω h x, ask ω h = true → quant ω h x < 2 ^ len ω h

namespace ReplyProtocol

variable {ι : Type} [Fintype ι] {Ω : Type*}

/-- The symbol returned by the field requested at history `h` on input `θ`. -/
noncomputable def reply (P : ReplyProtocol ι Ω) (ω : Ω) (h : List ℕ) (θ : ι → ℝ) : ℕ :=
  P.quant ω h (∑ i, P.coef ω h i * θ i + P.const ω h)

/-- Run at most `k` further fields from history `h`. -/
noncomputable def runFrom (P : ReplyProtocol ι Ω) (θ : ι → ℝ) (ω : Ω) : ℕ → List ℕ → List ℕ
  | 0, h => h
  | k + 1, h => if P.ask ω h then P.runFrom θ ω k (h ++ [P.reply ω h θ]) else h

/-- The transcript with fuel `B` (the complete transcript under a hard budget `B`). -/
noncomputable def transcript (P : ReplyProtocol ι Ω) (B : ℕ) (θ : ι → ℝ) (ω : Ω) : List ℕ :=
  P.runFrom θ ω B []

/-- The final action on input `θ` and seed `ω`. -/
noncomputable def decision (P : ReplyProtocol ι Ω) (B : ℕ) (θ : ι → ℝ) (ω : Ω) : Bool :=
  P.decide ω (P.transcript B θ ω)

/-- The total charged length of the fields that produced the history `h`. -/
def pathCost (P : ReplyProtocol ι Ω) (ω : Ω) (h : List ℕ) : ℕ :=
  ∑ j ∈ Finset.range h.length, P.len ω (h.take j)

/-- Hard reply budget `B` on the input set `S`: on every input of `S` and every random path, the sum
of the charged lengths is at most `B`. -/
def HardBudgetOn (P : ReplyProtocol ι Ω) (S : Set (ι → ℝ)) (B : ℕ) : Prop :=
  ∀ θ ∈ S, ∀ ω k, P.pathCost ω (P.runFrom θ ω k []) ≤ B

/-- An internal node of the reply tree at seed `ω`, truncated at budget `B`: every earlier symbol was
produced by an asked field and lies in its alphabet, a field is asked at `h`, and its cost fits the
remaining budget. -/
def IsBudgetNode (P : ReplyProtocol ι Ω) (ω : Ω) (B : ℕ) (h : List ℕ) : Prop :=
  (∀ j (hj : j < h.length), P.ask ω (h.take j) = true ∧ h[j] < 2 ^ P.len ω (h.take j)) ∧
    P.ask ω h = true ∧ P.pathCost ω h + P.len ω h ≤ B

/-- Fixed design: the list of fields (maps, lengths, and how many) is fixed by the seed. -/
def IsFixed (P : ReplyProtocol ι Ω) : Prop :=
  ∀ ω (h h' : List ℕ), h.length = h'.length →
    P.ask ω h = P.ask ω h' ∧ P.coef ω h = P.coef ω h' ∧ P.const ω h = P.const ω h' ∧
      P.len ω h = P.len ω h'

/-- The field requested at `h` and at `h'` is the same (map, length, quantizer, asking). -/
def SameField (P : ReplyProtocol ι Ω) (ω : Ω) (h h' : List ℕ) : Prop :=
  P.ask ω h = P.ask ω h' ∧ P.coef ω h = P.coef ω h' ∧ P.const ω h = P.const ω h' ∧
    P.len ω h = P.len ω h' ∧ P.quant ω h = P.quant ω h'

/-- At most two stages: a stage-one list fixed by the seed, then a stage-two list fixed by the
stage-one symbols. -/
def IsAtMostTwoStage (P : ReplyProtocol ι Ω) : Prop :=
  ∃ k : Ω → ℕ, ∀ ω (h h' : List ℕ), h.length = h'.length →
    (h.length < k ω ∨ h.take (k ω) = h'.take (k ω)) → P.SameField ω h h'

/-- Measurability in the seed, joint measurability of the quantizers. -/
def IsMeasurable [MeasurableSpace Ω] (P : ReplyProtocol ι Ω) : Prop :=
  ∀ h : List ℕ, Measurable (fun ω => P.ask ω h) ∧ Measurable (fun ω => P.coef ω h) ∧
    Measurable (fun ω => P.const ω h) ∧ Measurable (fun ω => P.len ω h) ∧
    Measurable (fun p : Ω × ℝ => P.quant p.1 h p.2) ∧ Measurable (fun ω => P.decide ω h)

end ReplyProtocol

/-- Raw protocol for the family (6): every requested scalar is a site of the raw dictionary. -/
def IsRaw {m : ℕ} {Ω : Type*} (P : ReplyProtocol (Coord m) Ω) : Prop :=
  ∀ ω h, P.ask ω h = true → (P.coef ω h, P.const ω h) ∈ rawDictionary m

/-- Every requested field uses the uniform quantizer `j_d` of (41) with its own length `d`. -/
def UsesUniformQuantizers {ι : Type} {Ω : Type*} (P : ReplyProtocol ι Ω) : Prop :=
  ∀ ω h, P.ask ω h = true → ∀ x, P.quant ω h x = jEnc (P.len ω h) x

/-- Worst-input expected regret on the family (6) with fuel `B`:
`sup_{θ ∈ P_cb} E_ω ℓ(A(θ; ω), θ)`. -/
noncomputable def worstRegret (m : ℕ) (γ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (P : ReplyProtocol (Coord m) Ω) (B : ℕ) : ENNReal :=
  ⨆ θ ∈ Pcb m, ∫⁻ ω, ENNReal.ofReal (loss m γ (P.decision B θ ω) θ) ∂μ

end DeepQOperator


