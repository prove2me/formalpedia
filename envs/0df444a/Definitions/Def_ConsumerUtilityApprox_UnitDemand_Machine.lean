-- Prove2me | Definitions.Def_ConsumerUtilityApprox_UnitDemand_Machine
-- name    : ConsumerUtilityApprox_UnitDemand_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:55:25.997603+00:00
-- url     : https://prove2.me/theorems/319da350-66ba-461d-bded-fa1782f4086a
-- title:
--   The computational model of §2.4: an oracle real RAM with OPT^{1,1} and exact-evaluation oracles, and the decoding of its output as a mechanism description
-- statement:
--   Theorem 3 and Lemma 6 assert that the mechanism "can be computed using polynomially many oracle calls and polynomial additional computation in $n,m,1/\varepsilon$, given oracle access to $\mathrm{OPT}^{1,1}$ and exact evaluation of the required expectations and item allocation probabilities" (§2.4). This item fixes that model.
--
--   **Machine.** A deterministic unit-cost real RAM: real registers, integer pointer registers, a memory indexed by $\mathbb Z$, the instructions of the published real RAM `SmaleNinth.RAMInstr` (real constants, $+,-,\times,\div$, indirect load/store, pointer arithmetic, comparisons and jumps, `accept`/`reject` = halt), plus an **oracle call** (the query is a block of memory cells, the answer is written to another block) and an **output** instruction appending a register to an output tape. On input $(n,m,\varepsilon)$ (memory cells $0,1,2$) the program sees the instance only through the oracle. Cost is the number of executed instructions, each oracle call counting one; a program *halts within* $N$ steps with output $\mathit{out}$ if after some $t\le N$ steps it sits at `accept`/`reject` with tape $\mathit{out}$.
--
--   **Valid oracles.** For an instance, an oracle is valid if it answers
--   - $[1,i,j,q]$ with $q\in[0,1]$ by $\mathrm{OPT}^{1,1}(V_{ij};q)$ and a two-point price law ($\theta\in[0,1]$) implementing it;
--   - $[2,i,0,\text{prices}]$ (a posted-price offer) and $[2,i,1,\ell]$ (a free-lottery offer) by buyer $i$'s exact expected utility and the $m$ exact request probabilities under that offer, with the paper's tie rules;
--   - $[3,i,j]$ by $\mathbb E[V_{ij}]$.
--   Other queries are unconstrained. Statements quantify over **every** valid oracle.
--
--   **Output.** The output tape is read as a mechanism description: $T$ (a natural number), $\rho$, then for each buyer and round the branch probability and, per item, a two-point price and a lottery, then the $Q_{ij}$, then the $\sigma_j$; any other tape is rejected.
--
--   **Formalization Note.** A price is two reals: a flag ($>0$ means $\infty$) and a value. Oracle answers of length $O(m)$ are written in one step. Valid oracles exist exactly when every $\mathrm{OPT}^{1,1}(V_{ij};q)$ has a two-point implementation, which is the mission's statement `posted_price_representation`.
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 8 (§2.4), p. 25 (Lemma 6), p. 26 (Theorem 3), pp. 48–50 (C.5)

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Mechanisms

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-!
Goldner, Lundy, Tsilivis, arXiv:2610.10516 (version of November 3, 2026), §2.4 (p. 8) and
the computational clauses of Lemma 6 (p. 25) and Theorem 3 (p. 26): the computational model.

A deterministic unit-cost real RAM — the published core `SmaleNinth.RAMInstr` (real constants,
`+ − × ÷`, indirect memory access through integer pointers, comparisons and jumps,
`accept`/`reject` = halt) — extended with one oracle instruction and an output tape. The
program receives `(n, m, ε)` in memory cells `0, 1, 2` and nothing else; the value laws are
reachable only through the oracle. Cost = number of executed instructions, an oracle call
counting one.

The oracle answers three kinds of queries (§2.4): `OPT^{1,1}` with an implementing law on at
most two prices; exact expected utility and request probabilities of a posted-price or a
free-lottery offer to a buyer; the means `E[V_ij]`. A *valid* oracle is any function meeting
this specification for the instance at hand.
-/

namespace ConsumerUtilityApprox.UnitDemand

open MultiItemRev.BundlingOpt

/-! ### The machine -/

/-- An instruction: a real-RAM core instruction, an oracle call, or an output instruction. -/
inductive Instr where
  /-- A `SmaleNinth.RAMInstr`, with its own semantics (`accept`/`reject` halt). -/
  | base (ins : SmaleNinth.RAMInstr)
  /-- Oracle call: the query is the list of memory cells `M[p[0]], …, M[p[0] + p[1] − 1]`;
  the answer list is written to `M[p[2]], M[p[2] + 1], …`. -/
  | oracle
  /-- Append `r[i]` to the output tape. -/
  | output (i : ℕ)

/-- A configuration: program counter, real registers, pointer registers, memory, output. -/
structure Config where
  pc : ℕ
  regs : ℕ → ℝ
  ptrs : ℕ → ℤ
  mem : ℤ → ℝ
  out : List ℝ

/-- The core program seen by `SmaleNinth.RAMStep` (non-core instructions are never executed
through it). -/
def baseProgram (P : List Instr) : SmaleNinth.RAMProgram :=
  P.map fun
    | .base ins => ins
    | _ => SmaleNinth.RAMInstr.reject

/-- The machine is halted: the program counter is at an `accept` or `reject`. -/
def IsHalted (P : List Instr) (s : Config) : Prop :=
  P[s.pc]? = some (.base .accept) ∨ P[s.pc]? = some (.base .reject)

/-- One step with oracle `Ω`. A halted configuration, or one whose program counter is outside
the program, is left unchanged. -/
noncomputable def step (Ω : List ℝ → List ℝ) (P : List Instr) (s : Config) : Config :=
  match P[s.pc]? with
  | none => s
  | some (.base _) =>
      let r := SmaleNinth.RAMStep (baseProgram P) ⟨s.pc, s.regs, s.ptrs, s.mem⟩
      ⟨r.pc, r.regs, r.ptrs, r.mem, s.out⟩
  | some .oracle =>
      let ans := Ω (List.ofFn fun k : Fin (s.ptrs 1).toNat => s.mem (s.ptrs 0 + (k : ℕ)))
      ⟨s.pc + 1, s.regs, s.ptrs,
        fun z => if s.ptrs 2 ≤ z ∧ z < s.ptrs 2 + ans.length
          then ans.getD (z - s.ptrs 2).toNat 0 else s.mem z, s.out⟩
  | some (.output i) => ⟨s.pc + 1, s.regs, s.ptrs, s.mem, s.out ++ [s.regs i]⟩

/-- The initial configuration on input `(n, m, ε)`. -/
noncomputable def initConfig (n m : ℕ) (ε : ℝ) : Config :=
  ⟨0, fun _ => 0, fun _ => 0,
    fun z => if z = 0 then (n : ℝ) else if z = 1 then (m : ℝ) else if z = 2 then ε else 0, []⟩

/-- The configuration after `t` steps. -/
noncomputable def run (Ω : List ℝ → List ℝ) (P : List Instr) (n m : ℕ) (ε : ℝ) (t : ℕ) :
    Config :=
  (step Ω P)^[t] (initConfig n m ε)

/-- `P` on input `(n, m, ε)` with oracle `Ω` halts after at most `bound` executed
instructions with output tape `out`. -/
def HaltsWithin (Ω : List ℝ → List ℝ) (P : List Instr) (n m : ℕ) (ε : ℝ) (bound : ℝ)
    (out : List ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ bound ∧ IsHalted P (run Ω P n m ε t) ∧ (run Ω P n m ε t).out = out

/-! ### Encodings of prices and offers -/

/-- A price encoded by two reals: flag `f > 0` means `∞` (no offer), else the price `p`
(negative values read as `0`). -/
noncomputable def decodePrice (f p : ℝ) : ℝ≥0∞ :=
  if 0 < f then ⊤ else ENNReal.ofReal p

/-- A two-point price encoded by five reals `(f₁, p₁, f₂, p₂, θ)` from position `o`. -/
noncomputable def decodeTwoPoint (l : List ℝ) (o : ℕ) : TwoPointPrice :=
  ⟨decodePrice (l.getD o 0) (l.getD (o + 1) 0), decodePrice (l.getD (o + 2) 0) (l.getD (o + 3) 0),
    l.getD (o + 4) 0⟩

/-- Gain `v_j − π` of a served request (`0` for no request). -/
def requestGain {m : ℕ} (v : Fin m → ℝ≥0) : Request m → ℝ
  | none => 0
  | some (j, π) => (v j : ℝ) - π

/-- Expected utility of buyer `i` (values `V_i ∼ ∏_j F_ij`) facing the offer `R`. -/
noncomputable def offerUtility {n m : ℕ} (I : Instance n m) (i : Fin n)
    (R : (Fin m → ℝ≥0) → PMF (Request m)) : ℝ :=
  ∫ v, ∑' r, ((R v) r).toReal * requestGain v r ∂I.buyerLaw i

/-- Probability that buyer `i` facing the offer `R` requests item `j`. -/
noncomputable def offerReqProb {n m : ℕ} (I : Instance n m) (i : Fin n)
    (R : (Fin m → ℝ≥0) → PMF (Request m)) (j : Fin m) : ℝ :=
  ∫ v, ((R v).toOuterMeasure {r | r.map Prod.fst = some j}).toReal ∂I.buyerLaw i

/-- The exact-evaluation answer for an offer: expected utility, then the `m` request
probabilities. -/
noncomputable def offerAnswer {n m : ℕ} (I : Instance n m) (i : Fin n)
    (R : (Fin m → ℝ≥0) → PMF (Request m)) : List ℝ :=
  offerUtility I i R :: List.ofFn (fun j => offerReqProb I i R j)

/-- The oracle specification (§2.4, Theorem 3) for instance `I`. Queries:
* `[1, i, j, q]` with `q ∈ [0,1]`: answer `[OPT^{1,1}(V_ij; q), f₁, p₁, f₂, p₂, θ]` with
  `θ ∈ [0,1]` and the two-point price implementing `OPT^{1,1}(V_ij; q)`;
* `[2, i, 0] ++ (5m reals)`: the posted-price offer with the two-point prices encoded item by
  item; answer `offerAnswer` (exact, ties as specified);
* `[2, i, 1] ++ (ℓ_1, …, ℓ_m)`: the free-lottery offer; answer `offerAnswer`;
* `[3, i, j]`: answer `[E[V_ij]]`.
Other queries are unconstrained. -/
def IsValidOracle {n m : ℕ} (I : Instance n m) (Ω : List ℝ → List ℝ) : Prop :=
  (∀ (i : Fin n) (j : Fin m) (q : ℝ), 0 ≤ q → q ≤ 1 →
    let a := Ω [1, ((i : ℕ) : ℝ), ((j : ℕ) : ℝ), q]
    a.length = 6 ∧ a.getD 0 0 = OPT11 (I.F i j) q ∧ 0 ≤ a.getD 5 0 ∧ a.getD 5 0 ≤ 1 ∧
      IsImplementing (I.F i j) q (decodeTwoPoint a 1)) ∧
  (∀ (i : Fin n) (rest : List ℝ), rest.length = 5 * m →
    Ω ([2, ((i : ℕ) : ℝ), 0] ++ rest) =
      offerAnswer I i (pricingRequest (fun j => decodeTwoPoint rest (5 * (j : ℕ))))) ∧
  (∀ (i : Fin n) (rest : List ℝ), rest.length = m →
    Ω ([2, ((i : ℕ) : ℝ), 1] ++ rest) =
      offerAnswer I i (lotteryRequest (fun j => rest.getD (j : ℕ) 0))) ∧
  (∀ (i : Fin n) (j : Fin m), Ω [3, ((i : ℕ) : ℝ), ((j : ℕ) : ℝ)] = [mean (I.F i j)])

/-! ### Reading a mechanism description from the output tape -/

/-- Decode the output tape as a `MechDescription n m`. Layout: `T` (a natural number), `ρ`;
then for each buyer `i` and round `t < T` (in the order `i * T + t`) a block of `1 + 6m`
reals: `w`, then for each item the two-point price `(f₁, p₁, f₂, p₂, θ)` and the lottery `ℓ`;
then `Q i j` (in the order `i * m + j`); then `σ j`. Any other tape decodes to `none`. -/
noncomputable def decodeDescription (n m : ℕ) (out : List ℝ) : Option (MechDescription n m) := by
  classical
  exact
    let T := ⌊out.getD 0 0⌋₊
    let blk := 1 + 6 * m
    let base : Fin n → ℕ → ℕ := fun i t => 2 + ((i : ℕ) * T + t) * blk
    let qOff := 2 + n * T * blk
    let σOff := qOff + n * m
    if (T : ℝ) = out.getD 0 0 ∧ out.length = σOff + m then
      some
        { T := T
          ρ := out.getD 1 0
          w := fun i t => out.getD (base i t) 0
          price := fun i t j => decodeTwoPoint out (base i t + 1 + 6 * (j : ℕ))
          lottery := fun i t j => out.getD (base i t + 1 + 6 * (j : ℕ) + 5) 0
          Q := fun i j => out.getD (qOff + (i : ℕ) * m + (j : ℕ)) 0
          σ := fun j => out.getD (σOff + (j : ℕ)) 0 }
    else none

end ConsumerUtilityApprox.UnitDemand


