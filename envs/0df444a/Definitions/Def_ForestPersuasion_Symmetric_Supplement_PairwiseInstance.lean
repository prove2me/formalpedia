-- Prove2me | Definitions.Def_ForestPersuasion_Symmetric_Supplement_PairwiseInstance
-- name    : ForestPersuasion_Symmetric_Supplement_PairwiseInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:16:53.070942+00:00
-- url     : https://prove2.me/theorems/7e99b9a4-1dda-4e26-86ac-4826c915acb0
-- title:
--   Pairwise-supermodular persuasion instances, 3-chain hierarchies, input codes and the FPTAS predicate
-- statement:
--   An instance consists of $n$ receivers arranged in a communication hierarchy (one optional parent per receiver), a rational prior $\mu=\Pr[\omega=1]$, the four rational payoffs $v_i(\omega,a)$ of each receiver $i$, singleton weights $a_i\in\mathbb Q$ and pair weights $b_{ij}\in\mathbb Q$. It is **valid** when the persuasion model satisfies the standing assumptions of §2 (acyclic hierarchy, $0<\mu<1$, $v_i(1,1)-v_i(1,0)\ge0$ and $v_i(0,1)-v_i(0,0)<0$) and every $a_i\ge0$, $b_{ij}\ge0$. The sender's utility is
--
--   $$u(S)=\sum_{i\in S}a_i+\sum_{\substack{i,j\in S\\ i<j}}b_{ij},\qquad S\subseteq[n],$$
--
--   which is nonnegative, monotone and supermodular because all weights are nonnegative.
--
--   The hierarchy is a **disjoint union of chains of 3 receivers** when the receivers can be labelled $v_1,v_2,v_3$ for $v=1,\dots,k$ (so $n=3k$) with each $v_1$ a root, $v_1$ the parent of $v_2$ and $v_2$ the parent of $v_3$, and no other edges. Since each receiver observes the signals of all its descendants, $v_1$ dominates $v_2,v_3$ and $v_2$ dominates $v_3$; receivers of different chains are incomparable.
--
--   An instance is written in binary: $n$, the parent entries, $\mu$, the four payoffs of every receiver, the $n$ weights $a_i$, and the $n^2$ weights $b_{ij}$ in lexicographic order, every number with the self-delimiting binary code of the base mission. The input of an approximation scheme is this code followed by an integer $N\ge1$ in unary, the accuracy being $\varepsilon=1/N$.
--
--   A function $g$ from (instance, $N$) to rationals is an **FPTAS on the 3-chain class** when one multi-stack machine computes $g$ on all inputs within $P(\text{input length})$ steps for one polynomial $P$ (so in time polynomial in the instance length and in $1/\varepsilon$), and for every valid instance whose hierarchy is a disjoint union of 3-receiver chains and every $N\ge1$,
--
--   $$|g(I,N)-V^*(I)|\le V^*(I)/N,$$
--
--   where $V^*$ is the sender's optimal value over all signaling schemes.
--
--   These objects state the hardness result of §4.1 (Theorem 6).
-- source:
--   Konstantin Zabarnyi, Designing Information in a Forest: Algorithmic Aspects, STOC 2027 submission #271 (October 2026; PDF dated November 2, 2026), §2 (PDF pp. 6–8, printed pp. 5–7), §4.1 Theorem 6 (PDF p. 10, printed p. 9), App. E Steps 1–5 (PDF pp. 24–28, printed pp. 23–27). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/271.pdf

import Mathlib
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_ForestPersuasion_Symmetric_Encoding

open scoped NNReal ENNReal
open Classical
noncomputable section

namespace ForestPersuasion.Symmetric.Supplement

open ForestPersuasion.Symmetric

/-- Raw numerical data of a persuasion instance whose sender utility is an explicit
nonnegative pairwise set function (App. E, PDF pp. 24–27): `n` receivers, one optional parent
per receiver, a rational prior, the four rational payoffs `v_i(ω, a)` of each receiver,
singleton weights `a_i` and pair weights `b_{ij}` (read only for `i < j`). -/
structure PairwiseRawInstance where
  n : ℕ
  parent : Fin n → Option (Fin n)
  prior : ℚ
  receiverUtility : Fin n → Bool → Bool → ℚ
  single : Fin n → ℚ
  pair : Fin n → Fin n → ℚ

/-- The persuasion model of §2 (published `Model`) underlying the raw data. -/
def PairwiseRawInstance.model (I : PairwiseRawInstance) : Model I.n where
  hierarchy := ⟨I.parent⟩
  prior := I.prior
  receiverUtility i w a := I.receiverUtility i w a

/-- Validity: the published §2 standing assumptions on the model (acyclic hierarchy,
`0 < µ < 1`, payoff sign conditions) and nonnegative singleton and pair weights. -/
def PairwiseRawInstance.Valid (I : PairwiseRawInstance) : Prop :=
  I.model.Valid ∧ (∀ i, 0 ≤ I.single i) ∧ ∀ i j, 0 ≤ I.pair i j

/-- Valid instances. -/
abbrev PairwiseInstance := {I : PairwiseRawInstance // I.Valid}

/-- `u(S) = Σ_{i ∈ S} a_i + Σ_{i ∈ S} Σ_{j ∈ S, i < j} b_{ij}`. -/
def pairwiseValue {n : ℕ} (a : Fin n → ℚ) (b : Fin n → Fin n → ℚ) (S : Finset (Fin n)) : ℚ :=
  (∑ i ∈ S, a i) + ∑ i ∈ S, ∑ j ∈ S.filter (fun j => i < j), b i j

/-- The sender utility of a valid instance, as a published `SenderUtility` (values in `ℝ≥0`).
Nonnegativity follows from the nonnegative weights; monotonicity and supermodularity are
consequences of the representation, not extra hypotheses. -/
def PairwiseInstance.utility (I : PairwiseInstance) : SenderUtility I.val.n :=
  fun S => ⟨(pairwiseValue I.val.single I.val.pair S : ℝ), by
    have h : 0 ≤ pairwiseValue I.val.single I.val.pair S :=
      add_nonneg (Finset.sum_nonneg fun i _ => I.property.2.1 i)
        (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => I.property.2.2 i j)
    exact_mod_cast h⟩

/-- The hierarchy is a disjoint union of chains of 3 receivers (Theorem 6, PDF p. 10;
App. E Step 1, PDF p. 24): the receivers are `e(v, r)` for `v < k`, `r < 3`, each `e(v, 0)` is a
root, `e(v, 0)` is the parent of `e(v, 1)`, and `e(v, 1)` is the parent of `e(v, 2)`. With the
published convention (receiver `i` observes the signals of its descendants), `e(v, 0)` dominates
`e(v, 1)` and `e(v, 2)`, and `e(v, 1)` dominates `e(v, 2)`. No other edges exist. -/
def IsDisjointThreeChains {n : ℕ} (G : Hierarchy n) : Prop :=
  ∃ (k : ℕ) (e : Fin k × Fin 3 ≃ Fin n), ∀ v : Fin k,
    G.parent (e (v, 0)) = none ∧
    G.parent (e (v, 1)) = some (e (v, 0)) ∧
    G.parent (e (v, 2)) = some (e (v, 1))

/-- Binary code of the raw data, with the published `encodeNat` / `encodeRat`: `n`, the parent
entries (0 for a root, `j+1` for parent `j`), the prior, the four payoffs of each receiver, the
`n` singleton weights in increasing order, and the `n²` pair weights `b_{ij}` with `(i, j)` in
lexicographic order. -/
def encodePairwiseRaw (I : PairwiseRawInstance) : List Bool :=
  encodeNat I.n ++
    (List.finRange I.n).flatMap (fun i => encodeNat (match I.parent i with
      | none => 0
      | some j => j.val + 1)) ++
    encodeRat I.prior ++
    (List.finRange I.n).flatMap (fun i =>
      [false, true].flatMap (fun w =>
        [false, true].flatMap (fun a => encodeRat (I.receiverUtility i w a)))) ++
    (List.finRange I.n).flatMap (fun i => encodeRat (I.single i)) ++
    (List.finRange I.n).flatMap (fun i =>
      (List.finRange I.n).flatMap (fun j => encodeRat (I.pair i j)))

/-- Input code of an approximation scheme: the instance code followed by the accuracy
parameter `N` (accuracy `ε = 1/N`) in unary, so that time polynomial in the code length is time
polynomial in the instance length and in `1/ε`. -/
def encodeFPTASInput (x : PairwiseInstance × ℕ+) : List Bool :=
  encodePairwiseRaw x.1.val ++ List.replicate (x.2 : ℕ) true

/-- A fully polynomial-time approximation scheme for the sender's optimal value `V*` on the
class of instances whose hierarchy is a disjoint union of 3-receiver chains: one machine and one
polynomial (time polynomial in the instance length and `N = 1/ε`) computing `g`, and on every
such instance, for every `N ≥ 1`, `|g(I, N) − V*| ≤ V*/N`. `V*` is the published `Vstar`
(supremum over actual signaling schemes). Outside the class `g` is unconstrained but is still
computed by the same machine. -/
def IsThreeChainFPTAS (g : PairwiseInstance × ℕ+ → ℚ) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime encodeFPTASInput encodeRat g) ∧
  ∀ (I : PairwiseInstance) (N : ℕ+), IsDisjointThreeChains I.val.model.hierarchy →
    |(g (I, N) : ℝ) - Vstar I.val.model I.utility| ≤ Vstar I.val.model I.utility / (N : ℝ)

end ForestPersuasion.Symmetric.Supplement


