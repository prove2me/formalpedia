-- Prove2me | Definitions.Def_F3SubsetSum_Supplement_SubsetSumQ
-- name    : F3SubsetSum_Supplement_SubsetSumQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:29:33.855418+00:00
-- url     : https://prove2.me/theorems/62a64e45-df5d-43c3-977e-17b968839b3c
-- title:
--   $\mathbb F_q^n$-Subset-Sum: solutions, machine codes, computation within $T$ steps, average-case success
-- statement:
--   Fix a prime $q\ge3$. An instance of **$\mathbb F_q^n$-Subset-Sum** (Problem 1.9) is a tuple $h=(h_1,\dots,h_m)$ of vectors in $\mathbb F_q^n$; a **solution** is a nonempty set $S\subseteq[m]$ with
--   $$
--   \sum_{i\in S}h_i=0.
--   $$
--   A Subset-Sum algorithm maps $(n,m,h)$ to a set $S\subseteq[m]$; it fails by returning a non-solution. Its **average-case success probability** is the fraction of the $q^{nm}$ instances on which its output is a solution, i.e. the success probability for $h_1,\dots,h_m$ independent and uniform.
--
--   A machine $M$ **computes** the algorithm within $T$ steps on size $(n,m)$ if on the code of every instance (the unary words $1^n0\,1^m0$, then every entry $v\in\{0,\dots,q-1\}$ as $1^v0$) it halts within $T$ steps with the $m$ indicator bits of the algorithm's output.
--
--   These objects state the classical algorithms of Theorems 1.10 and 1.11.
--
--   **Formalization Note** The machine is Mathlib's multi-stack Turing machine with Boolean alphabets, run with the published `HMBinPacking.OutputsWithin`; the unary codes are the published `F3SubsetSum.unaryD`. The published `F3SubsetSum.IsZeroSubsetSum` is the case $q=3$.
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Problem 1.9, p.7; Theorems 1.10, 1.11, p.7

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_F3SubsetSum_MachineCodes

set_option autoImplicit false

namespace F3SubsetSum.Supplement

/-- **Zero subset sum over `F_q`** (Problem 1.9). Kothari, Metger, O'Donnell, Shutty, Wu,
arXiv:2609.40321v1, Problem 1.9, p.7: "Let q ≥ 3 be a prime. Given input vectors
h_1, …, h_m ∈ F_q^n, the task is to find a nonempty S ⊆ [m] such that Σ_{i∈S} h_i = 0."

`IsZeroSubsetSumQ h S` says that `S` is a solution of the instance `h = (h₁, …, h_m)`, each
`h i ∈ F_qⁿ`: `S` is nonempty and the vectors indexed by `S` sum to `0`.

**Formalization Note** `[m]` is `Fin m` (0-based) and `F_qⁿ` is `Fin n → ZMod q`. The published
`F3SubsetSum.IsZeroSubsetSum` is the case `q = 3`. -/
def IsZeroSubsetSumQ {q n m : ℕ} (h : Fin m → Fin n → ZMod q) (S : Finset (Fin m)) : Prop :=
  S.Nonempty ∧ ∑ i ∈ S, h i = 0

/-- A **Subset-Sum algorithm** over `F_q` (as a function): on the sizes `n, m` and an instance
`h ∈ (F_qⁿ)^m` it returns a set `S ⊆ [m]`. Failure is reported by returning a set that is not a
solution (for instance `∅`). -/
abbrev SubsetSumAlg (q : ℕ) : Type :=
  (n m : ℕ) → (Fin m → Fin n → ZMod q) → Finset (Fin m)

/-- **Input code of an `F_qⁿ`-Subset-Sum instance** `h = (h_1, …, h_m)`: `1ⁿ 0 1ᵐ 0`, then
`h_1, …, h_m` (each as its `n` entries in order), every entry `v ∈ F_q` written `1^v 0` with
`v ∈ {0, …, q − 1}` (the published `F3SubsetSum.unaryD`). -/
def encodeSubsetSumInstance {q n m : ℕ} (h : Fin m → Fin n → ZMod q) : List Bool :=
  unaryD n ++ unaryD m ++
    (List.finRange m).flatMap (fun i => (List.finRange n).flatMap (fun j => unaryD (h i j).val))

/-- **Output code of a set** `S ⊆ [m]`: its `m` indicator bits, in the order `1, …, m`. -/
def encodeSubset {m : ℕ} (S : Finset (Fin m)) : List Bool :=
  (List.finRange m).map (fun i => decide (i ∈ S))

/-- **`M` computes the Subset-Sum algorithm `Alg` on all `(n, m)`-inputs within `T` steps.**
`M` is a deterministic multi-stack Turing machine with Boolean input and output alphabets
(Mathlib's `Turing.TM2ComputableAux Bool Bool`); on the code of **every** instance
`h ∈ (F_qⁿ)^m` (solvable or not, whether or not `Alg` succeeds on it) it halts within `T` steps
with the code of `Alg n m h` on its output stack (the published `HMBinPacking.OutputsWithin`).

**Formalization Note** The paper names no machine model ("deterministic classical algorithm …
runs in time poly(m)", Theorems 1.10, 1.11, p.7). A Turing machine and a RAM differ by polynomial
factors, which a `poly(m)` bound absorbs. -/
def SubsetSumComputesWithin {q : ℕ} (M : Turing.TM2ComputableAux Bool Bool) (Alg : SubsetSumAlg q)
    (n m T : ℕ) : Prop :=
  ∀ h : Fin m → Fin n → ZMod q,
    HMBinPacking.OutputsWithin M (encodeSubsetSumInstance h) (encodeSubset (Alg n m h)) T

open Classical in
/-- **Average-case success probability** of a Subset-Sum algorithm (Problem 1.9, p.7: "In the
average case, h_i's are independently uniform"): the number of instances `h ∈ (F_qⁿ)^m` on which
`Alg n m h` is a solution, divided by `q^{nm}`. -/
noncomputable def avgSuccessProb {q : ℕ} [NeZero q] (Alg : SubsetSumAlg q) (n m : ℕ) : ℝ :=
  ((Finset.univ.filter fun h : Fin m → Fin n → ZMod q => IsZeroSubsetSumQ h (Alg n m h)).card : ℝ) /
    (q : ℝ) ^ (n * m)

end F3SubsetSum.Supplement


