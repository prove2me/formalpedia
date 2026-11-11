-- Prove2me | Definitions.Def_RandModSubsetSum_Problem
-- name    : RandModSubsetSum_Problem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:01:00.074279+00:00
-- url     : https://prove2.me/theorems/df98c307-8f6c-4389-8a43-71c8bf52ea5a
-- title:
--   Random modular subset sum and Problem 3.1: constants, input and output words, solutions
-- statement:
--   The problem objects of Theorems 1.1, 3.2, 7.1 and 7.2.
--
--   1. Constants: $\delta_0=0.999996$, $\beta=\max\{B,2\}$, $c_B=\min\{10^{-24},(100\beta)^{-1}\}$, and the modulus range $2^{\delta_0n}\le Q\le 2^{Bn}$ (equivalently $\delta_0n\le\log_2Q\le Bn$).
--   2. **Modular problem**: coefficients $a\in(\mathbb Z/Q\mathbb Z)^n$ (representatives in $\{0,\dots,Q-1\}$), target $t=a\cdot x\bmod Q$; a binary $y$ is a solution if $a\cdot y\equiv t\pmod Q$. The input word is $(Q,t,a_1,\dots,a_n)$.
--   3. **Problem 3.1**: integer target $t=a\cdot x$; $y\in\{0,1\}^n$ is a solution if $\sum_ka_ky_k=t$ over the integers and $\sum_{k\in I_r}y_k=h_r$ for every stratum. The input word is $(Q,t,a_1,\dots,a_n,h_1,\dots,h_{13})$.
--   4. The output word is FAIL (the empty word) or $y_1,\dots,y_n$; a vector is **balanced** if $\sum_ix_i=n/2$.
--
--   **Formalization Note** Every number is one stored rational of the machine `TwMSOCount.Main`, so it is read in binary. A solution word has length $n\ge1$, so it is never the FAIL word.
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Theorem 1.1, p. 3; (4), p. 13; Problem 3.1, pp. 16–17; §7, p. 53

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_RandModSubsetSum_Strata

open scoped BigOperators

namespace RandModSubsetSum

/-- `δ₀ = δ* + η_res = 0.999996` ((4), p. 13; Theorem 1.1, p. 3).
Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), (4), p. 13. -/
noncomputable def delta0 : ℝ := 999996 / 10 ^ 6

/-- `β = max{B, 2}` (Theorem 1.1, p. 3). -/
noncomputable def beta (B : ℝ) : ℝ := max B 2

/-- `c_B = min{10⁻²⁴, (100β)⁻¹}` with `β = max{B, 2}` (Theorem 1.1, p. 3). -/
noncomputable def cB (B : ℝ) : ℝ := min (1 / 10 ^ 24) (1 / (100 * beta B))

/-- Input word of the modular problem `(Q, a, t)` (Theorem 1.1, p. 3; §7, p. 53): `Q`, then the
canonical representative of `t` in `{0, …, Q − 1}`, then those of `a_1, …, a_n`. Each number is
one stored rational of the machine, so it is read in binary. -/
def modInput {n Q : ℕ} (a : Fin n → Fin Q) (t : ℕ) : List ℚ :=
  [(Q : ℚ), (t : ℚ)] ++ List.ofFn (fun i => ((a i).val : ℚ))

/-- Input word of Problem 3.1 `(Q, a, t, h)` (p. 17): `Q`, the integer target `t`, the coefficients
`a_1, …, a_n ∈ {0, …, Q − 1}`, and the root counts `h_1, …, h_13`. -/
def intInput {n Q : ℕ} (a : Fin n → Fin Q) (t : ℕ) (h : Fin 13 → ℕ) : List ℚ :=
  [(Q : ℚ), (t : ℚ)] ++ List.ofFn (fun i => ((a i).val : ℚ)) ++ List.ofFn (fun r => ((h r : ℕ) : ℚ))

/-- Output word of a binary vector `y ∈ {0, 1}ⁿ`: `y_1, …, y_n`. FAIL is the empty word. -/
def encSol {n : ℕ} (y : Fin n → Fin 2) : List ℚ := List.ofFn (fun i => ((y i).val : ℚ))

/-- The modular target `t = a · x mod Q` (Theorem 1.1, p. 3), its canonical representative in
`{0, …, Q − 1}`. -/
def modTarget {n Q : ℕ} (a : Fin n → Fin Q) (x : Fin n → Fin 2) : ℕ :=
  (∑ i, (a i).val * (x i).val) % Q

/-- The integer target `t = a · x` of Problem 3.1 (p. 17). -/
def intTarget {n Q : ℕ} (a : Fin n → Fin Q) (x : Fin n → Fin 2) : ℕ := ∑ i, (a i).val * (x i).val

/-- `y` is a binary solution of `a · y ≡ t (mod Q)` (Theorem 1.1, p. 3). -/
def IsModSolution {n Q : ℕ} (a : Fin n → Fin Q) (t : ℕ) (y : Fin n → Fin 2) : Prop :=
  (∑ i, (a i).val * (y i).val) % Q = t % Q

/-- The output word is FAIL (the empty word) or the encoding of a binary solution of
`a · y ≡ t (mod Q)`. -/
def FailOrModSolution {n Q : ℕ} (a : Fin n → Fin Q) (t : ℕ) (o : List ℚ) : Prop :=
  o = [] ∨ ∃ y, IsModSolution a t y ∧ o = encSol y

/-- `y` solves Problem 3.1 (p. 17) for the weights `w`: `Σ_k a_k y_k = t` over the integers and
`Σ_{k ∈ I_r} y_k = h_r` for `r = 1, …, 13`. -/
def IsIntSolution (w : Fin 13 → ℝ) {n Q : ℕ} (a : Fin n → Fin Q) (t : ℕ) (h : Fin 13 → ℕ)
    (y : Fin n → Fin 2) : Prop :=
  (∑ i, (a i).val * (y i).val) = t ∧ ∀ r, rootCount w y r = h r

/-- The output word is FAIL or the encoding of a solution of Problem 3.1. -/
def FailOrIntSolution (w : Fin 13 → ℝ) {n Q : ℕ} (a : Fin n → Fin Q) (t : ℕ) (h : Fin 13 → ℕ)
    (o : List ℚ) : Prop :=
  o = [] ∨ ∃ y, IsIntSolution w a t h y ∧ o = encSol y

open Classical in
/-- `x ∈ {0, 1}ⁿ` has `Σ_i x_i = n/2` (Theorem 1.1, p. 3; used with `n` even). -/
def IsBalanced {n : ℕ} (x : Fin n → Fin 2) : Prop :=
  (Finset.univ.filter (fun i => x i = 1)).card = n / 2

/-- The modulus range `2^{δ₀ n} ≤ Q ≤ 2^{B n}` (Theorem 1.1, p. 3; (5), p. 18:
`δ₀ n ≤ log₂ Q ≤ B n`). -/
def InRange (B : ℝ) (n Q : ℕ) : Prop :=
  (2 : ℝ) ^ (delta0 * n) ≤ (Q : ℝ) ∧ (Q : ℝ) ≤ (2 : ℝ) ^ (B * n)

end RandModSubsetSum


