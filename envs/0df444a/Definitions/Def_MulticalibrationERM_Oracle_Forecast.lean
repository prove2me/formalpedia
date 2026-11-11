-- Prove2me | Definitions.Def_MulticalibrationERM_Oracle_Forecast
-- name    : MulticalibrationERM_Oracle_Forecast
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:49:27.192213+00:00
-- url     : https://prove2.me/theorems/4c715ce3-a84b-40b8-822d-c40f3fddf278
-- title:
--   Definition 3.1, §3.1 — distortion, Sylvester–Hadamard and cube tests, adjacent support, the (restricted) minimax forecast
-- statement:
--   A finite family $S$ of tests $\sigma\in[-1,1]^\Lambda$, kept as a list with repetitions, has **distortion** $\kappa\ge1$ (`HasDistortion S κ`) if it is nonempty and
--   $$\|b\|_1\le\kappa\max_{\sigma\in S}\langle\sigma,b\rangle\qquad\text{for every }b\in\mathbb R^\Lambda .$$
--   The **Sylvester matrix** is $W_1=(1)$, $W_{2k}=\begin{pmatrix}W_k&W_k\\W_k&-W_k\end{pmatrix}$. For $\nu=2^{\lceil\log_2 m\rceil}$ let $M$ be the first $m$ columns of $W_\nu$; the **Hadamard tests** $S_{\mathrm{Had}}$ are the $\nu$ rows of $M$ followed by their negations ($|S_{\mathrm{Had}}|=2\nu$). The **cube** $S_{\mathrm{cube}}=\{-1,+1\}^\Lambda$ lists all $2^m$ sign patterns.
--
--   A distribution $P$ on the grid (`IsDist`) has **adjacent support** if it is supported on one grid value or on two grid values at distance $1/K$; its mean is $\mu=\sum_v P(v)\,v$.
--
--   The **minimax forecast** on the consecutive grid values $\Lambda'=\Lambda\cap[lo/K,hi/K]$ (`minimax K lo hi a`; $lo=0,hi=K$ is $\mathrm{Minimax}(a)$ of Lemma 3.4, general $lo\le hi$ is $\mathrm{Minimax}_{\Lambda'}$ of Lemma 6.7): if $a_{lo}\ge0$, the point mass at $lo/K$; otherwise, if $a_{hi}\le0$, the point mass at $hi/K$; otherwise, with $j$ the first index in $[lo,hi)$ with $a_j\le0<a_{j+1}$, mass $\lambda$ on $j/K$ and $1-\lambda$ on $(j+1)/K$ where $\lambda a_j+(1-\lambda)a_{j+1}=0$. `minimaxOps` counts the elementary operations of this procedure in a unit-cost model (the sign tests, the scan, the computation of $\lambda$, one write per output coordinate).
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), pp. 12, 16–17, 35, Definition 3.1, Lemmas 3.4, 6.7

import Mathlib
import Definitions.Def_MulticalibrationERM_Oracle_Setting

namespace MulticalibrationERM.Oracle

/-! # Signed tests, their distortion, and the minimax forecast

Okoroafor, *The Sample Complexity of Multicalibration with an ERM Oracle* (supplied preprint,
SHA256 654c7a81…), Section 3.1, pp. 16–18 (Definition 3.1, the Hadamard and cube families,
Lemma 3.4's forecast) and Section 6.3, p. 35 (the forecast restricted to consecutive grid
values, Lemma 6.7).

A test is a vector `σ : Fin m → ℝ` indexed by the grid; a family of tests is a `List`, so that
repetitions are kept. Grid indices are natural numbers `0, …, K` (value `j / K`). -/

/-- Definition 3.1: a finite family `S ⊆ [−1, 1]^Λ` (a nonempty list) has **distortion** `κ ≥ 1`
if `‖b‖₁ ≤ κ max_{σ ∈ S} ⟨σ, b⟩` for every `b ∈ ℝ^Λ`; the maximum over the finite nonempty
family is written as "some `σ ∈ S` attains the bound". -/
def HasDistortion {m : ℕ} (S : List (Fin m → ℝ)) (κ : ℝ) : Prop :=
  1 ≤ κ ∧ S ≠ [] ∧ (∀ σ ∈ S, ∀ v, |σ v| ≤ 1) ∧
    ∀ b : Fin m → ℝ, ∃ σ ∈ S, ∑ v, |b v| ≤ κ * ∑ v, σ v * b v

/-- The Sylvester Hadamard matrix `W_{2^k}` (p. 16): `W_1 = (1)` and
`W_{2n} = [[W_n, W_n], [W_n, −W_n]]`, as a function of row and column indices `< 2^k`
(rows/columns `≥ 2^k` are not used). -/
def sylvester : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 1
  | k + 1, i, j =>
      (if 2 ^ k ≤ i ∧ 2 ^ k ≤ j then -1 else 1) * sylvester k (i % 2 ^ k) (j % 2 ^ k)

/-- `ν = 2^{⌈log₂ m⌉}`, so `m ≤ ν < 2m` (for `m ≥ 1`). -/
def hadNu (m : ℕ) : ℕ := 2 ^ Nat.clog 2 m

/-- The Hadamard tests `S_Had` (p. 16): with `M ∈ {−1, +1}^{ν × m}` the first `m` columns of
`W_ν`, the list (with repetitions) of the `ν` rows of `M` followed by their negations, so
`|S_Had| = 2ν`. -/
def hadamardTests (m : ℕ) : List (Fin m → ℝ) :=
  (List.range (hadNu m)).map (fun i => fun v : Fin m => sylvester (Nat.clog 2 m) i v) ++
    (List.range (hadNu m)).map (fun i => fun v : Fin m => -sylvester (Nat.clog 2 m) i v)

/-- The cube `S_cube = {−1, +1}^Λ` of all `2^m` sign patterns (p. 16). -/
noncomputable def cubeTests (m : ℕ) : List (Fin m → ℝ) :=
  (Finset.univ : Finset (Fin m → Bool)).toList.map (fun s => fun v => pm (s v))

/-- `P ∈ Δ(Λ)`: a probability vector on the grid. -/
def IsDist {K : ℕ} (P : Fin (K + 1) → ℝ) : Prop := (∀ j, 0 ≤ P j) ∧ ∑ j, P j = 1

/-- Adjacent support (p. 12): `P` is supported on one grid value or on two grid values at
distance `1/K`. -/
def AdjSupport {K : ℕ} (P : Fin (K + 1) → ℝ) : Prop :=
  ∃ i : ℕ, ∀ j : Fin (K + 1), P j ≠ 0 → (j : ℕ) = i ∨ (j : ℕ) = i + 1

/-- The mean `µ = ∑_v P(v) v` of a distribution on the grid. -/
noncomputable def gridMean {K : ℕ} (P : Fin (K + 1) → ℝ) : ℝ := ∑ j, P j * gv K j

/-- A coefficient vector read at a natural-number grid index (`0` outside the grid). -/
def coef {K : ℕ} (a : Fin (K + 1) → ℝ) (j : ℕ) : ℝ := if h : j < K + 1 then a ⟨j, h⟩ else 0

open Classical in
/-- The scan of the minimax forecast: the offset (from `lo`) of the first adjacent pair
`j, j + 1` in `[lo, hi]` with `a_j ≤ 0 < a_{j+1}`. -/
noncomputable def crossOffset (K lo hi : ℕ) (a : Fin (K + 1) → ℝ) : ℕ :=
  (List.range (hi - lo)).findIdx
    (fun j => decide (coef a (lo + j) ≤ 0 ∧ 0 < coef a (lo + j + 1)))

/-- The **minimax forecast** on the consecutive grid values `Λ' = Λ ∩ [lo/K, hi/K]`
(Lemma 3.4 for `lo = 0`, `hi = K`; Lemma 6.7 in general), as a probability vector on the grid:
if `a_lo ≥ 0`, the point mass at `lo`; otherwise, if `a_hi ≤ 0`, the point mass at `hi`;
otherwise, with `j` the first index in `[lo, hi)` with `a_j ≤ 0 < a_{j+1}`, mass `λ` on `j` and
`1 − λ` on `j + 1`, where `λ a_j + (1 − λ) a_{j+1} = 0`, i.e. `λ = a_{j+1} / (a_{j+1} − a_j)`. -/
noncomputable def minimax (K lo hi : ℕ) (a : Fin (K + 1) → ℝ) : Fin (K + 1) → ℝ :=
  fun j =>
    if 0 ≤ coef a lo then (if (j : ℕ) = lo then 1 else 0)
    else if coef a hi ≤ 0 then (if (j : ℕ) = hi then 1 else 0)
    else
      let c := lo + crossOffset K lo hi a
      let lam := coef a (c + 1) / (coef a (c + 1) - coef a c)
      if (j : ℕ) = c then lam else if (j : ℕ) = c + 1 then 1 - lam else 0

/-- The number of elementary operations used to compute `minimax K lo hi a` by the procedure
above, in a unit-cost model: two sign tests, the scan up to the first crossing (one test per
grid value examined), a constant for `λ`, and one write per grid value of the output vector. -/
noncomputable def minimaxOps (K lo hi : ℕ) (a : Fin (K + 1) → ℝ) : ℕ :=
  (K + 1) +
    (if 0 ≤ coef a lo then 1
     else if coef a hi ≤ 0 then 2
     else 2 + min (crossOffset K lo hi a + 1) (hi - lo) + 3)

end MulticalibrationERM.Oracle


