-- Prove2me | Definitions.Def_ZeroOneSCO_Columns
-- name    : ZeroOneSCO_Columns
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:51:27.375747+00:00
-- url     : https://prove2.me/theorems/8c5e83ed-1e90-457a-af4e-2b27845c4330
-- title:
--   Column quantities of a matrix: $\|Z\|_0^+$, $\Gamma_+,\Gamma_0,\Gamma_-$, $V_\Gamma$, $Z^{\downarrow}_r$, $\mathbb T(Z;s)$, $\mathcal S$ and $\Pi_{\mathcal S}$
-- statement:
--   This module fixes the combinatorics of the $0/1$ constraint on a matrix $Z\in\mathbb R^{M\times N}$.
--
--   The maximum entry of column $n$ is $Z^{\max}_{:n}:=\max_m Z_{mn}$. The columns split by its sign into
--   $$
--   \Gamma_+:=\{n: Z^{\max}_{:n}>0\},\qquad \Gamma_0:=\{n: Z^{\max}_{:n}=0\},\qquad \Gamma_-:=\{n: Z^{\max}_{:n}<0\},
--   $$
--   and for $\Gamma\subseteq\mathcal N$ one puts $V_\Gamma:=\{(m,n)\in\mathcal M\times\Gamma: Z_{mn}=0\}$. The measure
--   $$
--   \|Z\|_0^+:=\sum_{n=1}^N\ell_{0/1}(Z^{\max}_{:n})=|\Gamma_+|
--   $$
--   counts the columns with a positive entry, where $\ell_{0/1}(t)=1$ for $t>0$ and $0$ for $t\le0$. The constraint set is $\mathcal S:=\{Z:\|Z\|_0^+\le s\}$, and $\Pi_{\mathcal S}(Z)$ is the set of its points nearest to $Z$ in the Frobenius norm.
--
--   Writing $\|(Z_{:n})^+\|$ for the Euclidean norm of the positive part of column $n$, the value $Z^{\downarrow}_r$ is the $r$th largest of these $N$ numbers, and
--   $$
--   \mathbb T(Z;s):=\Bigl\{(\Gamma_+\setminus\Gamma_s)\cup\Gamma_0:\ \Gamma_s\subseteq\Gamma_+,\ |\Gamma_s|=\min\{s,|\Gamma_+|\},\ \min_{n\in\Gamma_s}\|(Z_{:n})^+\|\ge\max_{n\notin\Gamma_s}\|(Z_{:n})^+\|\Bigr\}.
--   $$
--   Finally $[(Z_{:T})^-\ Z_{:\overline T}]$ replaces each column in $T$ by its negative part and keeps the others.
--
--   These objects describe the projection onto $\mathcal S$ and drive the index-set selection of the Newton method.
--
--   **Formalization Note** `rthLargest` sorts the $N$ values with multiplicity and returns $0$ beyond position $N$. The condition with $\min\ge\max$ in $\mathbb T(Z;s)$ is written with two universal quantifiers, so an empty $\Gamma_s$ or an empty complement needs no special case. `[NeZero M]` gives the column maximum a nonempty index set. `projS` minimizes the squared Frobenius norm, which has the same minimizers. `plusZero` is $|\Gamma_+|$, and the lemma `plusZero_eq_sum` links it to the sum in (3).
-- source:
--   Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average Approximation for Chance Constrained Programming, arXiv:2210.11889v5, pp.2–7, (1), (3), (4), (6), (7), (8), (17), (20), (21)

import Mathlib

namespace ZeroOneSCO

/-- Matrices `ℝ^{M×N}` of Zhou, Pan, Xiu & Li, A 0/1 Constrained Optimization Solving Sample Average
Approximation for Chance Constrained Programming, arXiv:2210.11889v5, p.3. Rows are `Fin M`, columns
`Fin N`. -/
abbrev Mat (M N : ℕ) := Matrix (Fin M) (Fin N) ℝ

/-- The 0/1 loss `ℓ_{0/1}(t)`, equal to `1` for `t > 0` and `0` for `t ≤ 0`, arXiv:2210.11889v5,
(1), p.2. -/
noncomputable def loss01 (t : ℝ) : ℕ := if 0 < t then 1 else 0

/-- `Z^max_{:n} := max_m Z_mn`, the maximum entry of column `n`, arXiv:2210.11889v5, p.3.

**Formalization Note.** `[NeZero M]` makes the row index set nonempty, so the maximum exists. -/
noncomputable def colMax {M N : ℕ} [NeZero M] (Z : Mat M N) (n : Fin N) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun m => Z m n)

/-- `‖(Z_{:n})⁺‖`, the Euclidean norm of the positive part (6) of column `n`, arXiv:2210.11889v5,
pp.4–5. -/
noncomputable def colPosNorm {M N : ℕ} (Z : Mat M N) (n : Fin N) : ℝ :=
  Real.sqrt (∑ m, (max (Z m n) 0) ^ 2)

/-- `‖W_{:n}‖`, the Euclidean norm of column `n`, arXiv:2210.11889v5, p.5. -/
noncomputable def colNorm {M N : ℕ} (W : Mat M N) (n : Fin N) : ℝ :=
  Real.sqrt (∑ m, (W m n) ^ 2)

/-- `Γ₊(Z)`, the columns with positive maximum, arXiv:2210.11889v5, (7), p.5. -/
noncomputable def gammaPos {M N : ℕ} [NeZero M] (Z : Mat M N) : Finset (Fin N) :=
  Finset.univ.filter fun n => 0 < colMax Z n

/-- `Γ₀(Z)`, the columns with zero maximum, arXiv:2210.11889v5, (7), p.5. -/
noncomputable def gammaZero {M N : ℕ} [NeZero M] (Z : Mat M N) : Finset (Fin N) :=
  Finset.univ.filter fun n => colMax Z n = 0

/-- `Γ₋(Z)`, the columns with negative maximum, arXiv:2210.11889v5, (7), p.5. -/
noncomputable def gammaNeg {M N : ℕ} [NeZero M] (Z : Mat M N) : Finset (Fin N) :=
  Finset.univ.filter fun n => colMax Z n < 0

/-- `V_Γ(Z) := {(m,n) ∈ M × Γ : Z_mn = 0}`, arXiv:2210.11889v5, (7), p.5. -/
noncomputable def VGamma {M N : ℕ} (Γ : Finset (Fin N)) (Z : Mat M N) : Finset (Fin M × Fin N) :=
  Finset.univ.filter fun p => p.2 ∈ Γ ∧ Z p.1 p.2 = 0

/-- `‖Z‖₀⁺`, the number of columns of `Z` with positive maximum: (3), p.3, in the form (8), p.5, of
arXiv:2210.11889v5. -/
noncomputable def plusZero {M N : ℕ} [NeZero M] (Z : Mat M N) : ℕ := (gammaPos Z).card

/-- The defining sum (3), p.3, agrees with the form (8), p.5, used as the definition of `plusZero`. -/
theorem plusZero_eq_sum {M N : ℕ} [NeZero M] (Z : Mat M N) :
    plusZero Z = ∑ n, loss01 (colMax Z n) := by
  unfold plusZero gammaPos
  rw [Finset.card_filter]
  rfl

/-- The set `S := {Z : ‖Z‖₀⁺ ≤ s}`, arXiv:2210.11889v5, (4), p.4. -/
def S {M N : ℕ} [NeZero M] (s : ℕ) : Set (Mat M N) := {Z | plusZero Z ≤ s}

/-- The squared Frobenius norm `‖A‖² = ∑_mn A_mn²`, arXiv:2210.11889v5, p.5. -/
def frobSq {M N : ℕ} (A : Mat M N) : ℝ := ∑ m, ∑ n, (A m n) ^ 2

/-- The set-valued projection `Π_S(Z) = argmin_{Y ∈ S} ‖Z − Y‖`, arXiv:2210.11889v5, (20), p.7.

**Formalization Note.** `S` is not convex, so this is a set. The minimized quantity is the square of
the page's norm, which has the same minimizers. -/
def projS {M N : ℕ} [NeZero M] (s : ℕ) (Z : Mat M N) : Set (Mat M N) :=
  {Y | Y ∈ S s ∧ ∀ Y' ∈ S s, frobSq (Z - Y) ≤ frobSq (Z - Y')}

/-- `Z↓_r`, the `r`th largest element of `{‖(Z_{:1})⁺‖, …, ‖(Z_{:N})⁺‖}`, arXiv:2210.11889v5, p.5.

**Formalization Note.** The elements are taken with multiplicity (a multiset sorted in descending
order), `r` is 1-based, and the value is `0` when `r > N`. The paper uses `r = s ≥ 1`, and with the
default `0` display (9) also covers `s > N`. -/
noncomputable def rthLargest {M N : ℕ} (Z : Mat M N) (r : ℕ) : ℝ :=
  ((Finset.univ.val.map (colPosNorm Z)).sort (· ≥ ·)).getD (r - 1) 0

/-- `𝕋(Z; s)`, arXiv:2210.11889v5, (17), p.7: the sets `(Γ₊ \ Γs) ∪ Γ₀` with `Γs ⊆ Γ₊`,
`|Γs| = min{s, |Γ₊|}` and `min_{n ∈ Γs} ‖(Z_{:n})⁺‖ ≥ max_{n ∉ Γs} ‖(Z_{:n})⁺‖`.

**Formalization Note.** The `min ≥ max` of (17) is written with two universal quantifiers, so an
empty `Γs` or an empty complement needs no case. `n'` ranges over every column outside `Γs`, as on the
page. -/
noncomputable def TSet {M N : ℕ} [NeZero M] (Z : Mat M N) (s : ℕ) : Set (Finset (Fin N)) :=
  {T | ∃ Γs : Finset (Fin N), Γs ⊆ gammaPos Z ∧ Γs.card = min s (gammaPos Z).card ∧
    (∀ n ∈ Γs, ∀ n' ∉ Γs, colPosNorm Z n' ≤ colPosNorm Z n) ∧
    T = (gammaPos Z \ Γs) ∪ gammaZero Z}

/-- The matrix `[(Z_{:T})⁻ Z_{:T̄}]` of arXiv:2210.11889v5, (21), p.7: the negative part (6) on the
columns in `T` and `Z` itself on the others.

**Formalization Note.** Defined column by column, so no permutation of the columns is needed. -/
noncomputable def glue {M N : ℕ} (T : Finset (Fin N)) (Z : Mat M N) : Mat M N :=
  Matrix.of fun m n => if n ∈ T then min (Z m n) 0 else Z m n

end ZeroOneSCO


