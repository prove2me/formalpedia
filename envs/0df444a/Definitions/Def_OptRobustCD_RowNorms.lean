-- Prove2me | Definitions.Def_OptRobustCD_RowNorms
-- name    : OptRobustCD_RowNorms
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:49:59.225195+00:00
-- url     : https://prove2.me/theorems/f3976998-01e4-4bbf-b1c0-dbd8d84c1d8b
-- title:
--   Row-sum norms $\|E\|_{1,2}$, $\|E\|_{1,\infty}$, the Frobenius norm and the count $n_-(M)$ of negative eigenvalues
-- statement:
--   For $E\in\mathbb R^{n\times n}$ (Definition 5.7),
--   $$\|E\|_{1,2}=\Bigl(\sum_{i\in[n]}\Bigl(\sum_{j\in[n]}|E_{ij}|\Bigr)^2\Bigr)^{1/2},\qquad \|E\|_{1,\infty}=\max_{i\in[n]}\sum_{j\in[n]}|E_{ij}|.$$
--   $\|X\|_F^2=\sum_{ij}X_{ij}^2$, and $n_-(M)$ counts the strictly negative eigenvalues of $M$ with multiplicity (Lemma 6.1).
--
--   **Formalization Note** $n_-(M)$ counts the negative real roots of the characteristic polynomial with multiplicity; for a real symmetric matrix this is the number of negative eigenvalues. It is applied only to symmetric matrices.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Definition 5.7 p.26 (pdf p.28); Lemma 6.1 p.28 (pdf p.30)

import Mathlib

namespace OptRobustCD

/-!
# Row-sum norms, the Frobenius norm, and the number of negative eigenvalues

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…).
* Definition 5.7 (p.26, pdf p.28): "`∥E∥_{1,2} = (Σ_{i∈[n]} (Σ_{j∈[n]} |E_ij|)²)^{1/2}` and
  `∥E∥_{1,∞} = max_{i∈[n]} Σ_{j∈[n]} |E_ij|`."
* Lemma 6.1 (p.28, pdf p.30): "`n_−(H)` counts the number of strictly negative eigenvalues of `H`."

**Formalization Note.**
* `norm1inf` is the real supremum over the finite index set (`0` for the empty matrix).
* `negCount M` counts the strictly negative real roots of the characteristic polynomial of `M`
  with multiplicity. For a real symmetric matrix the characteristic polynomial splits over `ℝ`,
  so this is the number of negative eigenvalues with multiplicity. Every matrix to which the
  mission applies it is symmetric.
* `frob2 X = Σ_{ij} X_ij²` is the squared Frobenius norm `∥X∥_F²`.
-/

/-- `∥E∥_{1,2} = (Σ_i (Σ_j |E_ij|)²)^{1/2}`. -/
noncomputable def norm12 {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, (∑ j, |E i j|) ^ 2)

/-- `∥E∥_{1,∞} = max_i Σ_j |E_ij|`. -/
noncomputable def norm1inf {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ⨆ i, ∑ j, |E i j|

/-- `∥X∥_F² = Σ_{ij} X_ij²`. -/
def frob2 {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, X i j ^ 2

/-- The multiset of negative real roots of the characteristic polynomial of `M`, with
multiplicity (the negative eigenvalues of a symmetric `M`). -/
noncomputable def negEigs {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Multiset ℝ :=
  M.charpoly.roots.filter (· < 0)

/-- `n_−(M)`, the number of strictly negative eigenvalues with multiplicity. -/
noncomputable def negCount {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℕ :=
  Multiset.card (negEigs M)

end OptRobustCD


