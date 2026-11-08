-- Prove2me | Definitions.Def_RandMatDisc_goe
-- name    : RandMatDisc_goe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:39:48.490718+00:00
-- url     : https://prove2.me/theorems/4d68668b-dcc2-49d7-912d-cbf5ed60d550
-- title:
--   The normalized GOE law, $\mathrm{svec}$ and $\mathrm{mat}$
-- statement:
--   Let $d\ge1$. A random $d\times d$ matrix $A$ has the **normalized Gaussian Orthogonal Ensemble** law $\mathrm{GOE}(d)$ when $A$ is symmetric and its upper-triangular entries are independent centred Gaussians with
--
--   $$A_{k\ell}=A_{\ell k}\sim\mathcal N(0,1/d)\quad(1\le k<\ell\le d),\qquad A_{kk}\sim\mathcal N(0,2/d)\quad(1\le k\le d).$$
--
--   Write $D=d(d+1)/2$, the dimension of the space $\mathrm{Sym}_d$ of real symmetric $d\times d$ matrices. The **vectorization** $\mathrm{svec}:\mathrm{Sym}_d\to\mathbb R^D$ is
--
--   $$\mathrm{svec}(M)=\big((M_{aa})_{a=1}^d,\ (\sqrt2\,M_{ab})_{1\le a<b\le d}\big),$$
--
--   and $\mathrm{mat}=\mathrm{svec}^{-1}$ rebuilds the symmetric matrix: diagonal entries are read off directly and the off-diagonal entries $(a,b)$, $(b,a)$ are the corresponding coordinate divided by $\sqrt2$. The factor $\sqrt2$ makes $\mathrm{svec}$ an isometry from the Frobenius norm to the Euclidean norm, and $\sqrt{d/2}\,\mathrm{svec}(A)$ is a standard Gaussian vector in $\mathbb R^D$ when $A\sim\mathrm{GOE}(d)$.
--
--   These are the input model of the random matrix discrepancy problem and the change of variables that turns it into a problem about Gaussian vectors.
--
--   **Formalization Note** The coordinates of $\mathbb R^D$ are indexed by the pairs $(a,b)$ with $a\le b$ (type `SymIdx d`), not listed in the paper's order. The law is a measure on arrays `Fin d → Fin d → ℝ`, the underlying type of a matrix, read as a matrix through `Matrix.of`; it is the pushforward of the product of the Gaussian upper-triangular entries under symmetrization.
-- source:
--   Kızıldağ, Li, Stable and Online Algorithms for Random Matrix Discrepancy, arXiv:2610.01591 (held file sha256 889af7fc…), §1, p.3 (PDF p.5), GOE model (a), (b); §2.1, p.7 (PDF p.9), eq. (3)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace RandMatDisc

/-- The index set `{(a, b) : 1 ≤ a ≤ b ≤ d}` of the upper triangle of a `d × d` matrix, diagonal
included. Its cardinality is `D = d(d+1)/2`, the dimension of `Sym_d` (Kızıldağ, Li, *Stable and
Online Algorithms for Random Matrix Discrepancy*, arXiv:2610.01591, held file sha256 889af7fc…,
§2.1, p.7). The vector `svec M` is indexed by this type. -/
abbrev SymIdx (d : ℕ) : Type := {p : Fin d × Fin d // p.1 ≤ p.2}

/-- The vectorization `svec : Sym_d → ℝ^D`, eq. (3), p.7 (arXiv:2610.01591, sha256 889af7fc…):
`svec(M) = ((M_aa)_{a=1}^d, (√2 M_ab)_{1 ≤ a < b ≤ d})`. The coordinate of the pair `(a, a)` is
`M_aa` and the coordinate of `(a, b)` with `a < b` is `√2 M_ab`.

**Formalization Note.** The coordinates are indexed by `SymIdx d` rather than listed in the
paper's order (diagonal first, then the strict upper triangle); the order of the coordinates plays
no role. `svec` is defined on every matrix; on symmetric matrices it is the paper's map. -/
noncomputable def svec {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : EuclideanSpace ℝ (SymIdx d) :=
  WithLp.toLp 2 fun p => if p.1.1 = p.1.2 then M p.1.1 p.1.1 else Real.sqrt 2 * M p.1.1 p.1.2

/-- The inverse vectorization `mat = svec⁻¹`, p.7 (arXiv:2610.01591, sha256 889af7fc…): the
symmetric matrix whose diagonal entry `(a, a)` is the coordinate `(a, a)` and whose entries
`(a, b)`, `(b, a)` for `a < b` are the coordinate `(a, b)` divided by `√2`. -/
noncomputable def mat {d : ℕ} (v : EuclideanSpace ℝ (SymIdx d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b =>
    if h : a = b then v ⟨(a, b), h.le⟩
    else if h' : a ≤ b then v ⟨(a, b), h'⟩ / Real.sqrt 2
    else v ⟨(b, a), (not_le.mp h').le⟩ / Real.sqrt 2

/-- The symmetric array built from upper-triangular entries: entry `(k, ℓ)` is `x (k, ℓ)` when
`k ≤ ℓ` and `x (ℓ, k)` otherwise. -/
def symOfUpper {d : ℕ} (x : SymIdx d → ℝ) : Fin d → Fin d → ℝ :=
  fun k l => if h : k ≤ l then x ⟨(k, l), h⟩ else x ⟨(l, k), (not_le.mp h).le⟩

/-- The variance of the entry `(k, ℓ)`, `k ≤ ℓ`, of a normalized GOE matrix, p.3: `2/d` on the
diagonal and `1/d` off it. -/
noncomputable def goeVar (d : ℕ) (p : SymIdx d) : NNReal :=
  if p.1.1 = p.1.2 then 2 / (d : NNReal) else 1 / (d : NNReal)

/-- The **normalized Gaussian Orthogonal Ensemble** `GOE(d)`, p.3 (PDF p.5) of Kızıldağ, Li,
arXiv:2610.01591 (held file sha256 889af7fc…): "for each i, Aᵢ has independent normal upper
triangular entries: (a) (Aᵢ)_{kℓ} = (Aᵢ)_{ℓk} ∼ N(0, 1/d) for 1 ≤ k < ℓ ≤ d, and (b)
(Aᵢ)_{kk} ∼ N(0, 2/d) for 1 ≤ k ≤ d."

It is the law of the symmetric array `symOfUpper x` when the upper-triangular entries
`x (k, ℓ)`, `k ≤ ℓ`, are independent centred Gaussians of variance `goeVar d (k, ℓ)`.

**Formalization Note.** The law lives on `Fin d → Fin d → ℝ` (the underlying type of
`Matrix (Fin d) (Fin d) ℝ`, which carries no measurable structure of its own); a sample `A` is
read as the matrix `Matrix.of A`. At `d = 0` the type is a single point. -/
noncomputable def goe (d : ℕ) : Measure (Fin d → Fin d → ℝ) :=
  (Measure.pi fun p : SymIdx d => gaussianReal 0 (goeVar d p)).map symOfUpper

theorem measurable_symOfUpper (d : ℕ) : Measurable (symOfUpper (d := d)) := by
  unfold symOfUpper
  refine measurable_pi_lambda _ fun k => measurable_pi_lambda _ fun l => ?_
  by_cases h : k ≤ l
  · simp only [h, dite_true]; exact measurable_pi_apply _
  · simp only [h, dite_false]; exact measurable_pi_apply _

instance (d : ℕ) : IsProbabilityMeasure (goe d) :=
  Measure.isProbabilityMeasure_map (measurable_symOfUpper d).aemeasurable

end RandMatDisc


