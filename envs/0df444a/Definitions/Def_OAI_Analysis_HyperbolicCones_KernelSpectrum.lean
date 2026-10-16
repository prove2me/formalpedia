-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
-- name    : OAI_Analysis_HyperbolicCones_KernelSpectrum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:33:05.228563+00:00
-- url     : https://prove2.me/theorems/a24bb47d-6bf0-406b-9c98-49693aab1077
-- title:
--   Spectral identities for the inverse square root of a symmetric matrix
-- statement:
--   Let $\mathrm{Sym}_n$ be the space of real symmetric $n\times n$ matrices, and write $H\succ0$ when $H$ is positive definite. Every $H\in\mathrm{Sym}_n$ has a spectral decomposition $H=U\operatorname{diag}(\lambda_1,\dots,\lambda_n)\,U^{\mathsf T}$ with $U$ orthogonal. For a function $f:\mathbb{R}\to\mathbb{R}$, the matrix $f(H)=U\operatorname{diag}\bigl(f(\lambda_1),\dots,f(\lambda_n)\bigr)U^{\mathsf T}$ is given by the functional calculus. The inverse square root of $H$ is $H^{-1/2}=U\operatorname{diag}(\mu_1,\dots,\mu_n)\,U^{\mathsf T}$, where $\mu_i=\lambda_i^{-1/2}$ if $\lambda_i>0$ and $\mu_i=0$ if $\lambda_i\le0$.
--
--   The file proves the following facts, for every $n$ and every $H\in\mathrm{Sym}_n$.
--
--   1. **Functional-calculus form.** $H^{-1/2}=g(H)$, where $g(x)=1/\sqrt{x}$ for $x>0$ and $g(x)=0$ for $x\le0$.
--   2. **Multiplicativity.** For all functions $f_1,f_2:\mathbb{R}\to\mathbb{R}$, $(f_1f_2)(H)=f_1(H)\,f_2(H)$, where $(f_1f_2)(x)=f_1(x)f_2(x)$.
--   3. **Symmetry.** $H^{-1/2}$ is symmetric, that is, $(H^{-1/2})^{\mathsf T}=H^{-1/2}$.
--   4. **Positive spectrum.** If $A$ is a positive definite real $n\times n$ matrix and $\lambda\in\mathbb{R}$ is such that $A-\lambda I$ is not invertible, then $\lambda>0$.
--   5. **Normalization.** If $H\succ0$, then
--   $$
--   (H^{-1/2})^{\mathsf T}\,H\,H^{-1/2}=I_n .
--   $$
--   6. **Invertibility.** If $H\succ0$, then $H^{-1/2}$ is invertible.
--
--   Items 5 and 6 say that congruence by $H^{-1/2}$ is an invertible change of coordinates that turns a positive definite $H$ into the identity. This is how a positive linear map $D$ with $D(I)\succ0$ is replaced by the unital map $X\mapsto D(I)^{-1/2}D(X)D(I)^{-1/2}$ without changing the set on which a block matrix pencil is positive semidefinite.
--
--   **Formalization Note** The functional calculus is Mathlib's continuous functional calculus `cfc`. On a symmetric matrix every function is continuous on the finite spectrum, so `cfc f H` is given by the eigenvalue formula above. The convention for $\lambda_i\le0$ comes from `Real.sqrt` vanishing on negative numbers and from the inverse of $0$ being $0$. Item 4 is phrased with `spectrum ℝ A`, and item 2 is `matrix_cfc_mul`. Since the entries are real, the conjugate transpose is the transpose.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/KernelSpectrum.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/KernelSpectrum.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks

namespace OAI

/-! Spectral identities for the inverse square root. -/

noncomputable section

open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix

namespace Paper256

theorem inverseSquareRoot_eq_cfc {n : ℕ} (H : Sym n) :
    inverseSquareRoot H = cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (H : Mat n ℝ) := by
  let hH : (H : Mat n ℝ).IsHermitian := H.property
  rw [hH.cfc_eq]
  simp [inverseSquareRoot, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Function.comp_def, Matrix.star_eq_conjTranspose]

theorem matrix_cfc_mul {n : ℕ} (H : Sym n) (f g : ℝ → ℝ) :
    cfc (fun x => f x * g x) (H : Mat n ℝ) =
      cfc f (H : Mat n ℝ) * cfc g (H : Mat n ℝ) :=
  cfc_mul f g _ (H.val.finite_real_spectrum.continuousOn f)
    (H.val.finite_real_spectrum.continuousOn g)

theorem inverseSquareRoot_isHermitian {n : ℕ} (H : Sym n) :
    (inverseSquareRoot H).IsHermitian := by
  rw [inverseSquareRoot_eq_cfc]
  exact IsSelfAdjoint.cfc

theorem inverseSquareRoot_transpose {n : ℕ} (H : Sym n) :
    (inverseSquareRoot H)ᵀ = inverseSquareRoot H :=
  Matrix.isHermitian_iff_isSymm.mp (inverseSquareRoot_isHermitian H)

theorem posDef_real_spectrum_positive {n : ℕ} {A : Mat n ℝ} (hA : A.PosDef)
    {x : ℝ} (hx : x ∈ spectrum ℝ A) : 0 < x := by
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hA.eigenvalues_pos i

theorem inverseSquareRoot_conjugate {n : ℕ} (H : Sym n) (hH : (H : Mat n ℝ).PosDef) :
    (inverseSquareRoot H)ᵀ * (H : Mat n ℝ) * inverseSquareRoot H = 1 := by
  rw [inverseSquareRoot_transpose, inverseSquareRoot_eq_cfc]
  let f : ℝ → ℝ := fun x => (Real.sqrt x)⁻¹
  have hid : cfc (fun x : ℝ => x) (H : Mat n ℝ) = (H : Mat n ℝ) :=
    cfc_id' ℝ (H : Mat n ℝ) H.property
  change cfc f (H : Mat n ℝ) * (H : Mat n ℝ) * cfc f (H : Mat n ℝ) = 1
  calc
    cfc f (H : Mat n ℝ) * (H : Mat n ℝ) * cfc f (H : Mat n ℝ) =
        cfc (fun x => f x * x * f x) (H : Mat n ℝ) := by
      rw [matrix_cfc_mul H (fun x => f x * x) f,
        matrix_cfc_mul H f (fun x => x)]
      rw [hid]
    _ = cfc (fun _ : ℝ => 1) (H : Mat n ℝ) := by
      apply cfc_congr
      intro x hx
      have hxpos := posDef_real_spectrum_positive hH hx
      have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hxpos).ne'
      dsimp [f]
      field_simp
      exact (Real.sq_sqrt hxpos.le).symm
    _ = 1 := cfc_const_one ℝ (H : Mat n ℝ) H.property

theorem inverseSquareRoot_isUnit {n : ℕ} (H : Sym n) (hH : (H : Mat n ℝ).PosDef) :
    IsUnit (inverseSquareRoot H) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hs
  have h := congrArg Matrix.det (inverseSquareRoot_conjugate H hH)
  simp [Matrix.det_mul, Matrix.det_transpose, hs] at h

end Paper256

end

end OAI


