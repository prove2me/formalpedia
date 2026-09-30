-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_ElementaryLoci
-- name    : WeierstrassEllipticZeta_ElementaryLoci
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-21T15:44:57.637872+00:00
-- url     : https://prove2.me/theorems/949373ad-8ff4-4c91-bf3e-3cee04cd9879
-- title:
--   Elementary affine loci and explicit period kernels
-- statement:
--   Elementary affine loci in a fixed elliptic fibre have three shapes. In covering
--   coordinates (t,z,u), their direction spaces are {0}, {(s,0,αs):s∈ℂ}, and
--   {(s,0,b):s,b∈ℂ}. The locus with anchor r is the affine translate r+V.
--   The additive degree is m in the point case and zero in the other cases.
--
--   For an integer submodule Λ⊆ℂ and an integer-linear map η:Λ→ℂ, the explicit
--   period kernels are {0}, {ω∈Λ:η(ω)=αω}, and Λ, respectively. These are submodules
--   of ℂ over ℤ. The definition of the line kernel is the image under Λ↪ℂ of
--   ker(η−α·inclusion). This sign matches the mission's period graph (ω,−η(ω)).
--
--   These definitions describe linear translation directions and the explicit period
--   quotient used by the mission. They do not identify an arbitrary analytic subgroup
--   with an algebraic subgroup and contain no multiplicity estimate.
-- source:
--   Elementary affine locus normalization and exact period kernels in the mission's existing covering coordinates. This is a derived supporting result for the stabilizer/coset framework of Philippon (1986), section 5, https://www.numdam.org/item/10.24033/bsmf.2060.pdf. It does not formalize the global multiplicity theorem or assert an algebraic-subgroup identification. Under the established additive/elliptic projection alternative, replace a nonempty locus by a point, a line of slope alpha in a fixed elliptic fibre, or the full fibre. The exact curve kernels are zero, the periods satisfying eta(omega)=alpha*omega, and the entire period lattice. Both the finite coset count and additive degree factor are preserved. The complete geometry proof has no platform theorem dependencies; the converse uses the already-Proved projective locus stabilizer construction. The frontier equivalence keeps C, the chart point and the local cost unchanged. The uniform cost bound and selection of its elementary witness remain open.

import Definitions.Def_TranscendenceTheory_LinearTranslationStabilizer

noncomputable section
namespace WeierstrassEllipticZeta

/-- Three affine loci in a fixed elliptic fibre, with line slope in the vertical coordinate. -/
inductive ElementaryLocusShape
  | point
  | line (slope : ℂ)
  | fibre

/-- The complex vector space underlying an elementary locus. -/
def elementaryDirections : ElementaryLocusShape → Submodule ℂ (Fin 3 → ℂ)
  | .point => ⊥
  | .line α => LinearMap.ker (LinearMap.proj 1) ⊓
      LinearMap.ker (LinearMap.proj 2 - α • LinearMap.proj 0)
  | .fibre => LinearMap.ker (LinearMap.proj 1)

/-- An affine translate of one of the three elementary vector spaces. -/
def elementaryLocus (shape : ElementaryLocusShape) (r : Fin 3 → ℂ) :
    Set (Fin 3 → ℂ) :=
  (fun v => r + v) '' (elementaryDirections shape : Set (Fin 3 → ℂ))

/-- The additive degree retained by the cost estimate for an elementary locus. -/
def elementaryDegree : ElementaryLocusShape → ℕ → ℕ
  | .point, m => m
  | .line _, _ => 0
  | .fibre, _ => 0

/-- Periods whose quasiperiod agrees with the slope of an elementary line. -/
def resonantPeriods (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (α : ℂ) :
    Submodule ℤ ℂ :=
  (LinearMap.ker (η - α • Λ.subtype)).map Λ.subtype

/-- The exact kernel of the one-parameter curve modulo an elementary stabilizer. -/
def elementaryPeriodKernel (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) :
    ElementaryLocusShape → Submodule ℤ ℂ
  | .point => ⊥
  | .line α => resonantPeriods Λ η α
  | .fibre => Λ

end WeierstrassEllipticZeta


