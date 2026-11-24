-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraStandardSmooth
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraStandardSmooth
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T12:30:18.566948+00:00
-- url     : https://prove2.me/theorems/6304cff9-d106-4854-b6d2-37ac7c59e84b
-- title:
--   Graph Algebra Standard Smooth
-- statement:
--   Definitions and structural lemmas for Graph Algebra Standard Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphAlgebraStandardSmooth.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebra
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphPreSubmersivePresentation_jacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
namespace FunctorialResolution.EmbeddedResolution
variable {R : Type u} [CommRing R] {σ τ : Type u}
noncomputable section
abbrev graphJacobianMinorDet [Fintype τ] [DecidableEq τ] (f : τ → MvPolynomial σ R) (v : τ → σ) :
    GraphAlgebra f :=
  graphAlgebraEquiv f (graphJacobianMinorMatrix f v).det
abbrev GraphAlgebraAway [Fintype τ] [DecidableEq τ] (f : τ → MvPolynomial σ R) (v : τ → σ) : Type u :=
  Localization.Away (graphJacobianMinorDet f v)
theorem isUnit_algebraMap_graphJacobianMinorDet [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    IsUnit (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v) (graphJacobianMinorDet f v)) :=
  IsLocalization.map_units (M := Submonoid.powers (graphJacobianMinorDet f v)) (GraphAlgebraAway f v)
    ⟨graphJacobianMinorDet f v, Submonoid.mem_powers _⟩
theorem isUnit_algebraMap_jacobian_graphPreSubmersive [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    IsUnit (algebraMap (GraphAlgebra f) (GraphAlgebraAway f v)
      (graphPreSubmersivePresentation f v hv).jacobian) := by
  rw [graphPreSubmersivePresentation_jacobian, map_mul, map_pow, map_neg, map_one]
  exact ((isUnit_one.neg).pow _).mul (isUnit_algebraMap_graphJacobianMinorDet f v)
def graphAlgebraAwayLocalizationPresentation [Fintype τ] [DecidableEq τ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) :
    Algebra.SubmersivePresentation (GraphAlgebra f) (GraphAlgebraAway f v) Unit Unit :=
  Algebra.SubmersivePresentation.localizationAway (S := GraphAlgebraAway f v) (r := graphJacobianMinorDet f v)
def graphAlgebraAwayPreSubmersivePresentation [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.PreSubmersivePresentation (MvPolynomial τ R) (GraphAlgebraAway f v) (Unit ⊕ σ) (Unit ⊕ τ) :=
  Algebra.PreSubmersivePresentation.comp (graphAlgebraAwayLocalizationPresentation f v).toPreSubmersivePresentation
    (graphPreSubmersivePresentation f v hv)
theorem isUnit_jacobian_presentation_graphAlgebraAway [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    IsUnit (graphAlgebraAwayPreSubmersivePresentation f v hv).jacobian := by
  rw [graphAlgebraAwayPreSubmersivePresentation,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.smul_def]
  exact (isUnit_algebraMap_jacobian_graphPreSubmersive f v hv).mul (graphAlgebraAwayLocalizationPresentation f v).jacobian_isUnit
def graphAlgebraAwaySubmersivePresentation [Fintype τ] [DecidableEq τ] [Fintype σ]
    (f : τ → MvPolynomial σ R) (v : τ → σ) (hv : Function.Injective v) :
    Algebra.SubmersivePresentation (MvPolynomial τ R) (GraphAlgebraAway f v)
      (Unit ⊕ Fin (Fintype.card σ)) (Unit ⊕ Fin (Fintype.card τ)) :=
  Algebra.SubmersivePresentation.reindex
    { toPreSubmersivePresentation := graphAlgebraAwayPreSubmersivePresentation f v hv
      jacobian_isUnit := isUnit_jacobian_presentation_graphAlgebraAway f v hv }
    (Equiv.sumCongr (Equiv.refl Unit) (Fintype.equivFin σ).symm)
    (Equiv.sumCongr (Equiv.refl Unit) (Fintype.equivFin τ).symm)
end
end FunctorialResolution.EmbeddedResolution


