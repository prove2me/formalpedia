-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:09:07.506801+00:00
-- url     : https://prove2.me/theorems/a8d95920-e4ad-5a5a-9fae-fd2142e18577
-- title:
--   Algebra Map Zero Surjective
-- statement:
--   Definitions and structural lemmas for Algebra Map Zero Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AlgebraMapZeroSurjective.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHypA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
namespace GlobalTheory.ProjCone
variable {σ : Type} (I : Ideal (MvPolynomial σ ℂ)) [GradedAlgebra (quotGrading I)]
abbrev coord (c : σ) : MvPolynomial σ ℂ ⧸ I := Ideal.Quotient.mk I (X c)
omit [GradedAlgebra (quotGrading I)] in
theorem coord_mem (c : σ) : coord I c ∈ quotGrading I 1 :=
  ⟨X c, (mem_homogeneousSubmodule 1 _).mpr (isHomogeneous_X ℂ c), rfl⟩
omit [GradedAlgebra (quotGrading I)] in
theorem coord_mem_one_smul (c : σ) : coord I c ∈ quotGrading I (1 • 1) := by
  simpa using coord_mem I c
def awayRatio (c c' : σ) : HomogeneousLocalization.Away (quotGrading I) (coord I c) :=
  HomogeneousLocalization.Away.mk (quotGrading I) (coord_mem I c) 1 (coord I c') (coord_mem_one_smul I c')
def dehom (c : σ) : MvPolynomial σ ℂ →+* HomogeneousLocalization.Away (quotGrading I) (coord I c) :=
  eval₂Hom ((algebraMap (quotGrading I 0) _).comp (algebraMap ℂ (quotGrading I 0))) (awayRatio I c)
abbrev invCoord (c : σ) : Localization.Away (coord I c) := Localization.mk 1 ⟨coord I c, 1, pow_one _⟩
def toSpecC : Proj (quotGrading I) ⟶ Sp ℂ :=
  Proj.toSpecZero (quotGrading I) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (quotGrading I 0)))
abbrev chart (c : σ) : (Proj (quotGrading I)).Opens := Proj.basicOpen (quotGrading I) (coord I c)
def awayEquiv (c : σ) : HomogeneousLocalization.Away (quotGrading I) (coord I c) ≃+* Γ(Proj (quotGrading I), chart I c) :=
  (Proj.basicOpenIsoAway (quotGrading I) (coord I c) (coord_mem I c) one_pos).commRingCatIsoToRingEquiv
def ratio (c c' : σ) : Γ(Proj (quotGrading I), chart I c) := awayEquiv I c (awayRatio I c c')
end GlobalTheory.ProjCone
namespace GlobalTheory
open ProjCone
end GlobalTheory


