-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:12.160173+00:00
-- url     : https://prove2.me/theorems/78634577-71f6-4bfd-bbc9-10c0b52e2e0e
-- title:
--   Subsingleton Prime Spectrum
-- statement:
--   Definitions and structural lemmas for Subsingleton Prime Spectrum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/SubsingletonPrimeSpectrum.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (sp IsTan fstD scaleD prodPts isTan_iff isLieComb_iff comp_one' isTan_mul isTan_one
  isTan_scale)
open GlobalTheory.SqZero
open TrivSqZeroExt (inl inr)
namespace GlobalTheory.UnifDifferential
attribute [local instance] Over.cartesianMonoidalCategory
section Pull
variable {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
  {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
def pullFn (y : sp (R₀ := R) S ⟶ A) (U : A.left.Opens) (h : ⊤ ≤ y.left ⁻¹ᵁ U) (f : Γ(A.left, U)) : S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ((y.left.appLE U ⊤ h).hom f)
end Pull
variable {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [GrpObj A]
section Unif
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
end Unif
end GlobalTheory.UnifDifferential


