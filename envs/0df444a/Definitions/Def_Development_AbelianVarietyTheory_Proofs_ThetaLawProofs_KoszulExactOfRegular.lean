-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfRegular
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfRegular
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:10:14.700749+00:00
-- url     : https://prove2.me/theorems/3a5adc12-4445-422c-b284-65a56df1aee1
-- title:
--   Koszul Exact Of Regular
-- statement:
--   Definitions and structural lemmas for Koszul Exact Of Regular, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/KoszulExactOfRegular.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_compat
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom


set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory
noncomputable section
namespace GlobalTheory.KeyKa.KosBasis
variable {K : Type} [CommRing K]
abbrev lf (x : KeyIn K) {l : ℕ} (s : RR x l) (c : x.P.L.ι) : Γ(x.P.A.left, x.P.L.U c) := s.f c
def phi (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (v : Fin N → K) (c : x.P.L.ι) :
    Γ(x.P.A.left, x.P.L.U c) := ∑ k, cst x.P.A.hom (x.P.L.U c) (v k) * lf x (b k) c
def sec (x : KeyIn K) {l N : ℕ} (b : Fin N → RR x l) (v : Fin N → K) : RR x l where
  f := fun c => phi x b v c
  compat := fun i j => by
    obtain ⟨u, hu⟩ : ∃ u : Γ(x.P.A.left, x.P.L.U i ⊓ x.P.L.U j), u = ((pw x.P.L (l : ℤ)).g i j).val :=
      ⟨_, rfl⟩
    have h : ∀ k, rs x.P.A.left (inf_le_left : x.P.L.U i ⊓ x.P.L.U j ≤ _) (lf x (b k) i) =
        u * rs x.P.A.left (inf_le_right : x.P.L.U i ⊓ x.P.L.U j ≤ _) (lf x (b k) j) :=
      fun k => hu ▸ (b k).compat i j
    have h' : rs x.P.A.left (inf_le_left : x.P.L.U i ⊓ x.P.L.U j ≤ _) (phi x b v i) =
        u * rs x.P.A.left (inf_le_right : x.P.L.U i ⊓ x.P.L.U j ≤ _) (phi x b v j) := by
      simp only [phi, map_sum, map_mul, rs_cst, h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    subst hu
    exact h'
end GlobalTheory.KeyKa.KosBasis
end


