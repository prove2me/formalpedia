-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrOpen
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobalFunctionsDvrOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:33.397111+00:00
-- url     : https://prove2.me/theorems/fd8171d1-8cad-4771-acd5-798abdf9ef3b
-- title:
--   Global Functions Dvr Open
-- statement:
--   Definitions and structural lemmas for Global Functions Dvr Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/GlobalFunctionsDvrOpen.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GlobFnsDvr
import Definitions.Def_Lemmata_GeneralBFactFurther_Imports
import Theorems.Thm_Bl_general_b_fact_further_goal1

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen
variable {V : Type} [CommRing V] [IsDomain V]
theorem isLocalization_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ (FractionRing V) := by
  first | exact Bl.general_b_fact_further.goal1 .. | (apply Bl.general_b_fact_further.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_further.goal1 <;> assumption)
theorem isOpenImmersion_frac [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) :
    IsOpenImmersion (spMap (algebraMap V (FractionRing V))) := by
  have := isLocalization_frac hϖ
  let e := IsLocalization.algEquiv (Submonoid.powers ϖ) (Localization.Away ϖ) (FractionRing V)
  have he : algebraMap V (FractionRing V) =
      (e : Localization.Away ϖ →+* FractionRing V).comp (algebraMap V (Localization.Away ϖ)) :=
    RingHom.ext fun x => (e.commutes x).symm
  have : IsIso (CommRingCat.ofHom (e : Localization.Away ϖ →+* FractionRing V)) :=
    ⟨⟨CommRingCat.ofHom (e.symm : FractionRing V →+* Localization.Away ϖ), by ext x; simp, by ext x; simp⟩⟩
  show IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))))
  rw [he, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance
end ReciprocityTheory.ChartRestriction.G.Geo.Tor.GlobalFunctionsDvrOpen


