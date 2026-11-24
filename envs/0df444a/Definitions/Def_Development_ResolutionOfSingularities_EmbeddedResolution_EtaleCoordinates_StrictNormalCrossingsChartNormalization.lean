-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossingsChartNormalization
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:07:19.19392+00:00
-- url     : https://prove2.me/theorems/85ae6554-96e7-4650-acf8-02c4be8b4bf5
-- title:
--   Strict Normal Crossings Chart Normalization
-- statement:
--   Definitions and structural lemmas for Strict Normal Crossings Chart Normalization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/StrictNormalCrossingsChartNormalization.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def complOrderEmbInv (m : ℕ) (S : Finset (Fin m)) (t : Fin m) : Option (Fin (m - S.card)) :=
  if h : t ∈ S then none else some (Classical.choose (exists_complOrderEmb_eq m S h))
section
variable {Y Y' : Scheme.{u}} {k : Type u} [Field k] {p : Y ⟶ Spec (CommRingCat.of k)}
  {V : Y.Opens} {n : ℕ}
theorem morphismRestrict_comp_map_comp_affineSpaceFinToSpec (c : EtaleChart p V n) (f : Y' ⟶ Y)
    [IsOpenImmersion f] :
    (morphismRestrict f V ≫ c.map) ≫ affineSpaceFinToSpec k n = (f ⁻¹ᵁ V).ι ≫ (f ≫ p) := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, morphismRestrict_ι, Category.assoc]
theorem etale_morphismRestrict_comp_map (c : EtaleChart p V n) (f : Y' ⟶ Y) [IsOpenImmersion f] :
    Etale (morphismRestrict f V ≫ c.map) := by
  have h0 : IsOpenImmersion (morphismRestrict f V ≫ V.ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  have h1 : IsOpenImmersion (morphismRestrict f V) :=
    IsOpenImmersion.of_comp (morphismRestrict f V) V.ι
  have h2 : Etale c.map := c.isEtale
  have h3 : Etale (morphismRestrict f V) := inferInstance
  infer_instance
def EtaleChart.pullbackOpenImmersion (c : EtaleChart p V n) (f : Y' ⟶ Y) [IsOpenImmersion f] :
    EtaleChart (f ≫ p) (f ⁻¹ᵁ V) n :=
  ⟨morphismRestrict f V ≫ c.map, morphismRestrict_comp_map_comp_affineSpaceFinToSpec c f,
    etale_morphismRestrict_comp_map c f⟩
end
section
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
end
section
variable {W : Scheme.{u}} {k : Type u} [Field k]
end
end FunctorialResolution.EmbeddedResolution


