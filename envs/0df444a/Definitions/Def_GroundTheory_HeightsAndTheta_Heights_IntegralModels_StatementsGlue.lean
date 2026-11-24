-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:18:41.006297+00:00
-- url     : https://prove2.me/theorems/4b4d1d93-87a9-4f10-bbe7-d81228310ee4
-- title:
--   Statements Glue
-- statement:
--   Definitions and structural lemmas for Statements Glue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsGlue.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
def GlueModulesStar.Statement : Prop :=
  ∀ (X : Scheme.{0}) (V : X.Opens) (ι : Type) (U : ι → X.Opens),
    V ⊔ ⨆ i, U i = ⊤ → (∀ i j, i ≠ j → U i ⊓ U j ≤ V) →
    ∀ (G : (V : Scheme.{0}).Modules) (F : ∀ i, (U i : Scheme.{0}).Modules)
      (ψ : ∀ i, (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U i ⊓ V ≤ U i))).obj (F i) ≅
        (Scheme.Modules.pullback (X.homOfLE (inf_le_right : U i ⊓ V ≤ V))).obj G),
    ∃ (E : X.Modules) (e₀ : (Scheme.Modules.pullback V.ι).obj E ≅ G)
      (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj E ≅ F i),
      ∀ i, pullbackCompIso (X.homOfLE_ι (inf_le_right : U i ⊓ V ≤ V)) e₀ =
        pullbackCompIso (X.homOfLE_ι (inf_le_left : U i ⊓ V ≤ U i)) (e i) ≪≫ ψ i
def VectorBundleRestrict.Statement : Prop :=
  ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsOpenImmersion f] (E : Y.Modules), IsVectorBundle E →
    IsVectorBundle ((Scheme.Modules.pullback f).obj E)
def VectorBundleLocal.Statement : Prop :=
  ∀ (X : Scheme.{0}) (ι : Type) (U : ι → X.Opens), ⨆ i, U i = ⊤ → ∀ E : X.Modules,
    (∀ i, IsVectorBundle ((Scheme.Modules.pullback (U i).ι).obj E)) → IsVectorBundle E
section Inhabitants
def halfThirdOpens : Bool → SpecZ.Opens := fun b =>
  if b then invOpen (𝟙 SpecZ) 2 else invOpen (𝟙 SpecZ) 3
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Model


