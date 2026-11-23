-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:07.631834+00:00
-- url     : https://prove2.me/theorems/5ad002ff-0d71-45c4-96d7-97b21571fe8e
-- title:
--   Weil Is Iff Comm Is Of And Lift Subsingleton
-- statement:
--   Definitions and structural lemmas for Weil Is Iff Comm Is Of And Lift Subsingleton, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/WeilIsIffCommIsOfAndLiftSubsingleton.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.GlobalLift
open CommPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}
def nval {T : Over S} (ν : LB.Gen (negLB A L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν r z J
end GlobalTheory.GlobalLift
namespace GlobalTheory
end GlobalTheory


