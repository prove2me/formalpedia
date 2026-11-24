-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:02.778683+00:00
-- url     : https://prove2.me/theorems/cd94de35-a9b7-46e4-8ed1-7fd346d74992
-- title:
--   Cartan
-- statement:
--   Definitions and structural lemmas for Cartan, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/Cartan.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace Limits
universe w u
variable {X : TopCat.{u}}
section
variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
def constCochain {V : Opens X} (hUV : ∀ a, U a ≤ V) (s : P.obj (op V)) : Cochain P U 0 :=
  fun i => res P ((inter_le U i 0).trans (hUV (i 0))) s
end
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u})
  (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P)
section
variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
end
variable (B : Opens X → Prop)
def CechCondition (F : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ V, B V → ∀ (ι : Type u) [Finite ι] (U : ι → Opens X), (∀ a, B (U a)) → iSup U = V →
    CechAcyclic F.obj U
variable {B}
variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
end GroundTheory.Arith.SchemeCoh


