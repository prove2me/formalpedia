-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:40.603123+00:00
-- url     : https://prove2.me/theorems/98b294cb-1c10-486e-84e2-27ce589e466c
-- title:
--   Exists Subgroup Of Finite
-- statement:
--   Definitions and structural lemmas for Exists Subgroup Of Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSubgroupOfFinite.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace GlobalTheory.LevQuot
variable {X Y : Scheme.{0}}
def autOver (r : X ⟶ Y) : Subgroup (Aut X) where
  carrier := {ρ | ρ.hom ≫ r = r}
  mul_mem' := fun {a b} ha hb => by
    show (b.hom ≫ a.hom) ≫ r = r
    rw [Category.assoc, ha, hb]
  one_mem' := Category.id_comp _
  inv_mem' := fun {a} ha => by
    show a.inv ≫ r = r
    exact (Iso.inv_comp_eq a).2 (Eq.symm ha)
end GlobalTheory.LevQuot


