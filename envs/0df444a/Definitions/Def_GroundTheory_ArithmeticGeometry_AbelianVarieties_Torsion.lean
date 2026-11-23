-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Torsion
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_Torsion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:12.934209+00:00
-- url     : https://prove2.me/theorems/6ac4278c-2612-4e3b-9309-aacbb07cd409
-- title:
--   Torsion
-- statement:
--   Definitions and structural lemmas for Torsion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/Torsion.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some


set_option autoImplicit false
namespace GroundTheory.Arith.Abelian
open AddSubgroup
section Group
variable {A : Type*} [AddCommGroup A]
noncomputable def zmodHom (n : ℕ) (P : A) (hP : n • P = 0) : ZMod n →+ A :=
  ZMod.lift n ⟨zmultiplesHom A P, by simp [hP]⟩
end Group
section Curve
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
end Curve
end GroundTheory.Arith.Abelian


