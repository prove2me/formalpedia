-- Prove2me | Definitions.Def_Castro2006_extClasses
-- name    : Castro2006_extClasses
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T19:57:30.317347+00:00
-- url     : https://prove2.me/theorems/6f3f152e-ddf7-49b4-b199-17dfafd16cb2
-- title:
--   Extension classes inducing a given action
-- statement:
--   The induced action on an abelian kernel and the type of extensions inducing a fixed action.

import Mathlib
import Definitions.Def_Castro2006_action
open CategoryTheory

namespace Castro2006
variable {G N E : Type} [Group G] [CommGroup N] [Group E]

lemma conjAct_eq_one_of_mem_range (S : GroupExtension N E G) {e : E} (he : e ∈ S.inl.range) :
    S.conjAct e = 1 := by
  obtain ⟨n, rfl⟩ := he
  ext a
  change S.conjAct (S.inl n) a = a
  apply S.inl_injective
  rw [S.inl_conjAct_comm]
  have hcomm : S.inl n * S.inl a = S.inl a * S.inl n := by
    rw [← map_mul, ← map_mul, mul_comm n a]
  rw [hcomm]
  exact mul_inv_cancel_right (S.inl a) (S.inl n)

noncomputable def inducedAct (S : GroupExtension N E G) : G →* MulAut N :=
  (QuotientGroup.lift S.inl.range S.conjAct (by
    intro e he
    rw [MonoidHom.mem_ker]
    exact conjAct_eq_one_of_mem_range S he)).comp
    S.quotientRangeInlEquivRight.symm.toMonoidHom

structure ExtOf (φ : G →* MulAut N) where
  E : Type
  [grp : Group E]
  S : GroupExtension N E G
  induces : inducedAct S = φ

end Castro2006


