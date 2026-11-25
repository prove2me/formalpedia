-- Prove2me | Definitions.Def_GroundTheory_Brauer_BaseChange
-- name    : GroundTheory_Brauer_BaseChange
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:23:38.352399+00:00
-- url     : https://prove2.me/theorems/be52e3d8-5098-45c9-83a1-b1cbffa339f6
-- title:
--   Base Change
-- statement:
--   Definitions and structural lemmas for Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChange.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Brauer
open TensorProduct
universe u v
section Equivalence
variable {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
theorem IsBrauerEquivalent.baseChange {A B : CSA.{u, v} K} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent (baseChangeCSA L A) (baseChangeCSA L B) := by
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  exact ⟨n, m, hn, hm, ⟨(baseChangeMatrix K L A (Fin n)).symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L) e).trans <|
      baseChangeMatrix K L B (Fin m)⟩⟩
end Equivalence
namespace BrauerGroup
section Hom
variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
noncomputable def baseChangeFun : BrauerGroup.{u, u} K → BrauerGroup.{u, u} L :=
  Quotient.map (baseChangeCSA L) fun _ _ h ↦ IsBrauerEquivalent.baseChange L h
noncomputable def baseChange : BrauerGroup.{u, u} K →* BrauerGroup.{u, u} L where
  toFun := baseChangeFun K L
  map_one' := Quotient.sound <|
    isBrauerEquivalent_of_algEquiv (Algebra.TensorProduct.rid K L L)
  map_mul' := by
    rintro ⟨A⟩ ⟨B⟩
    exact Quotient.sound <| isBrauerEquivalent_of_algEquiv (baseChangeCSATensor L A B)
end Hom
section Relative
variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]
noncomputable def relBrauer : Subgroup (BrauerGroup.{u, u} K) :=
  (baseChange K L).ker
variable {K L}
end Relative
end BrauerGroup
end GroundTheory.Brauer


