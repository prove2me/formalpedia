-- Prove2me | Definitions.Def_TarchaBraids_endpoint_permutation_action_v1
-- name    : TarchaBraids_endpoint_permutation_action_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-21T23:16:55.274561+00:00
-- url     : https://prove2.me/theorems/61e15b96-bd65-4401-adeb-480d6a0b4b60
-- title:
--   Symmetric-group relabelling action on ordered configurations
-- statement:
--   The symmetric group acts continuously on ordered configurations by relabelling strands. A permutation g sends a labelled configuration p to the configuration whose coordinate function is p composed with g inverse.
-- source:
--   Standard ordered-configuration model of braid groups and the symmetric-group deck action.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace TarchaBraids

open BraidsLinksMCG

def orderedConfigPermute {n : ℕ} (g : Equiv.Perm (Fin n)) (p : OrderedConfig n) :
    OrderedConfig n :=
  ⟨p.1 ∘ g.symm, p.2.comp g.symm.injective⟩

instance orderedConfigPermMulAction (n : ℕ) :
    MulAction (Equiv.Perm (Fin n)) (OrderedConfig n) where
  smul g p := orderedConfigPermute g p
  one_smul p := by
    apply Subtype.ext
    rfl
  mul_smul g h p := by
    apply Subtype.ext
    rfl

instance orderedConfigPermContinuous (n : ℕ) :
    ContinuousConstSMul (Equiv.Perm (Fin n)) (OrderedConfig n) where
  continuous_const_smul g := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i =>
      (continuous_apply (g.symm i)).comp continuous_subtype_val

end TarchaBraids


