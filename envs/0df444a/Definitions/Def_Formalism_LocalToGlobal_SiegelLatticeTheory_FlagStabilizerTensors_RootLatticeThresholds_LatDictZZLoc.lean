-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:24:17.459812+00:00
-- url     : https://prove2.me/theorems/88fc1b96-5760-4819-ab00-17e9eca7517c
-- title:
--   Lat Dict ZZLoc
-- statement:
--   Definitions and structural lemmas for Lat Dict ZZLoc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open NumberField
namespace Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
section General
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
def orth (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Submodule K V) : Submodule K V where
  carrier := {x | ∀ q ∈ P, h q x = 0}
  add_mem' := by
    intro x y hx hy q hq
    have hx' : ∀ q ∈ P, h q x = 0 := hx
    have hy' : ∀ q ∈ P, h q y = 0 := hy
    simp [hx' q hq, hy' q hq]
  zero_mem' := by
    intro q _
    simp
  smul_mem' := by
    intro c x hx q hq
    have hx' : ∀ q ∈ P, h q x = 0 := hx
    simp [hx' q hq]
def Splits (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Submodule K V) (M : AddSubgroup V) : Prop :=
  ∀ w ∈ M, ∃ w₁ ∈ M, w₁ ∈ P ∧ w - w₁ ∈ orth h P
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {P : Submodule K V} {S : Subring K} {M M₁ M₂ : AddSubgroup V}
end General
section Fix
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
end Fix
section Z
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}
end Z
end Formalism.L2.SG.Pf.LatDictZ.Z3


