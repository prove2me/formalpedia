-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:03:57.363893+00:00
-- url     : https://prove2.me/theorems/0a89b472-d5b3-4998-babc-1ff8ffb769f7
-- title:
--   Forall Loc In Shift
-- statement:
--   Definitions and structural lemmas for Forall Loc In Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ForallLocInShift.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Theorems.Thm_GlobalTheory_CMVal_Euler_one_coord
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_modF_mul
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_modF_pos
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
noncomputable section
open Filter Topology
namespace GlobalTheory.CMVal.Euler
variable {G : Type} [CommGroup G] (U : Subgroup G) (ω : G →* ℂ)
def cs (M : Set G) (z : G ⧸ U) : ℂ := M.indicator ω z.out
def Stable (M : Set G) : Prop := ∀ u ∈ U, ∀ y, y * u ∈ M ↔ y ∈ M
variable {U ω}
end GlobalTheory.CMVal.Euler
end
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
namespace GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
theorem modF_unit {y : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) = 1) : modF y = 1 := by
  unfold modF
  simp [h]
def omega (χ : HChar E) (S : ℂ) : (Af E)ˣ →* ℂ where
  toFun y := (finPart χ y : ℂ) * ((modF y : ℝ) : ℂ) ^ S
  map_one' := by rw [map_one, modF_unit fun w => by simp [one_coord]]; simp
  map_mul' y y' := by
    rw [map_mul, IdeleModule.modF_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (IdeleModule.modF_pos y).le (IdeleModule.modF_pos y').le, Units.val_mul]
    ring
def intI : Set (Af E)ˣ := {y | ∀ w, Valued.v ((y : Af E) w) ≤ 1}
def MS (m : HeightOneSpectrum (OF E) → ℕ) (T : Finset (HeightOneSpectrum (𝓞 E))) : Set (Af E)ˣ :=
  {y | (∀ v, LocIn (m v) v (y : Af E)) ∧ ∀ w ∈ T, Valued.v ((y : Af E) w) = 1}
end GlobalTheory.CMVal.Euler


