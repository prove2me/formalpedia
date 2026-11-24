-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
-- name    : Development_AutomorphicArithmetic_PrimeDiscriminants_ExistsPrimitiveRootTorsionOrder
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:02.175646+00:00
-- url     : https://prove2.me/theorems/8f503dc9-1ec9-4059-b527-a1f251f866e9
-- title:
--   Exists Primitive Root Torsion Order
-- statement:
--   Definitions and structural lemmas for Exists Primitive Root Torsion Order, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/ExistsPrimitiveRootTorsionOrder.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
open NumberField
noncomputable section
namespace UpperTheory
section field
variable (E : Type) [Field E] [NumberField E]
theorem exists_primitiveRoot_torsionOrder : ∃ ζ : E, IsPrimitiveRoot ζ (Units.torsionOrder E) := by
  obtain ⟨μ, hμ⟩ : ∃ μ : Units.torsion E, orderOf μ = Units.torsionOrder E :=
    IsCyclic.exists_ofOrder_eq_natCard (α := Units.torsion E)
  refine ⟨(((μ : (𝓞 E)ˣ) : 𝓞 E) : E), ?_⟩
  have h1 : IsPrimitiveRoot μ (Units.torsionOrder E) := hμ ▸ IsPrimitiveRoot.orderOf μ
  have h2 : IsPrimitiveRoot (μ : (𝓞 E)ˣ) (Units.torsionOrder E) := IsPrimitiveRoot.coe_submonoidClass_iff.2 h1
  exact (IsPrimitiveRoot.coe_units_iff.2 h2).map_of_injective (f := algebraMap (𝓞 E) E) RingOfIntegers.coe_injective
variable {E}
theorem root_iff_pow_torsionOrder (x : E) : (∃ m : ℕ, 0 < m ∧ x ^ m = 1) ↔ x ^ Units.torsionOrder E = 1 := by
  refine ⟨fun h => ?_, fun h => ⟨_, Units.torsionOrder_pos E, h⟩⟩
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 h
  have : NeZero (orderOf x) := ⟨(orderOf_pos_iff.2 hfin).ne'⟩
  exact orderOf_dvd_iff_pow_eq_one.1 (Units.dvd_torsionOrder_of_isPrimitiveRoot (IsPrimitiveRoot.orderOf x))
theorem two_dvd_torsionOrder : 2 ∣ Units.torsionOrder E := (Units.even_torsionOrder E).two_dvd
theorem roots_pm_iff : (∀ x : E, (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → x = 1 ∨ x = -1) ↔ Units.torsionOrder E = 2 := by
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_torsionOrder E
    refine Nat.dvd_antisymm (hζ.dvd_of_pow_eq_one 2 ?_) two_dvd_torsionOrder
    rcases h ζ ⟨_, Units.torsionOrder_pos E, hζ.pow_eq_one⟩ with rfl | rfl <;> norm_num
  · intro h x hx
    rw [root_iff_pow_torsionOrder, h] at hx
    exact mul_self_eq_one_iff.1 (by rwa [← sq])
end field
end UpperTheory
namespace Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
def w : ℕ := Units.torsionOrder H.E
def nuW (l : ℕ) : ℕ := H.w.factorization l
def IsMu (x : H.E) : Prop := ∃ m : ℕ, 0 < m ∧ x ^ m = 1
theorem muPM_iff : H.MuPM ↔ H.w = 2 := UpperTheory.roots_pm_iff
theorem MuPM.nuW (h : H.MuPM) (l : ℕ) : H.nuW l = if l = 2 then 1 else 0 := by
  unfold HostRaw.nuW
  rw [H.muPM_iff.1 h, Nat.prime_two.factorization, Finsupp.single_apply]
  simp only [eq_comm]
end Formalism.HC.HostRaw
end


