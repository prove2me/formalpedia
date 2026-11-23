-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
-- name    : GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:17.078512+00:00
-- url     : https://prove2.me/theorems/9ea7e7da-a59f-40d7-b8c0-567beb35ffee
-- title:
--   Closed Subgroups
-- statement:
--   Definitions and structural lemmas for Closed Subgroups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ClosedSubgroups.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_val_unitsPadicEquiv_apply
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_castHom_proj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_symm_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.val_unitsPadicEquiv_apply


set_option autoImplicit false
open Filter Topology
open scoped GroundTheory.LocalField.Abstract
namespace GroundTheory.Global
namespace Cyclotomic
open GroundTheory.LocalField.Abstract
section Padic
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
end Padic
section ProfiniteInteger
def factorialPNat (n : ℕ) : ℕ+ := ⟨(n + 1).factorial, Nat.factorial_pos _⟩
theorem tendsto_natCast (a : ℤ̂) :
    Tendsto (fun n : ℕ => (((ProfiniteInteger.proj (factorialPNat n) a).val : ℕ) : ℤ̂)) atTop
      (𝓝 a) := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  intro m
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [eventually_ge_atTop (m : ℕ)] with n hn
  have hdvd : (m : ℕ) ∣ (factorialPNat n : ℕ) := Nat.dvd_factorial m.pos (by omega)
  have h := ProfiniteInteger.castHom_proj hdvd a
  rw [ZMod.castHom_apply, ZMod.cast_eq_val] at h
  simp only [ProfiniteInteger.proj_apply] at h
  rw [← h]
  rfl
theorem denseRange_natCast : DenseRange (Nat.cast : ℕ → ℤ̂) := fun a =>
  mem_closure_of_tendsto (tendsto_natCast a) (Eventually.of_forall fun _ => Set.mem_range_self _)
theorem mul_mem_of_isClosed' (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂)) {x : ℤ̂}
    (hx : x ∈ H) (a : ℤ̂) : a * x ∈ H :=
  denseRange_natCast.induction_on a (hH.preimage (continuous_id.mul continuous_const))
    fun k => by
      show (k : ℤ̂) * x ∈ H
      rw [← nsmul_eq_mul]
      exact H.nsmul_mem hx k
def idealOfIsClosed (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂)) : Ideal ℤ̂ where
  carrier := H
  add_mem' := H.add_mem
  zero_mem' := H.zero_mem
  smul_mem' a _ hx := mul_mem_of_isClosed' H hH hx a
noncomputable def primeIdempotent (q : Nat.Primes) : ℤ̂ :=
  ofPadics (Pi.single q 1)
end ProfiniteInteger
end Cyclotomic
end GroundTheory.Global


