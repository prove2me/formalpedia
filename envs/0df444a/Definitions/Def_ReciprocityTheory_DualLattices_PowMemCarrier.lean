-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
-- name    : ReciprocityTheory_DualLattices_PowMemCarrier
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:37:26.527413+00:00
-- url     : https://prove2.me/theorems/0fb9db2c-f48b-5f08-889f-c1beeea17dab
-- title:
--   Pow Mem Carrier
-- statement:
--   Definitions and structural lemmas for Pow Mem Carrier, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/PowMemCarrier.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ColengthCotangentBoundStatementOfClaim
import Definitions.Def_ReciprocityTheory_DualLattices_PrimeHopfOrderOfAddEquiv
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLat
import Definitions.Def_ReciprocityTheory_DualLattices_ImportsBis
import Definitions.Def_ReciprocityTheory_DualLattices_SqIdeal
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h1
import Theorems.Thm_ReciprocityTheory_PGsh_L2_h2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section SlopeTestRemainingChoices
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable (K : AddSubgroup N) [DecidablePred (· ∈ K)] [DecidableEq (N ⧸ K)] [Fintype (N ⧸ K)]
end SlopeTestRemainingChoices
def zmodEquiv (p : ℕ) [Fact p.Prime] {N : Type} [AddCommGroup N] (x : N) (hx : p • x = 0)
    (hx0 : x ≠ 0) : ZMod p ≃+ AddSubgroup.zmultiples x := by
  let f0 : ℤ →+ AddSubgroup.zmultiples x := zmultiplesHom _ ⟨x, AddSubgroup.mem_zmultiples x⟩
  have hf0 : f0 p = 0 := by
    apply Subtype.ext
    simp [f0, hx]
  let f : ZMod p →+ AddSubgroup.zmultiples x := ZMod.lift p ⟨f0, hf0⟩
  have hord : addOrderOf x = p := addOrderOf_eq_prime hx hx0
  refine AddEquiv.ofBijective f ⟨(injective_iff_map_eq_zero f).2 fun k hk => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := ZMod.intCast_surjective k
    have h1 : f0 m = 0 := by rw [← ZMod.lift_coe p ⟨f0, hf0⟩ m]; exact hk
    have h2 : m • x = 0 := by
      have := congrArg Subtype.val h1
      simpa [f0] using this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← hord]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.2 h2
  · rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hy
    refine ⟨(m : ZMod p), ?_⟩
    rw [ZMod.lift_coe]
    rfl
def ClaimBody (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N]
    (AA : HopfOrder (C := C) R N) : Prop :=
  ∃ (n : ℕ) (g : Fin n → N → C) (δ : Fin n → R),
    (∀ i, g i ∈ augIdeal AA.carrier) ∧
    (∀ f ∈ augIdeal AA.carrier, ∃ r : Fin n → R,
      f - ∑ j, r j • g j ∈ sqIdeal (augIdeal AA.carrier)) ∧
    (∀ i, ∃ a : Fin n → R,
      δ i • g i - ∑ j, (if j < i then a j else 0) • g j ∈ sqIdeal (augIdeal AA.carrier)) ∧
    ∀ c, HasColen R v AA.carrier c →
      c ^ 2 = (∏ i, v (algebraMap R C (δ i))) ^ Fintype.card N
end ReciprocityTheory.PGsh.Up


