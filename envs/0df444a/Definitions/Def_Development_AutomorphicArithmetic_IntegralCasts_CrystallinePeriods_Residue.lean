-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Residue
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Residue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:37.376548+00:00
-- url     : https://prove2.me/theorems/f099def7-a139-41cd-a72e-8cd01f943edd
-- title:
--   Residue
-- statement:
--   Definitions and structural lemmas for Residue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/Residue.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Section
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Ideal IsLocalRing
namespace Reformulated.AutPerF
universe u
variable (p : ℕ) [Fact p.Prime]
variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
  [Fact ¬IsUnit (p : A)]
omit [Fact p.Prime] [CharZero A] in
theorem span_p_le_maximalIdeal : span {(p : A)} ≤ maximalIdeal A := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact (Fact.out : ¬IsUnit (p : A))
omit [Fact ¬IsUnit (p : A)] in
theorem exists_maximalIdeal_pow_le_span_p : ∃ e : ℕ, maximalIdeal A ^ e ≤ span {(p : A)} := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    (show (p : A) ≠ 0 from Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hπ
  refine ⟨e, ?_⟩
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
  exact ⟨u, hu.symm⟩
def modPToResidue : ModP A p →+* ResidueField A :=
  Ideal.Quotient.factor (span_p_le_maximalIdeal p A)
omit [Fact p.Prime] [CharZero A] in
theorem modPToResidue_mk (a : A) : modPToResidue p A (Ideal.Quotient.mk _ a) = residue A a := rfl
omit [Fact p.Prime] [CharZero A] in
theorem modPToResidue_surjective : Function.Surjective (modPToResidue p A) :=
  Ideal.Quotient.factor_surjective _
theorem ker_modPToResidue_le : RingHom.ker (modPToResidue p A) ≤
    RingHom.ker (iterateFrobenius (ModP A p) p (exists_maximalIdeal_pow_le_span_p p A).choose) := by
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, modPToResidue_mk, residue_eq_zero_iff] at hx
  rw [RingHom.mem_ker, iterateFrobenius_def, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  refine (exists_maximalIdeal_pow_le_span_p p A).choose_spec
    (Ideal.pow_le_pow_right (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le ?_)
  exact Ideal.pow_mem_pow hx _
variable [CharP (ResidueField A) p] [PerfectRing (ResidueField A) p]
def residueSection : ResidueField A →+* ModP A p :=
  (RingHom.liftOfSurjective (modPToResidue p A) (modPToResidue_surjective p A)
    ⟨_, ker_modPToResidue_le p A⟩).comp
    (iterateFrobeniusEquiv (ResidueField A) p
      (exists_maximalIdeal_pow_le_span_p p A).choose).symm.toRingHom
variable [IsAdicComplete (span {(p : A)}) A]
def wittResidueToRing : WittVector p (ResidueField A) →+* A :=
  (Ainf.theta p A).comp (Ainf.ofWitt p (residueSection p A))
end Reformulated.AutPerF


