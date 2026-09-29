-- Prove2me | solution 1 for AddCommGroup.exists_basis_smul_eq_of_card_torsionBy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/06523a9f-3289-5449-8099-816c7871c110

import Mathlib
import Theorems.Thm_AddCommGroup_exists_mem_torsionBy_smul_eq_of_card_torsionBy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy

set_option autoImplicit false

namespace P2mLwLift

open Module Submodule Function

structure Pres (M : Type*) [AddCommGroup M] (n : ℕ) (V : Type*) [AddCommGroup V] where
  ι : V →+ M
  hι : Injective ι
  hιr : ∀ x : M, x ∈ ι.range ↔ ((n : ℕ) : ℤ) • x = 0

namespace Pres

variable {M : Type*} [AddCommGroup M] {n : ℕ} {V : Type*} [AddCommGroup V]

theorem nsmul_ι (P : Pres M n V) (v : V) : n • P.ι v = 0 := by
  have := (P.hιr (P.ι v)).1 ⟨v, rfl⟩
  rwa [natCast_zsmul] at this

theorem nsmul_self (P : Pres M n V) (v : V) : n • v = 0 :=
  P.hι (by rw [map_nsmul, P.nsmul_ι, map_zero])

theorem exists_eq (P : Pres M n V) {x : M} (hx : n • x = 0) : ∃ v, P.ι v = x := by
  obtain ⟨v, hv⟩ := (P.hιr x).2 (by rwa [natCast_zsmul])
  exact ⟨v, hv⟩

theorem mem_torsionBy (P : Pres M n V) (v : V) : P.ι v ∈ torsionBy ℤ M ((n : ℕ) : ℤ) :=
  (mem_torsionBy_iff _ _).2 ((P.hιr _).1 ⟨v, rfl⟩)

noncomputable def equiv (P : Pres M n V) : V ≃ torsionBy ℤ M ((n : ℕ) : ℤ) :=
  Equiv.ofBijective (fun v => ⟨P.ι v, P.mem_torsionBy v⟩)
    ⟨fun v w h => P.hι (Subtype.ext_iff.1 h), fun x => by
      obtain ⟨v, hv⟩ := (P.hιr x.1).2 ((mem_torsionBy_iff _ _).1 x.2)
      exact ⟨v, Subtype.ext hv⟩⟩

theorem natCard_eq (P : Pres M n V) : Nat.card V = Nat.card (torsionBy ℤ M ((n : ℕ) : ℤ)) :=
  Nat.card_congr P.equiv

theorem zmod_smul_eq_cast_zsmul {W : Type*} [AddCommGroup W] [Module (ZMod n) W] (a : ZMod n)
    (w : W) : a • w = (ZMod.cast a : ℤ) • w := by
  conv_lhs => rw [← ZMod.intCast_zmod_cast a]
  rw [Int.cast_smul_eq_zsmul]

end Pres

theorem nonempty_basis_of_prime {M : Type*} [AddCommGroup M] {N : ℕ} (hN : N.Prime) {r : ℕ}
    {W : Type*} [AddCommGroup W] [Module (ZMod N) W] (P : Pres M N W)
    (hcard : Nat.card (torsionBy ℤ M ((N : ℕ) : ℤ)) = N ^ r) :
    Nonempty (Basis (Fin r) (ZMod N) W) := by
  haveI := Fact.mk hN
  have hW : Nat.card W = N ^ r := P.natCard_eq.trans hcard
  haveI : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; exact pow_ne_zero _ hN.ne_zero)
  haveI : Module.Finite (ZMod N) W := Module.Finite.of_finite
  have hrank : finrank (ZMod N) W = r := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod N) (V := W)
    rw [Nat.card_zmod, hW] at h
    exact (Nat.pow_right_injective hN.two_le h).symm
  exact ⟨Module.finBasisOfFinrankEq _ _ hrank⟩

section Lift

variable {M : Type*} [AddCommGroup M] {ℓ r m : ℕ}
  {V : Type*} [AddCommGroup V] [Module (ZMod (ℓ ^ m)) V]
  {V' : Type*} [AddCommGroup V'] [Module (ZMod (ℓ ^ (m + 1))) V']

structure LiftData (M : Type*) [AddCommGroup M] (ℓ r m : ℕ)
    (V : Type*) [AddCommGroup V] [Module (ZMod (ℓ ^ m)) V]
    (V' : Type*) [AddCommGroup V'] [Module (ZMod (ℓ ^ (m + 1))) V'] where
  P : Pres M (ℓ ^ m) V
  P' : Pres M (ℓ ^ (m + 1)) V'
  hℓ : 0 < ℓ
  h1 : Nat.card (torsionBy ℤ M ((ℓ ^ 1 : ℕ) : ℤ)) = (ℓ ^ 1) ^ r
  hm : Nat.card (torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ)) = (ℓ ^ m) ^ r
  hm1 : Nat.card (torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ)) = (ℓ ^ (m + 1)) ^ r
  hS : ∀ x ∈ torsionBy ℤ M ((ℓ ^ m : ℕ) : ℤ), ∃ y ∈ torsionBy ℤ M ((ℓ ^ (m + 1) : ℕ) : ℤ), ℓ • y = x
  c : Basis (Fin r) (ZMod (ℓ ^ m)) V

namespace LiftData

theorem natCard_V' (D : LiftData M ℓ r m V V') : Nat.card V' = (ℓ ^ (m + 1)) ^ r := D.P'.natCard_eq.trans D.hm1

theorem finite_V' (D : LiftData M ℓ r m V V') : Finite V' :=
  Nat.finite_of_card_ne_zero (by rw [D.natCard_V']; exact pow_ne_zero _ (pow_ne_zero _ D.hℓ.ne'))

theorem exists_lift (D : LiftData M ℓ r m V V') (v : V) : ∃ v' : V', D.P.ι v = ℓ • D.P'.ι v' := by
  obtain ⟨y, hy, hyv⟩ := D.hS (D.P.ι v) (D.P.mem_torsionBy v)
  obtain ⟨v', hv'⟩ := D.P'.exists_eq (x := y) (by
    have := (mem_torsionBy_iff _ _).1 hy; rwa [natCast_zsmul] at this)
  exact ⟨v', by rw [hv', hyv]⟩

noncomputable def v' (D : LiftData M ℓ r m V V') (i : Fin r) : V' := (D.exists_lift (D.c i)).choose

theorem ι_v' (D : LiftData M ℓ r m V V') (i : Fin r) : ℓ • D.P'.ι (D.v' i) = D.P.ι (D.c i) :=
  (D.exists_lift (D.c i)).choose_spec.symm

def mulBy (k : ℕ) : V' →ₗ[ℤ] V' := DistribSMul.toLinearMap ℤ V' k

@[scoped simp] theorem mulBy_apply (k : ℕ) (w : V') : mulBy (V' := V') k w = k • w := rfl

theorem natCard_ker_mulBy (D : LiftData M ℓ r m V V') {j : ℕ} (hj : j ≤ m + 1) :
    Nat.card (LinearMap.ker (mulBy (V' := V') (ℓ ^ j))) =
      Nat.card (torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) := by
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨D.P'.ι w.1, ?_⟩) ⟨?_, ?_⟩)
  · have hw := w.2
    rw [LinearMap.mem_ker, mulBy_apply] at hw
    rw [mem_torsionBy_iff, natCast_zsmul, ← map_nsmul, hw, map_zero]
  · intro x y h
    exact Subtype.ext (D.P'.hι (by simpa using congrArg Subtype.val h))
  · rintro ⟨y, hy⟩
    rw [mem_torsionBy_iff, natCast_zsmul] at hy
    have hy' : ℓ ^ (m + 1) • y = 0 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hj
      rw [hk, pow_add, mul_comm, mul_smul, hy, smul_zero]
    obtain ⟨w, hw⟩ := D.P'.exists_eq hy'
    refine ⟨⟨w, ?_⟩, Subtype.ext (by simpa using hw)⟩
    rw [LinearMap.mem_ker, mulBy_apply]
    apply D.P'.hι
    rw [map_nsmul, hw, hy, map_zero]

theorem exists_eq_pow_smul_of_smul_eq_zero (D : LiftData M ℓ r m V V') (w : V') (hw : ℓ • w = 0) : ∃ z : V', w = ℓ ^ m • z := by
  haveI := D.finite_V'
  set g := mulBy (V' := V') (ℓ ^ m) with hg

  have hmul := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g)
  rw [Nat.card_congr g.quotKerEquivRange.toEquiv, D.natCard_V', D.natCard_ker_mulBy (Nat.le_succ m),
    D.hm] at hmul
  have hrange : Nat.card (LinearMap.range g) = ℓ ^ r := by
    have h : (ℓ ^ m) ^ r * Nat.card (LinearMap.range g) = (ℓ ^ m) ^ r * ℓ ^ r := by
      rw [← hmul, ← mul_pow, ← pow_succ]
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (pow_pos D.hℓ _) _) h

  set K := LinearMap.ker (mulBy (V' := V') (ℓ ^ 1)) with hK
  have hKcard : Nat.card K = ℓ ^ r := by
    rw [hK, D.natCard_ker_mulBy (Nat.succ_le_succ (Nat.zero_le m)), D.h1, pow_one]
  have hle : LinearMap.range g ≤ K := by
    rintro _ ⟨z, rfl⟩
    rw [hK, LinearMap.mem_ker, mulBy_apply, mulBy_apply, ← mul_smul, pow_one, ← pow_succ',
      D.P'.nsmul_self]

  have hbij : Bijective (Submodule.inclusion hle) :=
    (Submodule.inclusion_injective hle).bijective_of_nat_card_le (by rw [hrange, hKcard])
  have hwK : w ∈ K := by rw [hK, LinearMap.mem_ker, mulBy_apply, pow_one, hw]
  obtain ⟨⟨_, z, rfl⟩, hz⟩ := hbij.2 ⟨w, hwK⟩
  exact ⟨z, by (have h__af := ((congrArg Subtype.val hz).symm); simp at h__af; exact h__af)⟩

noncomputable def N (D : LiftData M ℓ r m V V') : Submodule (ZMod (ℓ ^ (m + 1))) V' :=
  span (ZMod (ℓ ^ (m + 1))) (Set.range D.v')

theorem v'_mem_N (D : LiftData M ℓ r m V V') (i : Fin r) : D.v' i ∈ D.N := subset_span ⟨i, rfl⟩

theorem exists_mem_N_add_smul (D : LiftData M ℓ r m V V') (hm0 : 0 < m) (z : V') : ∃ u ∈ D.N, ∃ z' : V', z = u + ℓ • z' := by

  have hz : ℓ ^ m • (ℓ • D.P'.ι z) = 0 := by
    rw [← mul_smul, ← pow_succ, D.P'.nsmul_ι]
  obtain ⟨v, hv⟩ := D.P.exists_eq hz

  set k : Fin r → ℤ := fun i => (ZMod.cast (D.c.repr v i) : ℤ) with hk
  set u : V' := ∑ i, k i • D.v' i with hu
  have huN : u ∈ D.N := Submodule.sum_mem _ fun i _ => zsmul_mem (D.v'_mem_N i) _
  have hιu : D.P'.ι (ℓ • u) = D.P.ι v := by
    rw [map_nsmul, hu, map_sum, Finset.smul_sum]
    have : ∀ i, ℓ • D.P'.ι (k i • D.v' i) = D.P.ι (D.c.repr v i • D.c i) := by
      intro i
      rw [map_zsmul, smul_comm, D.ι_v', Pres.zmod_smul_eq_cast_zsmul, map_zsmul]
    rw [Finset.sum_congr rfl fun i _ => this i, ← map_sum, D.c.sum_repr]

  have hzu : ℓ • (z - u) = 0 := by
    apply D.P'.hι
    rw [smul_sub, map_sub, hιu, hv, map_nsmul, sub_self, map_zero]
  obtain ⟨z'', hz''⟩ := D.exists_eq_pow_smul_of_smul_eq_zero (z - u) hzu
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm0).symm⟩
  refine ⟨u, huN, ℓ ^ m' • z'', ?_⟩
  rw [← mul_smul, ← pow_succ', ← hz'', add_sub_cancel]

theorem exists_mem_N_add_pow_smul (D : LiftData M ℓ r m V V') (hm0 : 0 < m) (k : ℕ) (z : V') :
    ∃ u ∈ D.N, ∃ z' : V', z = u + ℓ ^ k • z' := by
  induction k generalizing z with
  | zero => exact ⟨0, Submodule.zero_mem _, z, by rw [pow_zero, one_smul, zero_add]⟩
  | succ k ih =>
    obtain ⟨u, hu, z', rfl⟩ := ih z
    obtain ⟨u₁, hu₁, z'', rfl⟩ := D.exists_mem_N_add_smul hm0 z'
    refine ⟨u + ℓ ^ k • u₁, Submodule.add_mem _ hu (nsmul_mem hu₁ _), z'', ?_⟩
    rw [smul_add, ← mul_smul, ← pow_succ, add_assoc]

theorem N_eq_top (D : LiftData M ℓ r m V V') (hm0 : 0 < m) : D.N = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨u, hu, z', rfl⟩ := D.exists_mem_N_add_pow_smul hm0 (m + 1) z
  rw [D.P'.nsmul_self, add_zero]
  exact hu

theorem linearIndependent_v' (D : LiftData M ℓ r m V V') (hm0 : 0 < m) : LinearIndependent (ZMod (ℓ ^ (m + 1))) D.v' := by
  haveI := D.finite_V'
  haveI : NeZero (ℓ ^ (m + 1)) := ⟨pow_ne_zero _ D.hℓ.ne'⟩
  haveI : Finite (Fin r →₀ ZMod (ℓ ^ (m + 1))) :=
    Finite.of_equiv (Fin r → ZMod (ℓ ^ (m + 1))) Finsupp.equivFunOnFinite.symm
  have hsurj : Surjective (Finsupp.linearCombination (ZMod (ℓ ^ (m + 1))) D.v') := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact D.N_eq_top hm0
  have hcard : Nat.card (Fin r →₀ ZMod (ℓ ^ (m + 1))) ≤ Nat.card V' := by
    rw [Nat.card_congr Finsupp.equivFunOnFinite, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin, D.natCard_V']
  exact (hsurj.bijective_of_nat_card_le hcard).1

noncomputable def liftedBasis (D : LiftData M ℓ r m V V') (hm0 : 0 < m) : Basis (Fin r) (ZMod (ℓ ^ (m + 1))) V' :=
  Basis.mk (D.linearIndependent_v' hm0) (by rw [← N, D.N_eq_top hm0])

theorem liftedBasis_apply (D : LiftData M ℓ r m V V') (hm0 : 0 < m) (i : Fin r) : D.liftedBasis hm0 i = D.v' i := by
  rw [liftedBasis, Basis.coe_mk]

theorem exists_basis_smul_eq (D : LiftData M ℓ r m V V') (hprime : ℓ.Prime) :
    ∃ c' : Basis (Fin r) (ZMod (ℓ ^ (m + 1))) V', ∀ i, D.P.ι (D.c i) = ℓ • D.P'.ι (c' i) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  ·
    subst hm0
    have hN : (ℓ ^ (0 + 1)).Prime := by rwa [zero_add, pow_one]
    obtain ⟨c'⟩ := nonempty_basis_of_prime hN D.P' D.hm1
    refine ⟨c', fun i => ?_⟩
    have h1 : D.P.ι (D.c i) = 0 := by
      simpa only [pow_zero, one_smul] using D.P.nsmul_ι (D.c i)
    have h2 : ℓ • D.P'.ι (c' i) = 0 := by
      simpa only [zero_add, pow_one] using D.P'.nsmul_ι (c' i)
    rw [h1, h2]
  · exact ⟨D.liftedBasis hm0, fun i => by rw [D.liftedBasis_apply, D.ι_v']⟩

end LiftData
p2m_reactivate "P2MW.S_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy.P2mLwLift.LiftData"

end Lift
p2m_reactivate "P2MW.S_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy.P2mLwLift.LiftData"

end P2mLwLift
p2m_reactivate "P2MW.S_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy.P2mLwLift.LiftData P2MW.S_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy.P2mLwLift"

theorem solution (ℓ : ℕ) [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] (r m : ℕ)
    (hcard : ∀ j ≤ m + 1, Nat.card (Submodule.torsionBy ℤ M ((ℓ ^ j : ℕ) : ℤ)) = (ℓ ^ j) ^ r)
    {V : Type*} [AddCommGroup V] [Module (ZMod (ℓ ^ m)) V]
    (ι : V →+ M) (hι : Function.Injective ι)
    (hιr : ∀ x : M, x ∈ ι.range ↔ ((ℓ ^ m : ℕ) : ℤ) • x = 0)
    {V' : Type*} [AddCommGroup V'] [Module (ZMod (ℓ ^ (m + 1))) V']
    (ι' : V' →+ M) (hι' : Function.Injective ι')
    (hι'r : ∀ x : M, x ∈ ι'.range ↔ ((ℓ ^ (m + 1) : ℕ) : ℤ) • x = 0)
    (c : Module.Basis (Fin r) (ZMod (ℓ ^ m)) V) :
    ∃ c' : Module.Basis (Fin r) (ZMod (ℓ ^ (m + 1))) V', ∀ i, ι (c i) = ℓ • ι' (c' i) := by
  let D : P2mLwLift.LiftData M ℓ r m V V' :=
    { P := ⟨ι, hι, hιr⟩, P' := ⟨ι', hι', hι'r⟩, hℓ := (Fact.out : ℓ.Prime).pos,
      h1 := hcard 1 (Nat.succ_le_succ (Nat.zero_le m)), hm := hcard m (Nat.le_succ m),
      hm1 := hcard (m + 1) le_rfl,
      hS := AddCommGroup.exists_mem_torsionBy_smul_eq_of_card_torsionBy ℓ r m hcard, c := c }
  exact D.exists_basis_smul_eq Fact.out

end S_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy
end P2MW
export P2MW.S_AddCommGroup_exists_basis_smul_eq_of_card_torsionBy (solution)
