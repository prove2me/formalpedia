-- Prove2me | solution 1 for AddSubgroup.mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/bc5d9252-4b76-5ef1-841a-0deb2f0685eb

import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Theorems.Thm_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddSubgroup_mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

private theorem gtp_mem_tor {M : Type*} [AddCommGroup M] (n : ℕ) (x : M) :
    x ∈ Submodule.torsionBy ℤ M ((n : ℕ) : ℤ) ↔ n • x = 0 := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]

private theorem gtp_addSubgroup_eq_of_le_of_card_eq {M : Type*} [AddCommGroup M]
    {H K : AddSubgroup M} (hle : H ≤ K) [Finite K]
    (hc : Nat.card ↥H = Nat.card ↥K) : H = K := by
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, SetLike.coe_sort_coe]
  exact hc.ge

private def gtp_tor_equiv {M : Type*} [AddCommGroup M] (p : ℕ) :
    {x : M // p • x = 0} ≃ ↥(Submodule.torsionBy ℤ M ((p : ℕ) : ℤ)) where
  toFun s := ⟨s.1, (gtp_mem_tor p s.1).mpr s.2⟩
  invFun t := ⟨t.1, (gtp_mem_tor p t.1).mp t.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem gtp_finite_tor {M : Type*} [AddCommGroup M] (p : ℕ)
    (hfin1 : Finite {x : M // p • x = 0}) (k : ℕ) :
    Finite {x : M // p ^ k • x = 0} := by
  induction k with
  | zero =>
    haveI : Subsingleton {x : M // p ^ 0 • x = 0} := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      rw [pow_zero, one_nsmul] at ha hb
      exact Subtype.ext (ha.trans hb.symm)
    exact Finite.of_subsingleton
  | succ k ih =>
    haveI := ih
    haveI := hfin1
    have hfib : ∀ y : {w : M // p • w = 0},
        ({z : {x : M // p ^ (k + 1) • x = 0} | p ^ k • (z : M) = (y : M)}).Finite := by
      intro y
      rcases Set.eq_empty_or_nonempty
        {z : {x : M // p ^ (k + 1) • x = 0} | p ^ k • (z : M) = (y : M)} with hemp | hne
      · rw [hemp]; exact Set.finite_empty
      · obtain ⟨x₀, hx₀⟩ := hne
        have hx₀' : p ^ k • (x₀ : M) = (y : M) := hx₀
        have hmap : ∀ z : ↥{z : {x : M // p ^ (k + 1) • x = 0} | p ^ k • (z : M) = (y : M)},
            p ^ k • ((z.1 : M) - (x₀ : M)) = 0 := by
          intro z
          have hz : p ^ k • ((z.1 : M)) = (y : M) := z.2
          rw [nsmul_sub, hz, hx₀', sub_self]
        rw [← Set.finite_coe_iff]
        exact Finite.of_injective
          (fun z => (⟨(z.1 : M) - (x₀ : M), hmap z⟩ : {w : M // p ^ k • w = 0}))
          (fun a b hab => by
            have h := congrArg Subtype.val hab
            apply Subtype.ext
            apply Subtype.ext
            exact sub_left_inj.mp h)
    have huniv : (Set.univ : Set {x : M // p ^ (k + 1) • x = 0}) =
        ⋃ y : {w : M // p • w = 0},
          {z : {x : M // p ^ (k + 1) • x = 0} | p ^ k • (z : M) = (y : M)} := by
      ext z
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
      exact ⟨⟨p ^ k • (z : M), by rw [← mul_nsmul, ← pow_succ]; exact z.2⟩, rfl⟩
    have hU : (Set.univ : Set {x : M // p ^ (k + 1) • x = 0}).Finite := by
      rw [huniv]; exact Set.finite_iUnion hfib
    exact Set.finite_univ_iff.mp hU

private theorem gtp_socle_le {M : Type*} [AddCommGroup M] {p : ℕ} (hp : p.Prime)
    (hcard₁ : Nat.card ↥(Submodule.torsionBy ℤ M ((p : ℕ) : ℤ)) = p ^ 2)
    (H : AddSubgroup M) (e : M) (he : p • e = 0) (heH : e ∉ H) :
    Nat.card {x : ↥H // p • x = 0} ≤ p := by
  classical
  haveI hTpfin : Finite ↥(Submodule.torsionBy ℤ M ((p : ℕ) : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard₁]; exact pow_ne_zero 2 hp.pos.ne')
  set S : AddSubgroup ↥(Submodule.torsionBy ℤ M ((p : ℕ) : ℤ)) :=
    AddSubgroup.comap (Submodule.torsionBy ℤ M ((p : ℕ) : ℤ)).subtype.toAddMonoidHom H
  have hmemS : ∀ z : ↥(Submodule.torsionBy ℤ M ((p : ℕ) : ℤ)), z ∈ S ↔ (z : M) ∈ H :=
    fun z => Iff.rfl
  have hSdvd : Nat.card ↥S ∣ p ^ 2 := by
    rw [← hcard₁, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup S]
    exact dvd_mul_left _ _
  have hSne : Nat.card ↥S ≠ p ^ 2 := by
    intro hcs
    have hSeq : S = ⊤ := by
      apply gtp_addSubgroup_eq_of_le_of_card_eq le_top
      rw [hcs, Nat.card_congr AddSubgroup.topEquiv.toEquiv, hcard₁]
    have heS : (⟨e, (gtp_mem_tor p e).mpr he⟩ :
        ↥(Submodule.torsionBy ℤ M ((p : ℕ) : ℤ))) ∈ S := by
      rw [hSeq]; exact AddSubgroup.mem_top _
    exact heH ((hmemS _).mp heS)
  obtain ⟨j, hj2, hjcard⟩ := (Nat.dvd_prime_pow hp).mp hSdvd
  have hj1 : j ≤ 1 := by
    by_contra hgt
    exact hSne (by rw [hjcard, le_antisymm hj2 (by omega)])
  have e2 : {x : ↥H // p • x = 0} ≃ ↥S :=
    { toFun := fun s =>
        ⟨⟨(s.1 : M), (gtp_mem_tor p ((s.1 : M))).mpr (congrArg Subtype.val s.2)⟩,
          (hmemS _).mpr s.1.2⟩
      invFun := fun z =>
        ⟨⟨(z.1 : M), (hmemS _).mp z.2⟩, Subtype.ext ((gtp_mem_tor p ((z.1 : M))).mp z.1.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e2, hjcard]
  interval_cases j
  · simpa using hp.one_lt.le
  · simp

private theorem gtp_main {M : Type*} [AddCommGroup M] {p : ℕ} (hp : p.Prime) (m : ℕ)
    (K T : AddSubgroup M)
    (hKcard : Nat.card ↥K = p ^ m)
    (hKtors : ∀ x ∈ K, p ^ m • x = 0)
    (hTtors : ∀ x ∈ T, p ^ m • x = 0)
    (e : M) (he : p • e = 0)
    (hcard₁ : Nat.card ↥(Submodule.torsionBy ℤ M ((p : ℕ) : ℤ)) = p ^ 2)
    (heKT : e ∉ K ⊔ T) :
    T ≤ K := by
  classical
  have hHtors : ∀ z ∈ K ⊔ T, p ^ m • z = 0 := by
    intro z hz
    obtain ⟨u, hu, t, ht, hut⟩ := AddSubgroup.mem_sup.mp hz
    rw [← hut, nsmul_add, hKtors u hu, hTtors t ht, add_zero]
  have hfin1 : Finite {x : M // p • x = 0} := by
    haveI hTpfin : Finite ↥(Submodule.torsionBy ℤ M ((p : ℕ) : ℤ)) :=
      Nat.finite_of_card_ne_zero (by rw [hcard₁]; exact pow_ne_zero 2 hp.pos.ne')
    exact Finite.of_equiv _ (gtp_tor_equiv (M := M) p).symm
  haveI hHfin : Finite ↥(K ⊔ T) := by
    haveI := gtp_finite_tor p hfin1 m
    exact Finite.of_injective
      (fun z : ↥(K ⊔ T) => (⟨z.1, hHtors z.1 z.2⟩ : {x : M // p ^ m • x = 0}))
      (fun a b hab => by
        have h := congrArg Subtype.val hab
        exact Subtype.ext h)
  have hsocle : Nat.card {x : ↥(K ⊔ T) // p • x = 0} ≤ p :=
    gtp_socle_le hp hcard₁ (K ⊔ T) e he heKT
  have hexp : ∀ x : ↥(K ⊔ T), p ^ m • x = 0 := fun x => Subtype.ext (hHtors x.1 x.2)
  obtain ⟨-, hHdvd⟩ := IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow hp m hexp hsocle
  have hHle : Nat.card ↥(K ⊔ T) ≤ p ^ m := Nat.le_of_dvd (pow_pos hp.pos m) hHdvd
  have hKleH : Nat.card ↥K ≤ Nat.card ↥(K ⊔ T) :=
    Nat.card_le_card_of_injective
      (fun z : ↥K => (⟨z.1, (le_sup_left : K ≤ K ⊔ T) z.2⟩ : ↥(K ⊔ T)))
      (fun a b hab => by
        have h := congrArg Subtype.val hab
        exact Subtype.ext h)
  have hKH : K = K ⊔ T :=
    gtp_addSubgroup_eq_of_le_of_card_eq le_sup_left
      (le_antisymm hKleH (by rw [hKcard]; exact hHle))
  intro x hx
  have hxH : x ∈ K ⊔ T := (le_sup_right : T ≤ K ⊔ T) hx
  rwa [← hKH] at hxH

theorem solution
    (W : WeierstrassCurve ℤ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (p : ℕ) [Fact p.Prime] (m : ℕ)
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hKcard : Nat.card K = p ^ m)
    (hKtors : ∀ x ∈ K, p ^ m • x = 0)
    (e : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point) (he : p • e = 0)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (p : ℤ)) = p ^ 2)
    (hZeroSub : ∀ x y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • x = 0 → p ^ m • y = 0 →
      W.InZeroComponentAt A x → W.InZeroComponentAt A y → W.InZeroComponentAt A (x - y))
    (hStep3 : ∀ k ∈ K, ¬ W.InZeroComponentAt A (e - k)) :
    ∀ x : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • x = 0 → W.InZeroComponentAt A x → x ∈ K := by
  classical
  have hp : p.Prime := Fact.out

  let T : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point :=
    { carrier := {x | p ^ m • x = 0 ∧ W.InZeroComponentAt A x}
      zero_mem' := ⟨nsmul_zero _, Or.inl rfl⟩
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨by rw [nsmul_add, ha1, hb1, add_zero], ?_⟩
        have hnb : p ^ m • (-b) = 0 := by
          rw [← zero_sub b, nsmul_sub, nsmul_zero, hb1, sub_zero]
        have hznb := hZeroSub 0 b (nsmul_zero _) hb1 (Or.inl rfl) hb2
        rw [zero_sub] at hznb
        have h1 := hZeroSub a (-b) ha1 hnb ha2 hznb
        rwa [sub_neg_eq_add] at h1
      neg_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨by rw [← zero_sub a, nsmul_sub, nsmul_zero, ha1, sub_zero], ?_⟩
        have h0 := hZeroSub 0 a (nsmul_zero _) ha1 (Or.inl rfl) ha2
        rwa [zero_sub] at h0 }
  have hmemT : ∀ x, x ∈ T ↔
      p ^ m • x = 0 ∧ W.InZeroComponentAt A x := fun x => Iff.rfl
  have hTtors : ∀ x ∈ T, p ^ m • x = 0 := fun x hx => ((hmemT x).mp hx).1

  have heKT : e ∉ K ⊔ T := by
    intro hz
    obtain ⟨u, hu, t, ht, hut⟩ := AddSubgroup.mem_sup.mp hz
    have het : e - u = t := by rw [← hut]; abel
    exact hStep3 u hu (by rw [het]; exact ((hmemT t).mp ht).2)
  have hsub : T ≤ K := gtp_main hp m K T hKcard hKtors hTtors e he hcard₁ heKT
  intro x hx hxz
  exact hsub ((hmemT x).mpr ⟨hx, hxz⟩)

end S_AddSubgroup_mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub
end P2MW
export P2MW.S_AddSubgroup_mem_of_torsion_inZeroComponentAt_of_forall_not_inZeroComponentAt_sub (solution)
