-- Prove2me | solution 1 for AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/1bff5958-94d0-5ad9-af39-622f01a76313

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace P2MKcCB

variable {A : Type*} [AddCommGroup A] {n : ℕ} [NeZero n]

theorem mem_T_iff {a : A} : a ∈ Submodule.torsionBy ℤ A n ↔ n • a = 0 := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]

def σT (σ : A →+ A) : Submodule.torsionBy ℤ A n →+ Submodule.torsionBy ℤ A n where
  toFun t := ⟨σ t, mem_T_iff.2 (by rw [← map_nsmul, mem_T_iff.1 t.2, map_zero])⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

@[scoped simp] theorem coe_σT (σ : A →+ A) (t : Submodule.torsionBy ℤ A n) : (σT σ t : A) = σ t := rfl

variable (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) (σ : A →+ A)

def Sg : ZMod n × ZMod n →+ ZMod n × ZMod n :=
  (e.symm.toAddMonoidHom.comp (σT σ)).comp e.toAddMonoidHom

theorem coe_e_Sg (v : ZMod n × ZMod n) : ((e (Sg e σ v) : Submodule.torsionBy ℤ A n) : A) = σ (e v : A) := by
  simp [Sg]

theorem zsmul_eq_nsmul (c : ZMod n) (v : ZMod n × ZMod n) : c • v = c.val • v := by
  ext <;> simp [nsmul_eq_mul]

theorem Sg_smul (c : ZMod n) (v : ZMod n × ZMod n) : Sg e σ (c • v) = c • Sg e σ v := by
  rw [zsmul_eq_nsmul, map_nsmul, ← zsmul_eq_nsmul]

def d (v : ZMod n × ZMod n) : ZMod n := v.1 * (Sg e σ v).2 - v.2 * (Sg e σ v).1

theorem exists_addEquiv_of_isUnit (v : ZMod n × ZMod n) (hv : IsUnit (d e σ v)) :
    ∃ e' : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n,
      ((e' (0, 1) : Submodule.torsionBy ℤ A n) : A) = σ ((e' (1, 0) : Submodule.torsionBy ℤ A n) : A) := by
  obtain ⟨u, hu⟩ := hv
  set s := Sg e σ v with hs
  have hd : (u : ZMod n) = v.1 * s.2 - v.2 * s.1 := hu
  set di : ZMod n := ((u⁻¹ : (ZMod n)ˣ) : ZMod n) with hdi
  have hdd : di * (v.1 * s.2 - v.2 * s.1) = 1 := by rw [← hd, hdi, Units.inv_mul]
  let φ : ZMod n × ZMod n ≃+ ZMod n × ZMod n :=
    { toFun := fun x => (x.1 * v.1 + x.2 * s.1, x.1 * v.2 + x.2 * s.2)
      invFun := fun y => (di * (s.2 * y.1 - s.1 * y.2), di * (-v.2 * y.1 + v.1 * y.2))
      left_inv := by
        rintro ⟨x, y⟩
        simp only [Prod.mk.injEq]
        constructor
        · linear_combination x * hdd
        · linear_combination y * hdd
      right_inv := by
        rintro ⟨y₁, y₂⟩
        simp only [Prod.mk.injEq]
        constructor
        · linear_combination y₁ * hdd
        · linear_combination y₂ * hdd
      map_add' := by
        rintro ⟨x, y⟩ ⟨x', y'⟩
        simp only [Prod.mk_add_mk, Prod.mk.injEq]
        constructor <;> ring }
  refine ⟨φ.trans e, ?_⟩
  have h10 : φ (1, 0) = v := by
    show ((1 : ZMod n) * v.1 + 0 * s.1, (1 : ZMod n) * v.2 + 0 * s.2) = v
    ext <;> simp
  have h01 : φ (0, 1) = s := by
    show ((0 : ZMod n) * v.1 + 1 * s.1, (0 : ZMod n) * v.2 + 1 * s.2) = s
    ext <;> simp
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, h10, h01, hs, coe_e_Sg]

section Local

variable {p : ℕ} (hpn : p ∣ n)
include hpn

theorem exists_eq_mul_of_cast_eq_zero (x : ZMod n) (hx : ZMod.castHom hpn (ZMod p) x = 0) :
    ∃ y : ZMod n, x = (p : ZMod n) * y := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hx
  obtain ⟨m, hm⟩ := hx
  refine ⟨(m : ZMod n), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hm, Nat.cast_mul]

theorem cast_p_mul (y : ZMod n) : ZMod.castHom hpn (ZMod p) ((p : ZMod n) * y) = 0 := by
  rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

theorem exists_eq_mul_of_p_mul_eq_zero (hp : p.Prime) (x : ZMod n) (hx : (p : ZMod n) * x = 0) :
    ∃ y : ZMod n, x = ((n / p : ℕ) : ZMod n) * y := by
  have h1 : n ∣ p * x.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val]; exact hx
  have h2 : n / p ∣ x.val := by
    obtain ⟨m, hm⟩ := h1
    refine ⟨m, Nat.eq_of_mul_eq_mul_left hp.pos ?_⟩
    rw [hm, ← mul_assoc, Nat.mul_div_cancel' hpn]
  obtain ⟨m, hm⟩ := h2
  refine ⟨(m : ZMod n), ?_⟩
  rw [← ZMod.natCast_zmod_val x, hm, Nat.cast_mul]

theorem q_mul_p : ((n / p : ℕ) : ZMod n) * (p : ZMod n) = 0 := by
  rw [← Nat.cast_mul, Nat.div_mul_cancel hpn, ZMod.natCast_self]

def rV : ZMod n × ZMod n →+ ZMod p × ZMod p :=
  (ZMod.castHom hpn (ZMod p)).toAddMonoidHom.prodMap (ZMod.castHom hpn (ZMod p)).toAddMonoidHom

theorem rV_apply (v : ZMod n × ZMod n) :
    rV hpn v = (ZMod.castHom hpn (ZMod p) v.1, ZMod.castHom hpn (ZMod p) v.2) := rfl

theorem exists_eq_add_of_rV_eq {v v' : ZMod n × ZMod n} (h : rV hpn v = rV hpn v') :
    ∃ t : ZMod n × ZMod n, v = v' + (p : ZMod n) • t := by
  rw [rV_apply, rV_apply, Prod.mk.injEq] at h
  obtain ⟨t₁, ht₁⟩ := exists_eq_mul_of_cast_eq_zero hpn (v.1 - v'.1) (by rw [map_sub, h.1, sub_self])
  obtain ⟨t₂, ht₂⟩ := exists_eq_mul_of_cast_eq_zero hpn (v.2 - v'.2) (by rw [map_sub, h.2, sub_self])
  refine ⟨(t₁, t₂), ?_⟩
  ext
  · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]; linear_combination ht₁
  · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]; linear_combination ht₂

theorem rV_p_smul (t : ZMod n × ZMod n) : rV hpn ((p : ZMod n) • t) = 0 := by
  rw [rV_apply]
  ext
  · simp only [Prod.smul_fst, smul_eq_mul, Prod.fst_zero]; exact cast_p_mul hpn _
  · simp only [Prod.smul_snd, smul_eq_mul, Prod.snd_zero]; exact cast_p_mul hpn _

theorem cast_d_eq_of_rV_eq {v v' : ZMod n × ZMod n} (h : rV hpn v = rV hpn v') :
    ZMod.castHom hpn (ZMod p) (d e σ v) = ZMod.castHom hpn (ZMod p) (d e σ v') := by
  obtain ⟨t, rfl⟩ := exists_eq_add_of_rV_eq hpn h
  have hS : rV hpn (Sg e σ (v' + (p : ZMod n) • t)) = rV hpn (Sg e σ v') := by
    rw [map_add, Sg_smul, map_add, rV_p_smul, add_zero]
  rw [rV_apply, rV_apply, Prod.mk.injEq] at h hS
  simp only [d, map_sub, map_mul, h.1, h.2, hS.1, hS.2]

theorem exists_cast_d_ne_zero (hp : p.Prime)
    (hns : ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    ∃ u : ZMod n × ZMod n, ZMod.castHom hpn (ZMod p) (d e σ u) ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha, hna⟩ := hns
  have hpa : p • a = 0 := by rw [← ha]; exact addOrderOf_nsmul_eq_zero a
  have haT : a ∈ Submodule.torsionBy ℤ A n := by
    rw [mem_T_iff]
    obtain ⟨m, hm⟩ := hpn
    rw [hm, mul_comm, mul_nsmul', hpa, nsmul_zero]
  set w : ZMod n × ZMod n := e.symm ⟨a, haT⟩ with hw_def
  have hew : (e w : A) = a := by rw [hw_def, AddEquiv.apply_symm_apply]
  have hpw : (p : ZMod n) • w = 0 := by
    apply e.injective
    rw [zsmul_eq_nsmul, map_nsmul, map_zero, ZMod.val_natCast]
    apply Subtype.ext
    show (p % n) • ((e w : Submodule.torsionBy ℤ A n) : A) = 0
    rw [hew]
    have : (p % n) • a = p • a := by
      conv_rhs => rw [← Nat.mod_add_div p n]
      rw [add_nsmul, mul_comm, mul_nsmul', mem_T_iff.1 haT, nsmul_zero, add_zero]
    rw [this, hpa]
  have hw0 : w ≠ 0 := by
    intro h
    have : a = 0 := by
      rw [← hew, h, map_zero]; rfl
    rw [this, addOrderOf_zero] at ha
    exact hp.one_lt.ne ha
  have hSw : ∀ c : ZMod n, Sg e σ w ≠ c • w := by
    intro c hc
    apply hna c.val
    rw [← hew, ← coe_e_Sg, hc, zsmul_eq_nsmul, map_nsmul]
    rfl

  obtain ⟨u₁, hu₁⟩ := exists_eq_mul_of_p_mul_eq_zero hpn hp w.1
    (by have := congrArg Prod.fst hpw; simpa using this)
  obtain ⟨u₂, hu₂⟩ := exists_eq_mul_of_p_mul_eq_zero hpn hp w.2
    (by have := congrArg Prod.snd hpw; simpa using this)
  set q : ZMod n := ((n / p : ℕ) : ZMod n) with hq
  set u : ZMod n × ZMod n := (u₁, u₂) with hu
  have hwu : w = q • u := by ext <;> simp [hu, hu₁, hu₂]
  refine ⟨u, fun hdu => ?_⟩

  set r := ZMod.castHom hpn (ZMod p) with hr
  set ub : ZMod p × ZMod p := rV hpn u with hub
  set sb : ZMod p × ZMod p := rV hpn (Sg e σ u) with hsb
  have hdet : ub.1 * sb.2 - ub.2 * sb.1 = 0 := by
    have : r (d e σ u) = ub.1 * sb.2 - ub.2 * sb.1 := by
      simp only [d, map_sub, map_mul, hub, hsb, rV_apply, hr]
    rw [← this]; exact hdu
  have hdep : ∃ α β : ZMod p, (α ≠ 0 ∨ β ≠ 0) ∧ α • ub + β • sb = 0 := by
    by_cases hub0 : ub = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by rw [hub0, smul_zero, zero_smul, add_zero]⟩
    · by_cases h1 : ub.1 ≠ 0
      · refine ⟨-sb.1, ub.1, Or.inr h1, ?_⟩
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_zero]; ring
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_zero]; linear_combination hdet
      · push Not at h1
        have h2 : ub.2 ≠ 0 := by
          intro h2; exact hub0 (Prod.ext h1 h2)
        refine ⟨-sb.2, ub.2, Or.inr h2, ?_⟩
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.fst_zero]; linear_combination -hdet
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, Prod.snd_zero]; ring
  obtain ⟨αb, βb, hnz, hrel⟩ := hdep

  set α : ZMod n := (αb.val : ZMod n) with hα
  set β : ZMod n := (βb.val : ZMod n) with hβ
  have hrα : r α = αb := by rw [hα, map_natCast, ZMod.natCast_zmod_val]
  have hrβ : r β = βb := by rw [hβ, map_natCast, ZMod.natCast_zmod_val]
  have hz : rV hpn (α • u + β • Sg e σ u) = 0 := by
    have : rV hpn (α • u + β • Sg e σ u) = αb • ub + βb • sb := by
      rw [hub, hsb, rV_apply, rV_apply, rV_apply]
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, map_add, map_mul, ← hr, hrα, hrβ]
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, map_add, map_mul, ← hr, hrα, hrβ]
    rw [this, hrel]
  obtain ⟨t, ht⟩ := exists_eq_add_of_rV_eq hpn (v' := 0) (by rw [hz, map_zero])
  rw [zero_add] at ht
  have hstar : α • w + β • Sg e σ w = 0 := by
    have : q • (α • u + β • Sg e σ u) = 0 := by
      rw [ht, smul_smul, hq, q_mul_p hpn, zero_smul]
    rw [hwu, Sg_smul, smul_comm α q u, smul_comm β q, ← smul_add, this]
  have hpS : (p : ZMod n) • Sg e σ w = 0 := by rw [← Sg_smul, hpw, map_zero]

  have hinv : ∀ γb : ZMod p, γb ≠ 0 → ∀ γ : ZMod n, r γ = γb →
      ∃ γ' t' : ZMod n, γ' * γ = 1 + (p : ZMod n) * t' := by
    intro γb hγb γ hγ
    set γ' : ZMod n := ((γb⁻¹).val : ZMod n)
    have hr' : r γ' = γb⁻¹ := by simp [γ', hr]
    obtain ⟨t', ht'⟩ := exists_eq_mul_of_cast_eq_zero hpn (γ' * γ - 1)
      (by rw [map_sub, map_mul, map_one, ← hr, hr', hγ, inv_mul_cancel₀ hγb, sub_self])
    exact ⟨γ', t', by linear_combination ht'⟩
  rcases hnz with hαb | hβb
  ·
    by_cases hβb : βb = 0
    · obtain ⟨tβ, htβ⟩ := exists_eq_mul_of_cast_eq_zero hpn β (by rw [← hr, hrβ, hβb])
      have hβS : β • Sg e σ w = 0 := by rw [htβ, mul_comm, ← smul_smul, hpS, smul_zero]
      rw [hβS, add_zero] at hstar
      obtain ⟨α', t', hα'⟩ := hinv αb hαb α hrα
      apply hw0
      calc w = (α' * α) • w - t' • ((p : ZMod n) • w) := by
              rw [hα', add_smul, one_smul, smul_smul, mul_comm t', add_sub_cancel_right]
        _ = 0 := by rw [← smul_smul, hstar, smul_zero, hpw, smul_zero, sub_zero]
    · obtain ⟨β', t', hβ'⟩ := hinv βb hβb β hrβ
      apply hSw (-(β' * α))
      have h1 : β' • (α • w + β • Sg e σ w) = 0 := by rw [hstar, smul_zero]
      rw [smul_add, smul_smul, smul_smul, hβ', add_smul, one_smul, mul_smul (p : ZMod n) t',
        smul_comm (p : ZMod n) t', hpS, smul_zero, add_zero] at h1
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_right h1
  · obtain ⟨β', t', hβ'⟩ := hinv βb hβb β hrβ
    apply hSw (-(β' * α))
    have h1 : β' • (α • w + β • Sg e σ w) = 0 := by rw [hstar, smul_zero]
    rw [smul_add, smul_smul, smul_smul, hβ', add_smul, one_smul, mul_smul (p : ZMod n) t',
      smul_comm (p : ZMod n) t', hpS, smul_zero, add_zero] at h1
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_right h1

end Local

theorem exists_isUnit_d
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    ∃ v : ZMod n × ZMod n, IsUnit (d e σ v) := by
  classical

  have loc : ∀ p ∈ n.primeFactors, ∃ u : ZMod n × ZMod n, ∀ hpn : p ∣ n,
      ZMod.castHom hpn (ZMod p) (d e σ u) ≠ 0 := by
    intro p hp
    obtain ⟨u, hu⟩ := exists_cast_d_ne_zero e σ (Nat.dvd_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hp)
      (hns p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))
    exact ⟨u, fun _ => hu⟩
  choose! uu huu using loc

  have hs : ∀ i ∈ n.primeFactors, (id i) ≠ 0 := fun i hi => (Nat.prime_of_mem_primeFactors hi).ne_zero
  have pp : Set.Pairwise (n.primeFactors : Set ℕ) (Function.onFun Nat.Coprime id) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hi) (Nat.prime_of_mem_primeFactors hj)).2 hij
  obtain ⟨k₁, hk₁⟩ := Nat.chineseRemainderOfFinset (fun p => (uu p).1.val) id n.primeFactors hs pp
  obtain ⟨k₂, hk₂⟩ := Nat.chineseRemainderOfFinset (fun p => (uu p).2.val) id n.primeFactors hs pp
  refine ⟨((k₁ : ZMod n), (k₂ : ZMod n)), ?_⟩

  rw [← ZMod.natCast_zmod_val (d e σ _), ZMod.isUnit_iff_coprime]
  apply Nat.coprime_of_dvd
  intro p hp hpd hpn
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpn, NeZero.ne n⟩
  apply huu p hmem hpn

  have hred : rV hpn ((k₁ : ZMod n), (k₂ : ZMod n)) = rV hpn (uu p) := by
    rw [rV_apply, rV_apply]
    have e1 : ZMod.castHom hpn (ZMod p) (k₁ : ZMod n) = ZMod.castHom hpn (ZMod p) (uu p).1 := by
      rw [map_natCast, ← ZMod.natCast_zmod_val (uu p).1, map_natCast, ZMod.natCast_eq_natCast_iff]
      exact hk₁ p hmem
    have e2 : ZMod.castHom hpn (ZMod p) (k₂ : ZMod n) = ZMod.castHom hpn (ZMod p) (uu p).2 := by
      rw [map_natCast, ← ZMod.natCast_zmod_val (uu p).2, map_natCast, ZMod.natCast_eq_natCast_iff]
      exact hk₂ p hmem
    rw [e1, e2]
  rw [← cast_d_eq_of_rV_eq e σ hpn hred, ZMod.castHom_apply, ZMod.cast_eq_val,
    ZMod.natCast_eq_zero_iff]
  exact hpd

end P2MKcCB
p2m_reactivate "P2MW.S_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul.P2MKcCB"

theorem solution
    {A : Type*} [AddCommGroup A] (n : ℕ) [NeZero n]
    (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) (σ : A →+ A)
    (hns : ∀ p : ℕ, p.Prime → p ∣ n → ∃ a : A, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) :
    ∃ e' : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n,
      ((e' (0, 1) : Submodule.torsionBy ℤ A n) : A) =
        σ ((e' (1, 0) : Submodule.torsionBy ℤ A n) : A) := by
  obtain ⟨v, hv⟩ := P2MKcCB.exists_isUnit_d e σ hns
  exact P2MKcCB.exists_addEquiv_of_isUnit e σ v hv

end S_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul
end P2MW
export P2MW.S_AddCommGroup_exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul (solution)
