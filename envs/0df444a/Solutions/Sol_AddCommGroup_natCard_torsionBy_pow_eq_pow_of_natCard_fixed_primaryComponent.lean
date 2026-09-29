-- Prove2me | solution 1 for AddCommGroup.natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/83597874-0d14-5f62-9e7e-5b8b98a3a20b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace P2mTorsionGrowth

open AddSubgroup Function

section General

variable {A : Type*} [AddCommGroup A]

abbrev tor (A : Type*) [AddCommGroup A] (m : ℕ) : AddSubgroup A :=
  (nsmulAddMonoidHom m : A →+ A).ker

theorem mem_tor {m : ℕ} {x : A} : x ∈ tor A m ↔ m • x = 0 := by
  rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]

theorem tor_le_tor_mul (m m' : ℕ) : tor A m ≤ tor A (m' * m) := by
  intro x hx
  rw [mem_tor] at hx ⊢
  rw [mul_nsmul', hx, nsmul_zero]

theorem card_eq_card_range_mul_card_ker {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (f : B →+ C) : Nat.card B = Nat.card f.range * Nat.card f.ker := by
  rw [card_eq_card_quotient_mul_card_addSubgroup f.ker,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]

theorem finite_of_finite_range_ker {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    (f : B →+ C) [Finite f.range] [Finite f.ker] : Finite B := by
  apply Nat.finite_of_card_ne_zero
  rw [card_eq_card_range_mul_card_ker f]
  exact mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

theorem finite_of_le {H K : AddSubgroup A} (h : H ≤ K) [Finite K] : Finite H :=
  Finite.of_injective _ (AddSubgroup.inclusion_injective h)

theorem card_ker_mul_le {B : Type*} [AddCommGroup B] (f g : AddMonoid.End B)
    [Finite (f : B →+ B).ker] [Finite (g : B →+ B).ker] :
    Finite ((f * g : AddMonoid.End B) : B →+ B).ker ∧
      Nat.card ((f * g : AddMonoid.End B) : B →+ B).ker ≤
        Nat.card (f : B →+ B).ker * Nat.card (g : B →+ B).ker := by
  set K := ((f * g : AddMonoid.End B) : B →+ B).ker with hK

  let ψ : K →+ (f : B →+ B).ker :=
    ((g : B →+ B).comp K.subtype).codRestrict _ (fun x => by
      rw [AddMonoidHom.mem_ker]
      exact x.2)
  have hψ : ∀ x : K, ((ψ x : (f : B →+ B).ker) : B) = g x := fun x => rfl

  let ι : ψ.ker → (g : B →+ B).ker := fun x => ⟨(x.1 : B), by
    have hx := x.2
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddMonoidHom.mem_ker]
    have := congrArg (fun y : (f : B →+ B).ker => (y : B)) hx
    (simp [hψ] at this; exact this)⟩
  have hι : Function.Injective ι := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (g : B →+ B).ker => (z : B)) hxy
  haveI : Finite ψ.ker := Finite.of_injective ι hι
  haveI : Finite ψ.range := inferInstance
  refine ⟨finite_of_finite_range_ker ψ, ?_⟩
  rw [card_eq_card_range_mul_card_ker ψ]
  exact Nat.mul_le_mul (Nat.card_le_card_of_injective _ Subtype.val_injective)
    (Nat.card_le_card_of_injective ι hι)

end General

section Layers

variable {A : Type*} [AddCommGroup A] (ℓ : ℕ)

abbrev T (n : ℕ) : AddSubgroup A := tor A (ℓ ^ n)

theorem T_le_succ (n : ℕ) : T (A := A) ℓ n ≤ T ℓ (n + 1) := by
  rw [T, T, pow_succ']
  exact tor_le_tor_mul _ _

theorem T_mono {n m : ℕ} (h : n ≤ m) : T (A := A) ℓ n ≤ T ℓ m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [T, T, add_comm, pow_add]
  exact tor_le_tor_mul _ _

theorem T_zero : T (A := A) ℓ 0 = ⊥ := by
  ext x
  rw [mem_tor, pow_zero, one_nsmul, mem_bot]

def layMap (n : ℕ) : T (A := A) ℓ (n + 1) →+ A :=
  (nsmulAddMonoidHom (ℓ ^ n)).comp (T ℓ (n + 1)).subtype

@[scoped simp] theorem layMap_apply (n : ℕ) (x : T (A := A) ℓ (n + 1)) :
    layMap ℓ n x = ℓ ^ n • (x : A) := rfl

def I (n : ℕ) : AddSubgroup A := (layMap (A := A) ℓ n).range

theorem mem_I {n : ℕ} {x : A} :
    x ∈ I ℓ n ↔ ∃ y : A, ℓ ^ (n + 1) • y = 0 ∧ ℓ ^ n • y = x := by
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    exact ⟨y, (mem_tor.mp hy), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, mem_tor.mpr hy⟩, rfl⟩

theorem I_le_T_one (n : ℕ) : I (A := A) ℓ n ≤ T ℓ 1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_I ℓ).mp hx
  rw [mem_tor, pow_one, ← mul_nsmul', ← pow_succ', hy]

theorem I_succ_le (n : ℕ) : I (A := A) ℓ (n + 1) ≤ I ℓ n := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_I ℓ).mp hx
  refine (mem_I ℓ).mpr ⟨ℓ • y, ?_, ?_⟩
  · rw [← mul_nsmul', ← pow_succ, hy]
  · rw [← mul_nsmul', ← pow_succ]

theorem I_antitone : Antitone (I (A := A) ℓ) := antitone_nat_of_succ_le (I_succ_le ℓ)

theorem ker_layMap (n : ℕ) :
    (layMap (A := A) ℓ n).ker = (T ℓ n).addSubgroupOf (T ℓ (n + 1)) := by
  ext x
  rw [AddMonoidHom.mem_ker, mem_addSubgroupOf, layMap_apply, mem_tor]

theorem card_T_succ (n : ℕ) :
    Nat.card (T (A := A) ℓ (n + 1)) = Nat.card (I (A := A) ℓ n) * Nat.card (T (A := A) ℓ n) := by
  rw [card_eq_card_range_mul_card_ker (layMap ℓ n), ker_layMap,
    Nat.card_congr (addSubgroupOfEquivOfLe (T_le_succ ℓ n)).toEquiv]
  rfl

variable [hℓ : Fact ℓ.Prime]

theorem finite_T [Finite (tor A ℓ)] (n : ℕ) : Finite (T (A := A) ℓ n) := by
  induction n with
  | zero =>
    rw [T_zero]
    infer_instance
  | succ n ih =>
    haveI : Finite (T (A := A) ℓ 1) := by
      rw [T, pow_one]
      infer_instance
    haveI : Finite (layMap (A := A) ℓ n).range := finite_of_le (I_le_T_one ℓ n)
    haveI : Finite (layMap (A := A) ℓ n).ker := by
      rw [ker_layMap]
      exact Finite.of_equiv _ (addSubgroupOfEquivOfLe (T_le_succ ℓ n)).toEquiv.symm
    exact finite_of_finite_range_ker (layMap ℓ n)

theorem finite_I [Finite (tor A ℓ)] (n : ℕ) : Finite (I (A := A) ℓ n) := by
  haveI : Finite (T (A := A) ℓ 1) := finite_T ℓ 1
  exact finite_of_le (I_le_T_one ℓ n)

theorem card_I_le [Finite (tor A ℓ)] (n : ℕ) : Nat.card (I (A := A) ℓ n) ≤ Nat.card (tor A ℓ) := by
  have h := I_le_T_one (A := A) ℓ n
  rw [T, pow_one] at h
  exact card_le_of_le h

theorem exists_stable [Finite (tor A ℓ)] :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → I (A := A) ℓ n = I ℓ n₀ := by
  classical
  let e : ℕ → ℕ := fun n => Nat.card (I (A := A) ℓ n)
  have hanti : Antitone e := by
    apply antitone_nat_of_succ_le
    intro n
    haveI := finite_I (A := A) ℓ n
    exact card_le_of_le (I_succ_le ℓ n)
  let n₀ := Function.argmin e
  refine ⟨n₀, fun n hn => ?_⟩
  haveI := finite_I (A := A) ℓ n₀
  exact eq_of_le_of_card_ge (I_antitone ℓ hn) (by
    show e n₀ ≤ e n
    exact Function.argmin_le e n)

end Layers

section Divisible

variable {H : Type*} [AddCommGroup H] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

abbrev eker (f : AddMonoid.End H) : AddSubgroup H := (f : H →+ H).ker

theorem mem_eker {f : AddMonoid.End H} {x : H} : x ∈ eker f ↔ f x = 0 := AddMonoidHom.mem_ker

private theorem _root_.P2mTorsionGrowth.natCast_apply (n : ℕ) (x : H) : (n : AddMonoid.End H) x = n • x :=
  AddMonoid.End.natCast_apply n x

p2m_export "P2mTorsionGrowth" "natCast_apply"

theorem bijective_one_add (hprim : ∀ x : H, ∃ m : ℕ, ℓ ^ m • x = 0) (N : AddMonoid.End H) :
    Function.Bijective (1 + (ℓ : AddMonoid.End H) * N : AddMonoid.End H) := by
  set N' : AddMonoid.End H := -((ℓ : AddMonoid.End H) * N) with hN'
  have hv : (1 + (ℓ : AddMonoid.End H) * N : AddMonoid.End H) = 1 - N' := by
    rw [hN', sub_neg_eq_add]

  have hpow : ∀ (m : ℕ), N' ^ m = (-1) ^ m * N ^ m * ((ℓ ^ m : ℕ) : AddMonoid.End H) := by
    intro m
    have hc : Commute ((ℓ : AddMonoid.End H)) N := Nat.cast_commute ℓ N
    rw [hN', neg_pow, hc.mul_pow, Nat.cast_pow, mul_assoc]
    congr 1
    exact (hc.pow_pow m m).eq
  have hkill : ∀ x : H, ∃ m : ℕ, ∀ m', m ≤ m' → (N' ^ m') x = 0 := by
    intro x
    obtain ⟨m, hm⟩ := hprim x
    refine ⟨m, fun m' hm' => ?_⟩
    have hx : ((ℓ ^ m' : ℕ) : AddMonoid.End H) x = 0 := by
      rw [natCast_apply]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm'
      rw [pow_add, mul_comm, mul_nsmul', hm, nsmul_zero]
    rw [hpow m']
    show ((-1) ^ m' * N ^ m') (((ℓ ^ m' : ℕ) : AddMonoid.End H) x) = 0
    rw [hx, map_zero]
  rw [hv]
  constructor
  ·
    intro x y hxy
    have h0 : (1 - N') (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1 : N' (x - y) = x - y := by
      have : (1 - N') (x - y) = (x - y) - N' (x - y) := rfl
      rw [this, sub_eq_zero] at h0
      exact h0.symm
    have h2 : ∀ m : ℕ, (N' ^ m) (x - y) = x - y := by
      intro m
      rw [AddMonoid.End.coe_pow]
      exact Function.iterate_fixed h1 m
    obtain ⟨m, hm⟩ := hkill (x - y)
    have := hm m le_rfl
    rw [h2 m] at this
    exact sub_eq_zero.mp this
  ·
    intro y
    obtain ⟨m, hm⟩ := hkill y
    refine ⟨(∑ i ∈ Finset.range m, N' ^ i) y, ?_⟩
    show ((1 - N') * ∑ i ∈ Finset.range m, N' ^ i) y = y
    rw [mul_neg_geom_sum]
    show y - (N' ^ m) y = y
    rw [hm m le_rfl, sub_zero]

theorem surjective_nsmul_sq (hdiv : ∀ x : H, ∃ y : H, ℓ • y = x) :
    Function.Surjective (nsmulAddMonoidHom (ℓ ^ 2) : H →+ H) := by
  intro x
  obtain ⟨y, rfl⟩ := hdiv x
  obtain ⟨z, rfl⟩ := hdiv y
  exact ⟨z, by rw [nsmulAddMonoidHom_apply, pow_two, mul_nsmul']⟩

theorem exists_sub_one_eq (hdiv : ∀ x : H, ∃ y : H, ℓ • y = x)
    (θ : AddMonoid.End H) (hθ : ∀ x : H, ℓ ^ 2 • x = 0 → θ x = x) :
    ∃ M : AddMonoid.End H, θ - 1 = ((ℓ ^ 2 : ℕ) : AddMonoid.End H) * M := by
  set s : H →+ H := nsmulAddMonoidHom (ℓ ^ 2) with hs
  have hsurj : Function.Surjective s := surjective_nsmul_sq ℓ hdiv
  have hker : s.ker ≤ ((θ - 1 : AddMonoid.End H) : H →+ H).ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker, hs, nsmulAddMonoidHom_apply] at hx
    rw [AddMonoidHom.mem_ker]
    show θ x - x = 0
    rw [hθ x hx, sub_self]
  let M : AddMonoid.End H :=
    s.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
      ⟨((θ - 1 : AddMonoid.End H) : H →+ H), hker⟩
  have hM : ∀ y : H, M (s y) = (θ - 1) y := fun y =>
    s.liftOfRightInverse_comp_apply (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
      ⟨((θ - 1 : AddMonoid.End H) : H →+ H), hker⟩ y
  refine ⟨M, ?_⟩
  apply AddMonoidHom.ext
  intro y
  have hcomm : (((ℓ ^ 2 : ℕ) : AddMonoid.End H) * M) y = M (s y) := by
    show ((ℓ ^ 2 : ℕ) : AddMonoid.End H) (M y) = M (s y)
    rw [natCast_apply, hs, nsmulAddMonoidHom_apply, map_nsmul]
  exact (hM y).symm.trans hcomm.symm

theorem geom_sum_one_add {R : Type*} [Ring R] (a : R) (n : ℕ) :
    ∃ G : R, ∑ i ∈ Finset.range n, (1 + a) ^ i = n + G * a := by
  refine ⟨∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, (1 + a) ^ j, ?_⟩
  rw [Finset.sum_mul]
  have : ∀ i ∈ Finset.range n, (1 + a) ^ i = 1 + (∑ j ∈ Finset.range i, (1 + a) ^ j) * a := by
    intro i _
    have h := geom_sum_mul (1 + a) i
    rw [add_sub_cancel_left] at h
    rw [h, add_sub_cancel]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]

theorem card_ker_geom_sum (hprim : ∀ x : H, ∃ m : ℕ, ℓ ^ m • x = 0)
    (hdiv : ∀ x : H, ∃ y : H, ℓ • y = x) [Finite (tor H ℓ)] (θ : AddMonoid.End H)
    (hθ : ∀ x : H, ℓ ^ 2 • x = 0 → θ x = x) :
    Finite (eker (∑ i ∈ Finset.range ℓ, θ ^ i)) ∧
      Nat.card (eker (∑ i ∈ Finset.range ℓ, θ ^ i)) = Nat.card (tor H ℓ) := by
  obtain ⟨M, hM⟩ := exists_sub_one_eq ℓ hdiv θ hθ
  have hθ' : θ = 1 + ((ℓ ^ 2 : ℕ) : AddMonoid.End H) * M := by rw [← hM, add_sub_cancel]
  obtain ⟨G, hG⟩ := geom_sum_one_add (((ℓ ^ 2 : ℕ) : AddMonoid.End H) * M) ℓ

  set N : AddMonoid.End H := G * M with hN
  set v : AddMonoid.End H := 1 + (ℓ : AddMonoid.End H) * N with hv
  have hu : (∑ i ∈ Finset.range ℓ, θ ^ i) = (ℓ : AddMonoid.End H) * v := by
    rw [hθ', hG, hv, hN, mul_add, mul_one, Nat.cast_pow, pow_two]
    have hc : ∀ z : AddMonoid.End H, Commute (ℓ : AddMonoid.End H) z := Nat.cast_commute ℓ
    rw [(hc G).left_comm M, (hc G).left_comm ((ℓ : AddMonoid.End H) * M)]
    simp only [mul_assoc]
  have hbij : Function.Bijective v := bijective_one_add ℓ hprim N

  let E : eker (∑ i ∈ Finset.range ℓ, θ ^ i) ≃ tor H ℓ :=
    (Equiv.ofBijective v hbij).subtypeEquiv (fun x => by
      rw [mem_eker, mem_tor, hu, Equiv.ofBijective_apply]
      show (ℓ : AddMonoid.End H) (v x) = 0 ↔ _
      rw [natCast_apply])
  exact ⟨Finite.of_equiv _ E.symm, Nat.card_congr E⟩

theorem card_fix_pow_le (hprim : ∀ x : H, ∃ m : ℕ, ℓ ^ m • x = 0)
    (hdiv : ∀ x : H, ∃ y : H, ℓ • y = x) [Finite (tor H ℓ)] (θ : AddMonoid.End H)
    (hθ : ∀ x : H, ℓ ^ 2 • x = 0 → θ x = x) [Finite (eker (θ - 1))] (k : ℕ) :
    Finite (eker (θ ^ ℓ ^ k - 1)) ∧
      Nat.card (eker (θ ^ ℓ ^ k - 1)) ≤ Nat.card (eker (θ - 1)) * Nat.card (tor H ℓ) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_one, pow_zero, mul_one]
    exact ⟨inferInstance, le_rfl⟩
  | succ k ih =>
    obtain ⟨ihf, ihc⟩ := ih

    set θ' : AddMonoid.End H := θ ^ ℓ ^ k with hθ'def
    have hθ' : ∀ x : H, ℓ ^ 2 • x = 0 → θ' x = x := by
      intro x hx
      rw [hθ'def, AddMonoid.End.coe_pow]
      exact Function.iterate_fixed (hθ x hx) _
    have hfac : θ ^ ℓ ^ (k + 1) - 1 = (∑ i ∈ Finset.range ℓ, θ' ^ i) * (θ' - 1) := by
      rw [geom_sum_mul, hθ'def, ← pow_mul, ← pow_succ]
    obtain ⟨hf1, hc1⟩ := card_ker_geom_sum ℓ hprim hdiv θ' hθ'
    haveI : Finite (eker (∑ i ∈ Finset.range ℓ, θ' ^ i)) := hf1
    haveI : Finite (eker (θ' - 1)) := ihf
    obtain ⟨hf2, hc2⟩ := card_ker_mul_le (∑ i ∈ Finset.range ℓ, θ' ^ i) (θ' - 1)
    rw [hfac]
    refine ⟨hf2, hc2.trans ?_⟩
    rw [hc1, pow_succ]
    calc Nat.card (tor H ℓ) * Nat.card (eker (θ' - 1))
        ≤ Nat.card (tor H ℓ) * (Nat.card (eker (θ - 1)) * Nat.card (tor H ℓ) ^ k) :=
          Nat.mul_le_mul_left _ ihc
      _ = Nat.card (eker (θ - 1)) * (Nat.card (tor H ℓ) ^ k * Nat.card (tor H ℓ)) := by ring

end Divisible

theorem le_of_forall_mul_pow_le {a b C D : ℕ} (hD : 0 < D) (h : ∀ k : ℕ, D * a ^ k ≤ C * b ^ k) :
    a ≤ b := by
  by_contra hab
  rw [not_le] at hab
  rcases Nat.eq_zero_or_pos b with hb | hb
  · have := h 1
    rw [hb, pow_one, pow_one, mul_zero] at this
    have ha : 0 < a := by omega
    have : 0 < D * a := Nat.mul_pos hD ha
    omega
  ·
    have key : ∀ k : ℕ, b ^ k * (b + k) ≤ b * (b + 1) ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc b ^ (k + 1) * (b + (k + 1))
            = b * (b ^ k * (b + k)) + b ^ k * b := by ring
          _ ≤ b * (b ^ k * (b + k)) + b ^ k * (b + k) := by
              apply Nat.add_le_add_left
              exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
          _ = (b ^ k * (b + k)) * (b + 1) := by ring
          _ ≤ (b * (b + 1) ^ k) * (b + 1) := Nat.mul_le_mul_right _ ih
          _ = b * (b + 1) ^ (k + 1) := by ring
    have hab' : ∀ k : ℕ, (b + 1) ^ k ≤ a ^ k := fun k => Nat.pow_le_pow_left hab k

    set k := b * C with hk
    have h1 : b ^ k * (b + k) ≤ b * a ^ k := (key k).trans (Nat.mul_le_mul_left _ (hab' k))
    have h2 : b * (D * a ^ k) ≤ b * (C * b ^ k) := Nat.mul_le_mul_left _ (h k)
    have h3 : b * a ^ k ≤ b * (D * a ^ k) := by
      apply Nat.mul_le_mul_left
      exact Nat.le_mul_of_pos_left _ hD
    have h4 : b ^ k * (b + k) ≤ b * (C * b ^ k) := h1.trans (h3.trans h2)
    have h5 : b * (C * b ^ k) = b ^ k * k := by rw [hk]; ring
    rw [h5] at h4
    have h6 : b + k ≤ k := Nat.le_of_mul_le_mul_left h4 (by positivity)
    omega

end P2mTorsionGrowth
p2m_reactivate "P2MW.S_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent.P2mTorsionGrowth"

namespace P2mTorsionGrowth

open AddSubgroup Function

section Assembly

variable {A : Type*} [AddCommGroup A] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

abbrev Pr : AddSubgroup A := AddCommGroup.primaryComponent A ℓ

def Hs (n₀ : ℕ) : AddSubgroup A := (Pr (A := A) ℓ).map (nsmulAddMonoidHom (ℓ ^ n₀))

theorem mem_Pr {x : A} : x ∈ Pr (A := A) ℓ ↔ ∃ m : ℕ, ℓ ^ m • x = 0 :=
  AddCommGroup.mem_primaryComponent

theorem mem_Hs {n₀ : ℕ} {x : A} :
    x ∈ Hs (A := A) ℓ n₀ ↔ ∃ y : A, y ∈ Pr (A := A) ℓ ∧ ℓ ^ n₀ • y = x := by
  rw [Hs, mem_map]
  simp only [nsmulAddMonoidHom_apply]

theorem Hs_le_Pr (n₀ : ℕ) : Hs (A := A) ℓ n₀ ≤ Pr ℓ := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_Hs ℓ).mp hx
  exact AddSubgroup.nsmul_mem _ hy _

theorem map_mem_Pr (σ : A →+ A) {x : A} (hx : x ∈ Pr (A := A) ℓ) : σ x ∈ Pr (A := A) ℓ := by
  obtain ⟨m, hm⟩ := (mem_Pr ℓ).mp hx
  exact (mem_Pr ℓ).mpr ⟨m, by rw [← map_nsmul, hm, map_zero]⟩

theorem map_mem_Hs (σ : A →+ A) {n₀ : ℕ} {x : A} (hx : x ∈ Hs (A := A) ℓ n₀) :
    σ x ∈ Hs (A := A) ℓ n₀ := by
  obtain ⟨y, hy, rfl⟩ := (mem_Hs ℓ).mp hx
  exact (mem_Hs ℓ).mpr ⟨σ y, map_mem_Pr ℓ σ hy, by rw [map_nsmul]⟩

def res (n₀ : ℕ) (σ : AddMonoid.End A) : AddMonoid.End (Hs (A := A) ℓ n₀) :=
  ((σ : A →+ A).comp (Hs (A := A) ℓ n₀).subtype).codRestrict _ (fun x => map_mem_Hs ℓ σ x.2)

@[scoped simp] theorem coe_res (n₀ : ℕ) (σ : AddMonoid.End A) (x : Hs (A := A) ℓ n₀) :
    ((res ℓ n₀ σ x : Hs (A := A) ℓ n₀) : A) = σ x := rfl

theorem res_one (n₀ : ℕ) : res (A := A) ℓ n₀ 1 = 1 := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

theorem res_mul (n₀ : ℕ) (σ σ' : AddMonoid.End A) :
    res (A := A) ℓ n₀ (σ * σ') = res ℓ n₀ σ * res ℓ n₀ σ' := by
  apply AddMonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

theorem res_pow (n₀ : ℕ) (σ : AddMonoid.End A) (j : ℕ) :
    res (A := A) ℓ n₀ (σ ^ j) = res ℓ n₀ σ ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero, res_one]
  | succ j ih => rw [pow_succ, pow_succ, res_mul, ih]

theorem coe_res_pow (n₀ : ℕ) (σ : AddMonoid.End A) (j : ℕ) (x : Hs (A := A) ℓ n₀) :
    (((res ℓ n₀ σ ^ j) x : Hs (A := A) ℓ n₀) : A) = (σ ^ j) x := by
  rw [← res_pow, coe_res]

variable [Finite (tor A ℓ)]

theorem Hs_props {n₀ : ℕ} (hn₀ : ∀ n, n₀ ≤ n → I (A := A) ℓ n = I ℓ n₀) :

    (∀ x ∈ Hs (A := A) ℓ n₀, ∃ y ∈ Hs (A := A) ℓ n₀, ℓ • y = x) ∧

    Hs (A := A) ℓ n₀ ⊓ tor A ℓ = I ℓ n₀ := by

  have H1 : ∀ x ∈ Hs (A := A) ℓ n₀, ℓ • x = 0 → ∀ t : ℕ,
      ∃ w : A, ℓ ^ (n₀ + t + 1) • w = 0 ∧ ℓ ^ (n₀ + t) • w = x := by
    intro x hx hlx t
    obtain ⟨y, hy, rfl⟩ := (mem_Hs ℓ).mp hx
    have hxI : ℓ ^ n₀ • y ∈ I (A := A) ℓ n₀ := by
      refine (mem_I ℓ).mpr ⟨y, ?_, rfl⟩
      rw [pow_succ', mul_nsmul', hlx]
    rw [← hn₀ (n₀ + t) (Nat.le_add_right _ _)] at hxI
    exact (mem_I ℓ).mp hxI
  have H3 : Hs (A := A) ℓ n₀ ⊓ tor A ℓ = I ℓ n₀ := by
    apply le_antisymm
    · rintro x ⟨hx, hlx⟩
      obtain ⟨w, hw, hwx⟩ := H1 x hx (mem_tor.mp hlx) 0
      exact (mem_I ℓ).mpr ⟨w, hw, hwx⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := (mem_I ℓ).mp hx
      refine ⟨(mem_Hs ℓ).mpr ⟨y, (mem_Pr ℓ).mpr ⟨n₀ + 1, hy⟩, rfl⟩, ?_⟩
      have := I_le_T_one (A := A) ℓ n₀ hx
      rwa [T, pow_one] at this
  refine ⟨?_, H3⟩

  have key : ∀ m : ℕ, ∀ x ∈ Hs (A := A) ℓ n₀, ℓ ^ m • x = 0 →
      ∃ y ∈ Hs (A := A) ℓ n₀, ℓ • y = x := by
    intro m
    induction m with
    | zero =>
      intro x _ hx
      rw [pow_zero, one_nsmul] at hx
      exact ⟨0, zero_mem _, by rw [hx, nsmul_zero]⟩
    | succ m ih =>
      intro x hx hmx
      have hg : ℓ ^ m • x ∈ Hs (A := A) ℓ n₀ := AddSubgroup.nsmul_mem _ hx _
      have hlg : ℓ • (ℓ ^ m • x) = 0 := by rw [← mul_nsmul', ← pow_succ', hmx]
      obtain ⟨w, hw0, hw⟩ := H1 _ hg hlg (m + 1)
      set z : A := ℓ ^ n₀ • w with hz
      have hzH : z ∈ Hs (A := A) ℓ n₀ :=
        (mem_Hs ℓ).mpr ⟨w, (mem_Pr ℓ).mpr ⟨n₀ + (m + 1) + 1, hw0⟩, rfl⟩
      have hz' : ℓ ^ (m + 1) • z = ℓ ^ m • x := by
        rw [hz, ← mul_nsmul', ← pow_add, add_comm, hw]
      have hdiff : ℓ ^ m • (x - ℓ • z) = 0 := by
        rw [nsmul_sub, ← mul_nsmul', ← pow_succ, hz', sub_self]
      obtain ⟨y', hy', hy'eq⟩ := ih (x - ℓ • z) (sub_mem hx (AddSubgroup.nsmul_mem _ hzH _)) hdiff
      refine ⟨y' + z, add_mem hy' hzH, ?_⟩
      rw [nsmul_add, hy'eq, sub_add_cancel]
  intro x hx
  obtain ⟨m, hm⟩ := (mem_Pr ℓ).mp (Hs_le_Pr ℓ n₀ hx)
  exact key m x hx hm

theorem finite_quotient {n₀ : ℕ} (hn₀ : ∀ n, n₀ ≤ n → I (A := A) ℓ n = I ℓ n₀) :
    Finite (Pr (A := A) ℓ ⧸ (Hs (A := A) ℓ n₀).addSubgroupOf (Pr (A := A) ℓ)) := by
  set Q := Pr (A := A) ℓ ⧸ (Hs (A := A) ℓ n₀).addSubgroupOf (Pr (A := A) ℓ) with hQ
  obtain ⟨H2, -⟩ := Hs_props ℓ hn₀

  have hkill : ∀ q : Q, ℓ ^ n₀ • q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H p =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, mem_addSubgroupOf]
      exact (mem_Hs ℓ).mpr ⟨p, p.2, rfl⟩

  set L : AddSubgroup (Pr (A := A) ℓ) := (tor A ℓ).addSubgroupOf (Pr (A := A) ℓ) with hL
  haveI : Finite L := Finite.of_injective (fun x : L => (⟨x.1.1, x.2⟩ : tor A ℓ)) (by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : tor A ℓ => (z : A)) hxy)
  set L' : AddSubgroup Q := L.map (QuotientAddGroup.mk' _) with hL'
  haveI : Finite L' := Finite.of_surjective (fun x : L => (⟨QuotientAddGroup.mk' _ x.1,
      mem_map_of_mem _ x.2⟩ : L')) (by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩)
  have htor : tor Q ℓ ≤ L' := by
    intro q hq
    induction q using QuotientAddGroup.induction_on with
    | H p =>
      rw [mem_tor, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff,
        mem_addSubgroupOf, AddSubgroup.coe_nsmul] at hq

      obtain ⟨h, hh, hhp⟩ := H2 _ hq
      have hhP : h ∈ Pr (A := A) ℓ := Hs_le_Pr ℓ n₀ hh
      have hmem : p - ⟨h, hhP⟩ ∈ L := by
        rw [hL, mem_addSubgroupOf, mem_tor, AddSubgroup.coe_sub, nsmul_sub]
        show ℓ • (p : A) - ℓ • h = 0
        rw [hhp, sub_self]
      have hcls : (QuotientAddGroup.mk' ((Hs (A := A) ℓ n₀).addSubgroupOf (Pr ℓ)) ⟨h, hhP⟩ : Q) = 0 := by
        rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, mem_addSubgroupOf]
        exact hh
      rw [hL', mem_map]
      refine ⟨p - ⟨h, hhP⟩, hmem, ?_⟩
      rw [map_sub, hcls, sub_zero]
      rfl
  haveI : Finite (tor Q ℓ) := finite_of_le htor
  haveI : Finite (T (A := Q) ℓ n₀) := finite_T ℓ n₀
  have htop : T (A := Q) ℓ n₀ = ⊤ := by
    ext q
    simp only [mem_top, iff_true]
    exact mem_tor.mpr (hkill q)
  rw [htop] at this
  exact Finite.of_equiv _ (AddSubgroup.topEquiv : (⊤ : AddSubgroup Q) ≃+ Q).toEquiv

end Assembly
p2m_reactivate "P2MW.S_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent.P2mTorsionGrowth"

end P2mTorsionGrowth
p2m_reactivate "P2MW.S_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent.P2mTorsionGrowth"

namespace P2mTorsionGrowth

open AddSubgroup Function

section Main

variable {A : Type*} [AddCommGroup A] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem main [Finite (tor A ℓ)] (r : ℕ) (τ : A →+ A)
    (hle : Nat.card (tor A ℓ) ≤ ℓ ^ r)
    (hτ : ∀ x : A, ℓ ^ 2 • x = 0 → τ x = x)
    (c k₀ : ℕ) (hfix : ∀ k : ℕ,
      Nat.card {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ (k₀ + k)] x = x} =
        ℓ ^ (r * k + c)) (n : ℕ) :
    Nat.card (T (A := A) ℓ n) = ℓ ^ (r * n) := by
  obtain ⟨n₀, hn₀⟩ := exists_stable (A := A) ℓ

  suffices hsuff : ℓ ^ r ≤ Nat.card (I (A := A) ℓ n₀) by
    have hI : ∀ j, Nat.card (I (A := A) ℓ j) = ℓ ^ r := by
      intro j
      apply le_antisymm ((card_I_le ℓ j).trans hle)
      rcases le_total j n₀ with h | h
      · haveI := finite_I (A := A) ℓ j
        exact hsuff.trans (card_le_of_le (I_antitone ℓ h))
      · rw [hn₀ j h]; exact hsuff
    induction n with
    | zero => rw [T_zero, card_bot, mul_zero, pow_zero]
    | succ n ih => rw [card_T_succ, hI, ih, ← pow_add]; congr 1; ring

  obtain ⟨H2, H3⟩ := Hs_props ℓ hn₀
  haveI hQfin := finite_quotient ℓ hn₀
  haveI : Finite (I (A := A) ℓ n₀) := finite_I ℓ n₀
  have hprimH : ∀ x : Hs (A := A) ℓ n₀, ∃ m : ℕ, ℓ ^ m • x = 0 := by
    intro x
    obtain ⟨m, hm⟩ := (mem_Pr ℓ).mp (Hs_le_Pr ℓ n₀ x.2)
    exact ⟨m, Subtype.ext (by rw [AddSubgroup.coe_nsmul, hm, AddSubgroup.coe_zero])⟩
  have hdivH : ∀ x : Hs (A := A) ℓ n₀, ∃ y : Hs (A := A) ℓ n₀, ℓ • y = x := by
    intro x
    obtain ⟨y, hy, hyx⟩ := H2 x x.2
    exact ⟨⟨y, hy⟩, Subtype.ext (by rw [AddSubgroup.coe_nsmul]; exact hyx)⟩

  let EH : tor (Hs (A := A) ℓ n₀) ℓ ≃ I (A := A) ℓ n₀ :=
    { toFun := fun x => ⟨(x.1 : A), by
        have hx : ((x.1 : A)) ∈ Hs (A := A) ℓ n₀ ⊓ tor A ℓ := by
          refine ⟨x.1.2, mem_tor.mpr ?_⟩
          have := congrArg Subtype.val (mem_tor.mp x.2)
          rwa [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero] at this
        rwa [H3] at hx⟩
      invFun := fun y =>
        have hy : (y : A) ∈ Hs (A := A) ℓ n₀ ⊓ tor A ℓ := by rw [H3]; exact y.2
        ⟨⟨y, hy.1⟩, mem_tor.mpr (Subtype.ext (by
          rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]; exact mem_tor.mp hy.2))⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl }
  haveI : Finite (tor (Hs (A := A) ℓ n₀) ℓ) := Finite.of_equiv _ EH.symm
  have hcardH : Nat.card (tor (Hs (A := A) ℓ n₀) ℓ) = Nat.card (I (A := A) ℓ n₀) :=
    Nat.card_congr EH

  obtain ⟨τe, hτe⟩ : ∃ τe : AddMonoid.End A, ⇑τe = ⇑τ := ⟨τ, rfl⟩
  set θ : AddMonoid.End (Hs (A := A) ℓ n₀) := res ℓ n₀ (τe ^ ℓ ^ k₀) with hθdef
  have hθcoe : ∀ x : Hs (A := A) ℓ n₀, ((θ x : Hs (A := A) ℓ n₀) : A) = (⇑τ)^[ℓ ^ k₀] x := by
    intro x
    rw [hθdef, coe_res, AddMonoid.End.coe_pow, hτe]
  have hθ : ∀ x : Hs (A := A) ℓ n₀, ℓ ^ 2 • x = 0 → θ x = x := by
    intro x hx
    apply Subtype.ext
    rw [hθcoe]
    apply Function.iterate_fixed
    apply hτ
    have := congrArg Subtype.val hx
    rwa [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero] at this

  haveI hfin0 : Finite (eker (θ - 1)) := by
    have hcard := hfix 0
    rw [add_zero] at hcard
    haveI : Finite {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k₀] x = x} := by
      apply Nat.finite_of_card_ne_zero
      rw [hcard]
      exact pow_ne_zero _ hℓ.out.ne_zero
    refine Finite.of_injective (fun y : eker (θ - 1) =>
      (⟨(y.1 : A), Hs_le_Pr ℓ n₀ y.1.2, ?_⟩ :
        {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ k₀] x = x})) ?_
    · have hy := y.2
      rw [mem_eker] at hy
      have hy' : θ y.1 = y.1 := by
        have : (θ - 1) y.1 = θ y.1 - y.1 := rfl
        rw [this, sub_eq_zero] at hy
        exact hy
      have := congrArg Subtype.val hy'
      rw [hθcoe] at this
      exact this
    · intro y y' hyy'
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val hyy'
      exact this

  have hineq : ∀ k : ℕ,
      ℓ ^ c * (ℓ ^ r) ^ k ≤
        (Nat.card (Pr (A := A) ℓ ⧸ (Hs (A := A) ℓ n₀).addSubgroupOf (Pr (A := A) ℓ)) *
          Nat.card (eker (θ - 1))) * Nat.card (I (A := A) ℓ n₀) ^ k := by
    intro k

    have hcard := hfix k
    have hexp : ℓ ^ (r * k + c) = ℓ ^ c * (ℓ ^ r) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [← hexp, ← hcard]

    obtain ⟨σ, hσ⟩ : ∃ σ : AddMonoid.End A, σ = τe ^ ℓ ^ (k₀ + k) := ⟨_, rfl⟩
    have hσcoe : ⇑σ = (⇑τ)^[ℓ ^ (k₀ + k)] := by rw [hσ, AddMonoid.End.coe_pow, hτe]
    have hσres : res ℓ n₀ σ = θ ^ ℓ ^ k := by
      rw [hσ, hθdef, ← res_pow, ← pow_mul, ← pow_add]
    obtain ⟨F, hF⟩ : ∃ F : AddSubgroup A, F = Pr (A := A) ℓ ⊓ eker (σ - 1) := ⟨_, rfl⟩
    have hFle : F ≤ Pr (A := A) ℓ := hF.le.trans inf_le_left
    have hFfix : ∀ x ∈ F, σ x = x := by
      intro x hx
      have hx' : x ∈ eker (σ - 1) := (hF.le hx).2
      rw [mem_eker] at hx'
      have h2 : (σ - 1) x = σ x - x := rfl
      rwa [h2, sub_eq_zero] at hx'
    have hcardF : Nat.card {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧
        (⇑τ)^[ℓ ^ (k₀ + k)] x = x} = Nat.card F := by
      refine Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
      rw [hF, mem_inf, mem_eker, ← hσcoe]
      show _ ↔ _ ∧ σ x - x = 0
      rw [sub_eq_zero]
    rw [hcardF]

    let ψ : F →+ Pr (A := A) ℓ ⧸ (Hs (A := A) ℓ n₀).addSubgroupOf (Pr (A := A) ℓ) :=
      (QuotientAddGroup.mk' _).comp (AddSubgroup.inclusion hFle)

    obtain ⟨hfk, hck⟩ := card_fix_pow_le ℓ hprimH hdivH θ hθ k
    haveI := hfk
    have hkerψ : ∀ x : ψ.ker, ((x.1 : F) : A) ∈ Hs (A := A) ℓ n₀ := by
      intro x
      have hx := x.2
      rw [AddMonoidHom.mem_ker] at hx
      change (QuotientAddGroup.mk' _ (AddSubgroup.inclusion _ x.1)) = 0 at hx
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, mem_addSubgroupOf] at hx
      exact hx
    let ι : ψ.ker → eker (θ ^ ℓ ^ k - 1) := fun x =>
      ⟨⟨((x.1 : F) : A), hkerψ x⟩, by
        rw [mem_eker]
        show (θ ^ ℓ ^ k) _ - _ = 0
        rw [sub_eq_zero]
        apply Subtype.ext
        rw [← hσres, coe_res]
        exact hFfix _ (x.1 : F).2⟩
    have hι : Function.Injective ι := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : eker (θ ^ ℓ ^ k - 1) => ((z : Hs (A := A) ℓ n₀) : A)) hxy
    haveI : Finite ψ.ker := Finite.of_injective ι hι
    rw [card_eq_card_range_mul_card_ker ψ]
    calc Nat.card ψ.range * Nat.card ψ.ker
        ≤ Nat.card (Pr (A := A) ℓ ⧸ (Hs (A := A) ℓ n₀).addSubgroupOf (Pr (A := A) ℓ)) *
            Nat.card (eker (θ ^ ℓ ^ k - 1)) :=
          Nat.mul_le_mul (Nat.card_le_card_of_injective _ Subtype.val_injective)
            (Nat.card_le_card_of_injective ι hι)
      _ ≤ Nat.card (Pr (A := A) ℓ ⧸ (Hs (A := A) ℓ n₀).addSubgroupOf (Pr (A := A) ℓ)) *
            (Nat.card (eker (θ - 1)) * Nat.card (tor (Hs (A := A) ℓ n₀) ℓ) ^ k) :=
          Nat.mul_le_mul_left _ hck
      _ = _ := by rw [hcardH, mul_assoc]

  exact le_of_forall_mul_pow_le (pow_pos hℓ.out.pos _) hineq

end Main
p2m_reactivate "P2MW.S_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent.P2mTorsionGrowth"

end P2mTorsionGrowth
p2m_reactivate "P2MW.S_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent.P2mTorsionGrowth"

open P2mTorsionGrowth in
theorem solution
    {A : Type*} [AddCommGroup A] (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) (τ : A →+ A)
    (hfin : Finite (Submodule.torsionBy ℤ A (ℓ : ℤ)))
    (hle : Nat.card (Submodule.torsionBy ℤ A (ℓ : ℤ)) ≤ ℓ ^ r)
    (hτ : ∀ x : A, ℓ ^ 2 • x = 0 → τ x = x)
    (hfix : ∃ c k₀ : ℕ, ∀ k : ℕ,
      Nat.card {x : A // x ∈ AddCommGroup.primaryComponent A ℓ ∧ (⇑τ)^[ℓ ^ (k₀ + k)] x = x} =
        ℓ ^ (r * k + c))
    (n : ℕ) :
    Nat.card (Submodule.torsionBy ℤ A ((ℓ ^ n : ℕ) : ℤ)) = ℓ ^ (r * n) := by
  obtain ⟨c, k₀, hfix⟩ := hfix
  have e1 : ∀ m : ℕ, Submodule.torsionBy ℤ A (m : ℤ) ≃ tor A m := fun m =>
    Equiv.subtypeEquivRight (fun x => by
      rw [Submodule.mem_torsionBy_iff, mem_tor, natCast_zsmul])
  haveI : Finite (tor A ℓ) := Finite.of_equiv _ (e1 ℓ)
  have hle' : Nat.card (tor A ℓ) ≤ ℓ ^ r := by rwa [← Nat.card_congr (e1 ℓ)]
  rw [Nat.card_congr (e1 (ℓ ^ n))]
  exact main ℓ r τ hle' hτ c k₀ hfix n

end S_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent
end P2MW
export P2MW.S_AddCommGroup_natCard_torsionBy_pow_eq_pow_of_natCard_fixed_primaryComponent (solution)
