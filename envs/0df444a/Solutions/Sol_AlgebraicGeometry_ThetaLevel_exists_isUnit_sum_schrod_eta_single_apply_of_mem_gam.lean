-- Prove2me | solution 1 for AlgebraicGeometry.ThetaLevel.exists_isUnit_sum_schrod_eta_single_apply_of_mem_gam
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/1adb6e53-a223-587b-ac1e-7f10598278c9

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ThetaLevel_exists_isUnit_sum_schrod_eta_single_apply_of_mem_gam

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

noncomputable section

namespace C4bKit

theorem sum_eq_zero_of_isUnit_one_sub {K : Type} [AddCommGroup K] [Fintype K] {R : Type} [CommRing R]
    (χ : K → R) (hχ : ∀ k k' : K, χ (k + k') = χ k * χ k') (k₁ : K) (hk₁ : IsUnit (1 - χ k₁)) :
    ∑ k, χ k = 0 := by
  have h : ∑ k, χ k = χ k₁ * ∑ k, χ k := by
    rw [Finset.mul_sum]
    exact (Fintype.sum_equiv (Equiv.addLeft k₁) (fun k => χ k₁ * χ k) (fun k => χ k) (fun k => by
      show χ k₁ * χ k = χ (k₁ + k); rw [hχ])).symm
  have h2 : (1 - χ k₁) * ∑ k, χ k = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact (hk₁.mul_right_eq_zero).1 h2

theorem pow_a_h_k {g : ℕ} {δ : Fin g → ℕ} {d : ℕ} (z : AlgebraicGeometry.ThetaLevel.Heis δ d) (hz : z.h = 0) (m : ℕ) :
    (z ^ m).a = m • z.a ∧ (z ^ m).h = 0 ∧ (z ^ m).k = m • z.k := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨ha, hh, hk⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · rw [pow_succ, AlgebraicGeometry.ThetaLevel.Heis.mul_a, ha, hz, AlgebraicGeometry.ThetaLevel.pair_zero_right, add_zero, succ_nsmul]
    · rw [pow_succ, AlgebraicGeometry.ThetaLevel.Heis.mul_h, hh, hz, add_zero]
    · rw [pow_succ, AlgebraicGeometry.ThetaLevel.Heis.mul_k, hk, succ_nsmul]

theorem exists_eq_two_mul_of_nsmul_eq_zero {d : ℕ} [NeZero d] (a : ZMod (2 * d)) (ha : d • a = 0) :
    ∃ j : ℕ, a = ((2 * j : ℕ) : ZMod (2 * d)) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne _)
  haveI : NeZero (2 * d) := ⟨by omega⟩
  rw [nsmul_eq_mul, ← ZMod.natCast_zmod_val a, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at ha
  obtain ⟨c, hc⟩ := ha
  have h2 : 2 ∣ a.val := ⟨c, by nlinarith [hc]⟩
  obtain ⟨j, hj⟩ := h2
  exact ⟨j, by rw [← hj, ZMod.natCast_zmod_val]⟩

end C4bKit

end

open C4bKit in

theorem solution
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (γ : MulAut (Heis δ d)) (hγ : γ ∈ Heis.Gam δ d)
    :
    ∃ y₀ : HH δ, IsUnit ((∑ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) (Pi.single y₀ 1)) y₀) := by
  classical
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne _)
  have hω2d : ω ^ (2 * d) = 1 := by rw [pow_mul, hω, hζ]

  have hδdvd : ∀ i, δ i ∣ d := fun i => hδd ▸ Finset.dvd_prod_of_mem δ (Finset.mem_univ i)

  set q : HH δ → ZMod (2 * d) := fun k => (γ (Heis.eta k)).a with hq
  set α : HH δ → HH δ := fun k => (γ (Heis.eta k)).h with hα
  set β : HH δ → HH δ := fun k => (γ (Heis.eta k)).k with hβ
  have heta_add : ∀ k k' : HH δ, (Heis.eta (k + k') : Heis δ d) = Heis.eta k * Heis.eta k' := by
    intro k k'
    refine Heis.ext ?_ ?_ ?_ <;> simp [Heis.eta, pair_zero_right]
  have hγmul : ∀ k k', γ (Heis.eta (k + k')) = γ (Heis.eta k) * γ (Heis.eta k') := by
    intro k k'; rw [heta_add, map_mul]
  have hα_add : ∀ k k', α (k + k') = α k + α k' := by
    intro k k'; simp only [hα]; rw [hγmul, Heis.mul_h]
  have hβ_add : ∀ k k', β (k + k') = β k + β k' := by
    intro k k'; simp only [hβ]; rw [hγmul, Heis.mul_k]
  have hq_add : ∀ k k', α k' = 0 → q (k + k') = q k + q k' := by
    intro k k' hk'
    simp only [hq]; rw [hγmul, Heis.mul_a]
    have : (γ (Heis.eta k')).h = 0 := hk'
    rw [this, pair_zero_right, add_zero]
  have hα0 : α 0 = 0 := by
    have := hα_add 0 0; rw [add_zero] at this; exact left_eq_add.mp this |>.symm ▸ (by simpa using this)

  let αHom : HH δ →+ HH δ := { toFun := α, map_zero' := hα0, map_add' := hα_add }
  let K₀ : AddSubgroup (HH δ) := αHom.ker
  have hK₀ : ∀ k, k ∈ K₀ ↔ α k = 0 := fun k => AddMonoidHom.mem_ker

  have hcoord : ∀ y : HH δ, (∑ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) (Pi.single y 1)) y =
      ∑ k : K₀, omegaPow d B ω (q k + pair δ d (β k) y) := by
    intro y
    rw [Finset.sum_apply]
    have hterm : ∀ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) (Pi.single y 1) y =
        if α k = 0 then omegaPow d B ω (q k + pair δ d (β k) y) else 0 := by
      intro k
      rw [schrod_apply]
      simp only [thetaChar]
      by_cases hk : α k = 0
      · have hh : (γ (Heis.eta k)).h = 0 := hk
        rw [if_pos hk, hh, sub_zero, Pi.single_eq_same, mul_one, ← omegaPow_add d B ω hω2d]
      · have hh : (γ (Heis.eta k)).h ≠ 0 := hk
        rw [if_neg hk, Pi.single_eq_of_ne (by intro h'; exact hh (by simpa [sub_eq_self] using h')), mul_zero, mul_zero]
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (p := fun k => k ∈ K₀) (Finset.univ.filter fun k => α k = 0) (fun k => by simp [K₀, αHom])
      (fun k => omegaPow d B ω (q k + pair δ d (β k) y))

  let Ev : ZMod (2 * d) → Prop := fun a => ∃ m : ℕ, a = ((2 * m : ℕ) : ZMod (2 * d))
  have hEv_add : ∀ a b, Ev a → Ev b → Ev (a + b) := by
    rintro a b ⟨m, rfl⟩ ⟨m', rfl⟩; exact ⟨m + m', by push_cast; ring⟩
  have hEv_zero : Ev 0 := ⟨0, by simp⟩
  have hEv_sum : ∀ (s : Finset (Fin g)) (f : Fin g → ZMod (2 * d)), (∀ i, Ev (f i)) → Ev (∑ i ∈ s, f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hEv_zero
    | insert i s hi ih => rw [Finset.sum_insert hi]; exact hEv_add _ _ (hf i) ih

  have hiota : ∀ (i : Fin g) (x : ZMod (δ i)), iota δ d i x = ((2 * ((d / δ i) * x.val) : ℕ) : ZMod (2 * d)) := by
    intro i x
    have h2 : δ i ∣ 2 * d := (hδdvd i).mul_left 2
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [iota_natCast δ d i h2, ← Nat.cast_mul]
    congr 1
    rw [Nat.mul_div_assoc 2 (hδdvd i)]; ring
  have hEv_pair : ∀ k h : HH δ, Ev (pair δ d k h) := by
    intro k h
    simp only [pair]
    exact hEv_sum _ _ fun i => ⟨(d / δ i) * (k i * h i).val, hiota i _⟩

  have hunit : ∀ a, Ev a → a ≠ 0 → IsUnit (1 - omegaPow d B ω a) := by
    rintro a ⟨m, rfl⟩ hne
    rw [omegaPow_natCast d B ω hω2d, pow_mul, hω, ← Nat.mod_add_div m d, pow_add, pow_mul, hζ, one_pow, mul_one]
    refine hζu _ (Nat.pos_of_ne_zero fun h0 => hne ?_) (Nat.mod_lt _ hd0)

    obtain ⟨c, hc⟩ := (Nat.dvd_iff_mod_eq_zero).2 h0
    rw [hc, show 2 * (d * c) = (2 * d) * c by ring, Nat.cast_mul, ZMod.natCast_self, zero_mul]

  have heta_nsmul : ∀ (m : ℕ) (k : HH δ), (Heis.eta (m • k) : Heis δ d) = Heis.eta k ^ m := by
    intro m k
    induction m with
    | zero => simp only [zero_smul, pow_zero]; rfl
    | succ m ih => rw [succ_nsmul, heta_add, ih, pow_succ]
  have hdk : ∀ k : HH δ, d • k = 0 := by
    intro k; funext i
    show (d • k) i = 0
    rw [Pi.smul_apply, nsmul_eq_mul, (ZMod.natCast_eq_zero_iff d (δ i)).2 (hδdvd i), zero_mul]
  have hEv_q : ∀ k : K₀, Ev (q k) := by
    intro k
    have hk0 : α k = 0 := (hK₀ k).1 k.2
    have hpow : (γ (Heis.eta (k : HH δ))) ^ d = 1 := by
      rw [← map_pow, ← heta_nsmul, hdk]; exact map_one γ
    have := (C4bKit.pow_a_h_k (γ (Heis.eta (k : HH δ))) hk0 d).1
    rw [hpow, Heis.one_a] at this
    exact C4bKit.exists_eq_two_mul_of_nsmul_eq_zero _ this.symm

  have hcardH : (Fintype.card (HH δ) : B) = (d : B) := by
    rw [Fintype.card_pi]; simp only [ZMod.card]; rw [hδd]
  have hinner : ∀ k' : HH δ, ∑ y : HH δ, omegaPow d B ω (pair δ d k' y) = if k' = 0 then (d : B) else 0 := by
    intro k'
    by_cases hk' : k' = 0
    · rw [if_pos hk', hk']
      simp only [pair_zero_left, omegaPow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcardH]
    · rw [if_neg hk']
      obtain ⟨i, hi⟩ : ∃ i, k' i ≠ 0 := by
        by_contra h; push Not at h; exact hk' (funext h)
      refine C4bKit.sum_eq_zero_of_isUnit_one_sub (fun y => omegaPow d B ω (pair δ d k' y))
        (fun y y' => by rw [pair_add_right, omegaPow_add d B ω hω2d]) (Pi.single i 1) (hunit _ (hEv_pair _ _) ?_)

      have hp : pair δ d k' (Pi.single i 1) = iota δ d i (k' i) := by
        simp only [pair]
        rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero, map_zero]) (fun h => absurd (Finset.mem_univ i) h),
          Pi.single_eq_same, mul_one]
      rw [hp, hiota]
      intro h0
      haveI : NeZero (2 * d) := ⟨by omega⟩
      rw [ZMod.natCast_eq_zero_iff] at h0

      have hx0 : 0 < (k' i).val := Nat.pos_of_ne_zero fun h => hi ((ZMod.val_eq_zero _).1 h)
      have hxlt : (k' i).val < δ i := ZMod.val_lt _
      have hq' : 0 < d / δ i := Nat.div_pos (Nat.le_of_dvd hd0 (hδdvd i)) (Nat.pos_of_ne_zero (NeZero.ne _))
      have h1 : d ∣ (d / δ i) * (k' i).val := by
        have := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h0; exact this
      have h2 : (d / δ i) * (k' i).val < d := by
        calc (d / δ i) * (k' i).val < (d / δ i) * δ i := Nat.mul_lt_mul_of_pos_left hxlt hq'
          _ = d := Nat.div_mul_cancel (hδdvd i)
      exact absurd (Nat.le_of_dvd (Nat.mul_pos hq' hx0) h1) (not_le.2 h2)

  have hK₀β : ∀ k : K₀, β k = 0 → (k : HH δ) = 0 := by
    intro k hb
    have hk0 : α k = 0 := (hK₀ k).1 k.2
    have hz : γ (Heis.eta (k : HH δ)) = Heis.cen (q k) := by
      refine Heis.ext ?_ ?_ ?_
      · rfl
      · exact hk0
      · exact hb
    rw [← hγ (q k)] at hz
    have := γ.injective hz
    have := congrArg Heis.k this
    simpa [Heis.eta, Heis.cen] using this

  set S : HH δ → B := fun y => ∑ k : K₀, omegaPow d B ω (q k + pair δ d (β k) y) with hS
  have htotal : ∑ y, S y = (d : B) := by
    simp only [hS]
    rw [Finset.sum_comm]
    simp_rw [omegaPow_add d B ω hω2d, ← Finset.mul_sum, hinner]
    rw [Fintype.sum_eq_single (⟨0, K₀.zero_mem⟩ : K₀) (fun k hk => by
      rw [if_neg (fun hb => hk (Subtype.ext (hK₀β k hb))), mul_zero])]
    have hq0 : q (0 : HH δ) = 0 := by
      simp only [hq]
      rw [show (Heis.eta (0 : HH δ) : Heis δ d) = 1 from rfl, map_one, Heis.one_a]
    have hβ0 : β (0 : HH δ) = 0 := by
      simp only [hβ]
      rw [show (Heis.eta (0 : HH δ) : Heis δ d) = 1 from rfl, map_one, Heis.one_k]
    show omegaPow d B ω (q (0 : HH δ)) * (if β (0 : HH δ) = 0 then (d : B) else 0) = (d : B)
    rw [hq0, hβ0, if_pos rfl, omegaPow_zero, one_mul]

  have hψ_add : ∀ (y : HH δ) (k k' : K₀),
      q ((k + k' : K₀) : HH δ) + pair δ d (β ((k + k' : K₀) : HH δ)) y =
        (q k + pair δ d (β k) y) + (q k' + pair δ d (β k') y) := by
    intro y k k'
    rw [AddSubgroup.coe_add, hq_add _ _ ((hK₀ _).1 k'.2), hβ_add, pair_add_left]
    abel

  by_cases hA : ∃ y₀ : HH δ, ∀ k : K₀, q k + pair δ d (β k) y₀ = 0
  · obtain ⟨y₀, hy₀⟩ := hA
    refine ⟨y₀, ?_⟩
    rw [hcoord]
    simp_rw [hy₀, omegaPow_zero]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

    obtain ⟨m, hm⟩ := K₀.card_addSubgroup_dvd_card
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hm
    have hdm : (d : B) = (Fintype.card K₀ : B) * (m : B) := by rw [← hcardH, hm, Nat.cast_mul]
    rw [hdm] at hd
    exact isUnit_of_mul_isUnit_left hd
  · push Not at hA
    have hS0 : ∀ y, S y = 0 := by
      intro y
      obtain ⟨k₁, hk₁⟩ := hA y
      simp only [hS]
      refine C4bKit.sum_eq_zero_of_isUnit_one_sub (fun k : K₀ => omegaPow d B ω (q k + pair δ d (β k) y))
        (fun k k' => by rw [hψ_add, omegaPow_add d B ω hω2d]) k₁ (hunit _ ?_ hk₁)
      exact hEv_add _ _ (hEv_q k₁) (hEv_pair _ _)
    have hd0' : (d : B) = 0 := by rw [← htotal]; exact Finset.sum_eq_zero fun y _ => hS0 y
    rw [hd0'] at hd
    haveI : Subsingleton B := subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hd)
    exact ⟨0, isUnit_of_subsingleton _⟩

end S_AlgebraicGeometry_ThetaLevel_exists_isUnit_sum_schrod_eta_single_apply_of_mem_gam
end P2MW
export P2MW.S_AlgebraicGeometry_ThetaLevel_exists_isUnit_sum_schrod_eta_single_apply_of_mem_gam (solution)
