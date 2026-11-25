-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCup
-- name    : GroundTheory_ProfiniteCohomology_CyclicCup
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:09:28.325686+00:00
-- url     : https://prove2.me/theorems/2d14a276-0552-58a6-b236-9fc6138cf452
-- title:
--   Cyclic Cup
-- statement:
--   Definitions and structural lemmas for Cyclic Cup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CyclicCup.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCupDefs
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Theorems.Thm_GroundTheory_GroupCoh_cupCochainsTensor_tmul
import Theorems.Thm_GroundTheory_GroupCoh_h2IntAddEquiv_symm_apply_eq_H2_class
import Theorems.Thm_GroundTheory_GroupCoh_iCocycles_cocyclesMap
import Theorems.Thm_GroundTheory_GroupCoh_mem_normRangeInvariants_iff
import Theorems.Thm_GroundTheory_GroupCoh_rightUnitor_hom_tmul
import Theorems.Thm_GroundTheory_GroupCoh_tateZeroClass_surjective
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cupH___fa07882c353c
import Theorems.Thm_P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336
import Theorems.Thm_P2M_GroundTheory_GroupCoh_map___apply_e7888b2277b6
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.GroupCoh.cupCochainsTensor_tmul
attribute [local simp] P2M_GroundTheory_GroupCoh_cup__apply_a78771e4f336


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory MonoidalCategory groupCohomology GroundTheory.GroupCoh
section Formula
variable {G : Type} [Group G]
noncomputable def reprIco (u : AddCircle (1 : ℚ)) : ℚ :=
  (AddCircle.equivIco 1 0 u : ℚ)
theorem reprIco_mem (u : AddCircle (1 : ℚ)) : reprIco u ∈ Set.Ico (0 : ℚ) 1 := by
  unfold reprIco
  simpa using (AddCircle.equivIco (1 : ℚ) 0 u).2
theorem coe_reprIco (u : AddCircle (1 : ℚ)) : ((reprIco u : ℚ) : AddCircle (1 : ℚ)) = u :=
  (AddCircle.equivIco (1 : ℚ) 0).symm_apply_apply u
theorem reprIco_coe {q : ℚ} (hq : q ∈ Set.Ico (0 : ℚ) 1) :
    reprIco (q : AddCircle (1 : ℚ)) = q := by
  unfold reprIco
  rw [AddCircle.equivIco_coe_eq (by simpa using hq)]
noncomputable def charCocycle (χ : Additive G →+ AddCircle (1 : ℚ)) (p : G × G) : ℤ :=
  ⌊reprIco (χ (Additive.ofMul p.1)) + reprIco (χ (Additive.ofMul p.2))⌋
theorem charCocycle_cast (χ : Additive G →+ AddCircle (1 : ℚ)) (x x' : G) :
    (charCocycle χ (x, x') : ℚ) = reprIco (χ (Additive.ofMul x)) + reprIco (χ (Additive.ofMul x'))
      - reprIco (χ (Additive.ofMul (x * x'))) := by
  have h1 := reprIco_mem (χ (Additive.ofMul x))
  have h2 := reprIco_mem (χ (Additive.ofMul x'))
  have h3 := reprIco_mem (χ (Additive.ofMul (x * x')))
  have hc : ((reprIco (χ (Additive.ofMul x)) + reprIco (χ (Additive.ofMul x'))
      - reprIco (χ (Additive.ofMul (x * x'))) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_add, coe_reprIco, coe_reprIco, coe_reprIco, ofMul_mul,
      map_add, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 hc
  rw [zsmul_one] at hn
  have hfl : charCocycle χ (x, x') = n := by
    unfold charCocycle
    rw [Int.floor_eq_iff]
    simp only [Set.mem_Ico] at h1 h2 h3
    constructor <;> linarith
  rw [hfl, hn]
variable [Fintype G]
theorem charCocycle_mem_and_eq (χ : Additive G →+ AddCircle (1 : ℚ)) :
    ∃ hc : charCocycle χ ∈ cocycles₂ (Rep.trivial ℤ G ℤ),
      charClass χ = H2π (Rep.trivial ℤ G ℤ) ⟨charCocycle χ, hc⟩ :=
  h2IntAddEquiv_symm_apply_eq_H2_class G χ (fun g => reprIco (χ (Additive.ofMul g)))
    (fun _ => coe_reprIco _) (charCocycle χ) (fun g h => charCocycle_cast χ g h)
theorem charCocycle_mem (χ : Additive G →+ AddCircle (1 : ℚ)) :
    charCocycle χ ∈ cocycles₂ (Rep.trivial ℤ G ℤ) :=
  (charCocycle_mem_and_eq χ).1
theorem charClass_eq_H2π (χ : Additive G →+ AddCircle (1 : ℚ)) :
    charClass χ = H2π (Rep.trivial ℤ G ℤ) ⟨charCocycle χ, charCocycle_mem χ⟩ :=
  (charCocycle_mem_and_eq χ).2
end Formula
section CupFormula
attribute [local instance 2000] Rep.hV2
variable {G : Type} [Group G] {A : Rep ℤ G}
theorem smul_mem_cocycles₂ (c : cocycles₂ (Rep.trivial ℤ G ℤ)) (a : A.ρ.invariants) :
    (fun p => c p • (a : A)) ∈ cocycles₂ A := by
  rw [mem_cocycles₂_iff]
  intro g h j
  have hc := (mem_cocycles₂_iff c).1 c.2 g h j
  have ha : A.ρ g (a : A) = a := a.2 g
  change c (g * h, j) + c (g, h) = c (h, j) + c (g, h * j) at hc
  rw [map_zsmul, ha, ← add_zsmul, ← add_zsmul, hc]
theorem H0Iso_inv_apply (a : A.ρ.invariants) :
    (H0Iso A).inv.hom a = (π A 0).hom ((cocyclesIso₀ A).inv.hom a) := by
  have e : (cocyclesIso₀ A).inv ≫ π A 0 = (H0Iso A).inv := by
    rw [Iso.inv_comp_eq, ← π_comp_H0Iso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← e]
  rfl
theorem cupCharClass_apply (χ : Additive G →+ AddCircle (1 : ℚ))
    (c : cocycles₂ (Rep.trivial ℤ G ℤ)) (hc : charClass χ = H2π _ c) (a : A.ρ.invariants) :
    (cupCharClass A χ).hom a = H2π A ⟨fun p => c p • (a : A), smul_mem_cocycles₂ c a⟩ := by
  change (map (MonoidHom.id G) (ρ_ A).hom 2).hom
    (cupH (A := A) (B := 𝟙_ (Rep ℤ G)) (zero_add 2) ((H0Iso A).inv.hom a) (charClass χ)) = _
  rw [H0Iso_inv_apply, hc]
  change map (MonoidHom.id G) (ρ_ A).hom 2 (cupH (A := A) (B := 𝟙_ (Rep ℤ G)) (zero_add 2)
    (π A 0 ((cocyclesIso₀ A).inv a))
    (π (𝟙_ (Rep ℤ G)) 2 ((isoCocycles₂ (𝟙_ (Rep ℤ G))).inv c))) =
    π A 2 ((isoCocycles₂ A).inv ⟨fun p => c p • (a : A), smul_mem_cocycles₂ c a⟩)
  rw [cupH_π]
  refine (GroundTheory.GroupCoh.map_π_apply _ _).trans ?_
  congr 1
  apply cocycles_ext
  rw [iCocycles_cocyclesMap]
  funext v
  erw [iCocycles_cupCocycles, cupCochain_apply]
  rw [isoCocycles₂_inv_comp_iCocycles_apply, isoCocycles₂_inv_comp_iCocycles_apply,
    cocyclesIso₀_inv_comp_iCocycles_apply]
  erw [rightUnitor_hom_tmul]
  simp only [cochainsIso₀, cochainsIso₂]
  exact int_smul_eq_zsmul _ _ _
end CupFormula
section Cyclic
attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module
variable {G : Type} [Group G] {A : Rep ℤ G}
theorem reprIco_zero : reprIco 0 = 0 := by
  simpa using reprIco_coe (q := 0) (by simp)
theorem charCocycle_one_right (χ : Additive G →+ AddCircle (1 : ℚ)) (x : G) :
    charCocycle χ (x, 1) = 0 := by
  unfold charCocycle
  rw [ofMul_one, map_zero, reprIco_zero, add_zero, Int.floor_eq_zero_iff]
  exact reprIco_mem _
theorem charCocycle_one_left (χ : Additive G →+ AddCircle (1 : ℚ)) (x : G) :
    charCocycle χ (1, x) = 0 := by
  unfold charCocycle
  rw [ofMul_one, map_zero, reprIco_zero, zero_add, Int.floor_eq_zero_iff]
  exact reprIco_mem _
variable [Fintype G]
theorem charCocycle_cocycle (χ : Additive G →+ AddCircle (1 : ℚ)) (x y w : G) :
    charCocycle χ (x * y, w) + charCocycle χ (x, y) =
      charCocycle χ (y, w) + charCocycle χ (x, y * w) := by
  have h := (mem_cocycles₂_iff _).1 (charCocycle_mem χ) x y w
  exact h
theorem sum_charCocycle_cast (χ : Additive G →+ AddCircle (1 : ℚ)) (g : G) :
    ((∑ x, charCocycle χ (x, g) : ℤ) : ℚ) =
      Fintype.card G * reprIco (χ (Additive.ofMul g)) := by
  push_cast
  simp_rw [charCocycle_cast]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.sum_equiv (Equiv.mulRight g) (fun x => reprIco (χ (Additive.ofMul (x * g))))
      (fun x => reprIco (χ (Additive.ofMul x))) (fun x => rfl)]
  simp
noncomputable def normWeight (χ : Additive G →+ AddCircle (1 : ℚ)) (h x : G) : ℤ :=
  -⌊reprIco (χ (Additive.ofMul h)) - reprIco (χ (Additive.ofMul x))⌋
omit [Fintype G] in
theorem normWeight_cast (χ : Additive G →+ AddCircle (1 : ℚ)) (h x : G) :
    (normWeight χ h x : ℚ) = reprIco (χ (Additive.ofMul x)) - reprIco (χ (Additive.ofMul h))
      + reprIco (χ (Additive.ofMul (x⁻¹ * h))) := by
  have h1 := reprIco_mem (χ (Additive.ofMul h))
  have h2 := reprIco_mem (χ (Additive.ofMul x))
  have h3 := reprIco_mem (χ (Additive.ofMul (x⁻¹ * h)))
  have hc : ((reprIco (χ (Additive.ofMul h)) - reprIco (χ (Additive.ofMul x))
      - reprIco (χ (Additive.ofMul (x⁻¹ * h))) : ℚ) : AddCircle (1 : ℚ)) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_sub, coe_reprIco, coe_reprIco, coe_reprIco, ofMul_mul,
      ofMul_inv, map_add, map_neg]
    abel
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff _).1 hc
  rw [zsmul_one] at hn
  have hfl : ⌊reprIco (χ (Additive.ofMul h)) - reprIco (χ (Additive.ofMul x))⌋ = n := by
    rw [Int.floor_eq_iff]
    simp only [Set.mem_Ico] at h1 h2 h3
    constructor <;> linarith
  unfold normWeight
  rw [hfl]
  push_cast
  linarith
theorem smul_norm_mem_coboundaries₂ (χ : Additive G →+ AddCircle (1 : ℚ)) (b : A) :
    (fun p => charCocycle χ p • A.ρ.norm b) ∈ coboundaries₂ A := by
  refine ⟨fun x => ∑ h, normWeight χ h x • A.ρ h b, ?_⟩
  funext ⟨x, x'⟩
  have hw : ∀ h : G, normWeight χ (x⁻¹ * h) x' - normWeight χ h (x * x') + normWeight χ h x =
      charCocycle χ (x, x') := by
    intro h
    have e := charCocycle_cast χ x x'
    have e1 := normWeight_cast χ (x⁻¹ * h) x'
    have e2 := normWeight_cast χ h (x * x')
    have e3 := normWeight_cast χ h x
    rw [← mul_assoc] at e1
    rw [mul_inv_rev] at e2
    have : ((normWeight χ (x⁻¹ * h) x' - normWeight χ h (x * x') + normWeight χ h x : ℤ) : ℚ) =
        (charCocycle χ (x, x') : ℚ) := by
      push_cast
      rw [e, e1, e2, e3]
      ring
    exact_mod_cast this
  have hshift : A.ρ x (∑ h, normWeight χ h x' • A.ρ h b) =
      ∑ h, normWeight χ (x⁻¹ * h) x' • A.ρ h b := by
    rw [map_sum]
    simp_rw [map_zsmul, ← Module.End.mul_apply, ← map_mul]
    exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ (fun h => by simp)
  simp only [d₁₂_hom_apply]
  rw [hshift, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Representation.norm,
    LinearMap.sum_apply, ← Finset.sum_zsmul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← hw h, add_zsmul, sub_zsmul, sub_eq_add_neg]
theorem exists_norm_eq_of_mem_coboundaries₂ (χ : Additive G →+ AddCircle (1 : ℚ)) (g : G)
    (hg : ∑ x, charCocycle χ (x, g) = 1) (a : A)
    (h : (fun p => charCocycle χ p • a) ∈ coboundaries₂ A) : ∃ b, A.ρ.norm b = a := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f g, ?_⟩
  have e : ∀ x, A.ρ x (f g) - f (x * g) + f x = charCocycle χ (x, g) • a := fun x =>
    congrFun hf (x, g)
  have hs := Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => e x)
  have hsum : ∑ x, charCocycle χ (x, g) • a = (∑ x, charCocycle χ (x, g)) • a := by
    have := map_sum (zmultiplesHom A a) (fun x => charCocycle χ (x, g)) Finset.univ
    simp only [zmultiplesHom_apply] at this
    exact this.symm
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum, hg, one_zsmul,
    Fintype.sum_equiv (Equiv.mulRight g) (fun x => f (x * g)) f (fun x => rfl), sub_add_cancel]
    at hs
  rw [← hs, Representation.norm, LinearMap.sum_apply]
theorem exists_sub_mem_coboundaries₂ (χ : Additive G →+ AddCircle (1 : ℚ)) (g : G)
    (hgen : ∀ x, ∃ j : ℕ, g ^ j = x) (hg : ∑ x, charCocycle χ (x, g) = 1) (z : cocycles₂ A) :
    ∃ a : A, (∀ h, A.ρ h a = a) ∧
      (fun p => charCocycle χ p • a) - ⇑z ∈ coboundaries₂ A := by
  classical
  set m := Fintype.card G with hm
  set c := charCocycle χ with hcdef
  have hz := (mem_cocycles₂_iff z).1 z.2
  set a : A := ∑ x, z (x, g) with hadef
  have ha : ∀ h, A.ρ h a = a := by
    intro h
    have e : ∀ x, A.ρ h (z (x, g)) = z (h * x, g) + z (h, x) - z (h, x * g) := by
      intro x
      rw [(hz h x g)]
      abel
    rw [hadef, map_sum, Finset.sum_congr rfl (fun x _ => e x), Finset.sum_sub_distrib,
      Finset.sum_add_distrib,
      Fintype.sum_equiv (Equiv.mulLeft h) (fun x => z (h * x, g)) (fun x => z (x, g))
        (fun x => rfl),
      Fintype.sum_equiv (Equiv.mulRight g) (fun x => z (h, x * g)) (fun x => z (h, x))
        (fun x => rfl)]
    abel
  set φ : G → A := fun x => c (x, g) • a - z (x, g) with hφdef
  have hsum : ∑ x, c (x, g) • a = (∑ x, c (x, g)) • a := by
    have := map_sum (zmultiplesHom A a) (fun x => c (x, g)) Finset.univ
    simp only [zmultiplesHom_apply] at this
    exact this.symm
  have hφ : ∑ x, φ x = 0 := by
    rw [hφdef, Finset.sum_sub_distrib, hsum, hg, one_zsmul, hadef, sub_self]
  have hmem : ∀ x, x ∈ Subgroup.zpowers g := fun x => by
    obtain ⟨j, rfl⟩ := hgen x
    exact Subgroup.npow_mem_zpowers g j
  have hord : orderOf g = m := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hmem, Nat.card_eq_fintype_card]
  have hsumpow : ∀ ψ : G → A, ∑ i ∈ Finset.range m, ψ (g ^ i) = ∑ x, ψ x := by
    intro ψ
    refine Finset.sum_nbij (fun i => g ^ i) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · intro i hi j hj hij
      rw [Finset.coe_range, ← hord] at hi hj
      exact pow_injOn_Iio_orderOf hi hj hij
    · intro x _
      obtain ⟨j, rfl⟩ := hgen x
      refine ⟨j % m, ?_, ?_⟩
      · rw [Finset.coe_range, Set.mem_Iio]
        exact Nat.mod_lt _ (Fintype.card_pos)
      · simp only
        rw [← hord, pow_mod_orderOf]
  set F : ℕ → A := fun j => z (1, 1) + ∑ i ∈ Finset.range j, φ (g ^ i) with hFdef
  have hFsucc : ∀ j, F (j + 1) = F j + φ (g ^ j) := by
    intro j
    simp only [hFdef, Finset.sum_range_succ, add_assoc]
  have hFper : ∀ j, F (j + m) = F j := by
    intro j
    have e : ∑ i ∈ Finset.range m, φ (g ^ (j + i)) = 0 := by
      have := hsumpow (fun x => φ (g ^ j * x))
      simp only [← pow_add] at this
      rw [this, Fintype.sum_equiv (Equiv.mulLeft (g ^ j)) (fun x => φ (g ^ j * x)) φ
        (fun x => rfl), hφ]
    simp only [hFdef, Finset.sum_range_add, e, add_zero]
  have hFmod : ∀ j, F j = F (j % m) := by
    have hk : ∀ k r, F (r + m * k) = F r := by
      intro k
      induction k with
      | zero => intro r; simp
      | succ k ih => intro r; rw [Nat.mul_succ, ← add_assoc, hFper, ih]
    intro j
    conv_lhs => rw [← Nat.mod_add_div j m]
    exact hk _ _
  set ind : G → ℕ := fun x => Classical.choose (hgen x) with hinddef
  have hind : ∀ x, g ^ ind x = x := fun x => Classical.choose_spec (hgen x)
  set f : G → A := fun x => F (ind x) with hfdef
  have hf : ∀ j, f (g ^ j) = F j := by
    intro j
    have e := hind (g ^ j)
    rw [pow_inj_mod, hord] at e
    simp only [hfdef]
    rw [hFmod (ind _), hFmod j, e]
  have hf1 : f 1 = z (1, 1) := by
    have := hf 0
    rw [pow_zero] at this
    rw [this]
    simp [hFdef]
  have hfg : f g = 0 := by
    have := hf 1
    rw [pow_one] at this
    rw [this, hFsucc, pow_zero, hFdef]
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, hφdef, hcdef,
      charCocycle_one_left, zero_smul, cocycles₂_map_one_fst z g]
    abel
  have hfstep : ∀ x, f (x * g) = f x + φ x := by
    intro x
    obtain ⟨j, rfl⟩ := hgen x
    rw [← pow_succ, hf, hf, hFsucc]
  set z' : G × G → A := fun p => z p - (d₁₂ A).hom f p with hz'def
  have hz'g : ∀ x, z' (x, g) = c (x, g) • a := by
    intro x
    simp only [hz'def, d₁₂_hom_apply, hfg, map_zero, hfstep, hφdef]
    abel
  have hz'1 : ∀ x, z' (x, 1) = 0 := by
    intro x
    simp only [hz'def, d₁₂_hom_apply, hf1, mul_one, cocycles₂_map_one_snd z x]
    abel
  have hdf := (mem_cocycles₂_iff ((d₁₂ A).hom f)).1 (d₁₂_apply_mem_cocycles₂ f)
  have hz'coc : ∀ x y w, z' (x * y, w) + z' (x, y) = A.ρ x (z' (y, w)) + z' (x, y * w) := by
    intro x y w
    have h1 := hz x y w
    have h2 := hdf x y w
    simp only [hz'def, map_sub]
    rw [show z (x * y, w) - (d₁₂ A).hom f (x * y, w) + (z (x, y) - (d₁₂ A).hom f (x, y)) =
      (z (x * y, w) + z (x, y)) - ((d₁₂ A).hom f (x * y, w) + (d₁₂ A).hom f (x, y)) by abel,
      h1, h2]
    abel
  have hz'pow : ∀ j x, z' (x, g ^ j) = c (x, g ^ j) • a := by
    intro j
    induction j with
    | zero =>
      intro x
      rw [pow_zero, hz'1, hcdef, charCocycle_one_right, zero_smul]
    | succ j ih =>
      intro x
      have e1 := hz'coc x (g ^ j) g
      rw [hz'g, hz'g, ih, map_zsmul, ha] at e1
      have e2 := charCocycle_cocycle χ x (g ^ j) g
      rw [pow_succ]
      have e3 : c (x, g ^ j * g) = c (x * g ^ j, g) + c (x, g ^ j) - c (g ^ j, g) := by
        rw [hcdef]
        linarith
      rw [e3, sub_zsmul, add_zsmul, e1]
      abel
  refine ⟨a, ha, -f, ?_⟩
  funext p
  obtain ⟨x, y⟩ := p
  obtain ⟨j, rfl⟩ := hgen y
  have e := hz'pow j x
  simp only [hz'def] at e
  simp only [map_neg, Pi.neg_apply, Pi.sub_apply]
  rw [← e]
  abel
theorem exists_generator_sum_charCocycle [IsCyclic G] (χ : Additive G →+ AddCircle (1 : ℚ))
    (hχ : Function.Injective χ) (hm : 2 ≤ Fintype.card G) :
    ∃ g : G, (∀ x, ∃ j : ℕ, g ^ j = x) ∧ ∑ x, charCocycle χ (x, g) = 1 := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := G)
  set m := Fintype.card G with hmdef
  have hordσ : orderOf σ = m := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, Nat.card_eq_fintype_card]
  have hu : addOrderOf (χ (Additive.ofMul σ)) = m := by
    rw [addOrderOf_injective χ hχ, addOrderOf_ofMul_eq_orderOf, hordσ]
  have hfin : IsOfFinAddOrder (χ (Additive.ofMul σ)) := by
    rw [← addOrderOf_pos_iff, hu]
    omega
  obtain ⟨r, hr, -, hre⟩ := AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder hfin
  rw [hu] at hr hre
  have hbez : (r : ℤ) * Nat.gcdA r m + m * Nat.gcdB r m = 1 := by
    have := Nat.gcd_eq_gcd_ab r m
    rw [hr] at this
    push_cast at this
    linarith
  obtain ⟨s, hs⟩ : ∃ s : ℤ, s = Nat.gcdA r m := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = Nat.gcdB r m := ⟨_, rfl⟩
  rw [← hs, ← ht] at hbez
  have hσm : σ ^ (m : ℤ) = 1 := by
    rw [zpow_natCast, ← hordσ, pow_orderOf_eq_one]
  have hσeq : (σ ^ s) ^ (r : ℤ) = σ := by
    rw [← zpow_mul, show s * (r : ℤ) = 1 + (m : ℤ) * (-t) by linarith, zpow_add, zpow_one,
      zpow_mul, hσm, one_zpow, mul_one]
  refine ⟨σ ^ s, ?_, ?_⟩
  · intro x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hσ x)
    have hx : σ ^ k ∈ Subgroup.zpowers (σ ^ s) := ⟨(r : ℤ) * k, by
      simp only
      rw [zpow_mul, hσeq]⟩
    rw [← mem_powers_iff_mem_zpowers] at hx
    obtain ⟨j, hj⟩ := hx
    exact ⟨j, hj⟩
  · have hmpos : (0 : ℚ) < m := by exact_mod_cast (by omega : 0 < m)
    have hbezQ : (r : ℚ) * s + m * t = 1 := by exact_mod_cast hbez
    have hχg : χ (Additive.ofMul (σ ^ s)) = (((1 : ℚ) / m : ℚ) : AddCircle (1 : ℚ)) := by
      rw [ofMul_zpow, map_zsmul, ← hre, ← AddCircle.coe_zsmul, ← sub_eq_zero, ← AddCircle.coe_sub,
        AddCircle.coe_eq_zero_iff]
      refine ⟨-t, ?_⟩
      simp only [zsmul_eq_mul, mul_one]
      field_simp
      push_cast
      linarith
    have hy : reprIco (χ (Additive.ofMul (σ ^ s))) = 1 / m := by
      rw [hχg, reprIco_coe]
      refine ⟨by positivity, ?_⟩
      rw [div_lt_one hmpos]
      exact_mod_cast (by omega : 1 < m)
    have := sum_charCocycle_cast χ (σ ^ s)
    rw [hy, mul_one_div_cancel hmpos.ne'] at this
    exact_mod_cast this
omit [Fintype G] in

theorem mem_coboundaries₂_of_subsingleton [Subsingleton G] (z : cocycles₂ A) :
    ⇑z ∈ coboundaries₂ A := by
  refine ⟨fun _ => z (1, 1), ?_⟩
  funext ⟨x, y⟩
  rw [Subsingleton.elim x 1, Subsingleton.elim y 1]
  simp
theorem cupCharClass_apply_charCocycle (χ : Additive G →+ AddCircle (1 : ℚ))
    (a : A.ρ.invariants) :
    (cupCharClass A χ).hom a = H2π A ⟨fun p => charCocycle χ p • (a : A),
      smul_mem_cocycles₂ ⟨charCocycle χ, charCocycle_mem χ⟩ a⟩ :=
  cupCharClass_apply χ _ (charClass_eq_H2π χ) a
theorem cupCharClass_eq_zero_of_mem (χ : Additive G →+ AddCircle (1 : ℚ)) (a : A.ρ.invariants)
    (ha : a ∈ normRangeInvariants A) : (cupCharClass A χ).hom a = 0 := by
  obtain ⟨b, hb⟩ := (mem_normRangeInvariants_iff A a).1 ha
  rw [cupCharClass_apply_charCocycle, H2π_eq_zero_iff]
  change (fun p => charCocycle χ p • (a : A)) ∈ coboundaries₂ A
  rw [← hb]
  exact smul_norm_mem_coboundaries₂ χ b
noncomputable def tateZeroToH2 (A : Rep ℤ G) (χ : Additive G →+ AddCircle (1 : ℚ)) :
    tateCohomology A 0 ⟶ H2 A :=
  ((tateCohomologyZeroIso ℤ G).app A).hom ≫
    ModuleCat.ofHom ((normRangeInvariants A).liftQ (cupCharClass A χ).hom
      (fun a ha => cupCharClass_eq_zero_of_mem χ a ha))
theorem tateZeroToH2_tateZeroClass (χ : Additive G →+ AddCircle (1 : ℚ)) (a : A.ρ.invariants) :
    (tateZeroToH2 A χ).hom (tateZeroClass A a) = (cupCharClass A χ).hom a := by
  change ((normRangeInvariants A).liftQ (cupCharClass A χ).hom
      (fun a ha => cupCharClass_eq_zero_of_mem χ a ha))
    ((((tateCohomologyZeroIso ℤ G).app A).inv ≫ ((tateCohomologyZeroIso ℤ G).app A).hom).hom
      (Submodule.Quotient.mk a)) = _
  rw [Iso.inv_hom_id]
  rfl
variable [IsCyclic G]
theorem cupCharClass_eq_zero_iff (χ : Additive G →+ AddCircle (1 : ℚ)) (hχ : Function.Injective χ)
    (a : A.ρ.invariants) : (cupCharClass A χ).hom a = 0 ↔ a ∈ normRangeInvariants A := by
  refine ⟨fun h => ?_, cupCharClass_eq_zero_of_mem χ a⟩
  rw [mem_normRangeInvariants_iff]
  rcases Nat.lt_or_ge (Fintype.card G) 2 with hm | hm
  · have : Subsingleton G := Fintype.card_le_one_iff_subsingleton.1 (by omega)
    refine ⟨a, ?_⟩
    rw [Representation.norm, LinearMap.sum_apply, Fintype.sum_subsingleton _ 1, map_one,
      Module.End.one_apply]
  · obtain ⟨g, -, hg⟩ := exists_generator_sum_charCocycle χ hχ hm
    rw [cupCharClass_apply_charCocycle, H2π_eq_zero_iff] at h
    exact exists_norm_eq_of_mem_coboundaries₂ χ g hg (a : A) h
theorem cupCharClass_surjective (χ : Additive G →+ AddCircle (1 : ℚ)) (hχ : Function.Injective χ) :
    Function.Surjective (cupCharClass A χ).hom := by
  intro y
  induction y using H2_induction_on with
  | h z =>
    rcases Nat.lt_or_ge (Fintype.card G) 2 with hm | hm
    · have : Subsingleton G := Fintype.card_le_one_iff_subsingleton.1 (by omega)
      refine ⟨0, ?_⟩
      rw [map_zero, eq_comm, H2π_eq_zero_iff]
      exact mem_coboundaries₂_of_subsingleton z
    · obtain ⟨g, hgen, hg⟩ := exists_generator_sum_charCocycle χ hχ hm
      obtain ⟨a, ha, hmem⟩ := exists_sub_mem_coboundaries₂ χ g hgen hg z
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [cupCharClass_apply_charCocycle, H2π_eq_iff]
      exact hmem
theorem tateZeroToH2_bijective (χ : Additive G →+ AddCircle (1 : ℚ)) (hχ : Function.Injective χ) :
    Function.Bijective (tateZeroToH2 A χ).hom := by
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := tateZeroClass_surjective A x
    obtain ⟨b, rfl⟩ := tateZeroClass_surjective A y
    rw [tateZeroToH2_tateZeroClass, tateZeroToH2_tateZeroClass, ← sub_eq_zero, ← map_sub,
      cupCharClass_eq_zero_iff χ hχ] at hxy
    rw [← sub_eq_zero, ← map_sub]
    change ((tateCohomologyZeroIso ℤ G).app A).inv.hom (Submodule.Quotient.mk (a - b)) = 0
    rw [(Submodule.Quotient.mk_eq_zero _).2 hxy]
    exact map_zero _
  · obtain ⟨a, rfl⟩ := cupCharClass_surjective χ hχ y
    exact ⟨tateZeroClass A a, tateZeroToH2_tateZeroClass χ a⟩
noncomputable def tateZeroIsoH2 (A : Rep ℤ G) (χ : Additive G →+ AddCircle (1 : ℚ))
    (hχ : Function.Injective χ) : tateCohomology A 0 ≅ H2 A :=
  have : IsIso (tateZeroToH2 A χ) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (tateZeroToH2_bijective χ hχ)
  asIso (tateZeroToH2 A χ)
end Cyclic
end GroundTheory.ProfCoh


