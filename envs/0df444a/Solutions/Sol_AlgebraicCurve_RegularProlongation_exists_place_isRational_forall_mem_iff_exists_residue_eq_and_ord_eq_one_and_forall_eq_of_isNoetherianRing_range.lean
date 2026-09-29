-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/05e52ec7-6c0b-5571-89a3-bf49ab6fd406

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range

set_option autoImplicit false
set_option linter.unnecessarySimpa false

open AlgebraicCurve IsLocalRing

namespace K4pBody

theorem isDVR_of_maximalIdeal_eq_span {D : Type*} [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [IsLocalRing D] (t : D) (ht0 : t ≠ 0) (hmax : maximalIdeal D = Ideal.span {t}) :
    IsDiscreteValuationRing D := by
  have hnf : ¬ IsField D := by
    intro hF
    have hbot : maximalIdeal D = ⊥ := IsLocalRing.isField_iff_maximalIdeal_eq.mp hF
    have : t ∈ maximalIdeal D := hmax.symm ▸ Ideal.subset_span (Set.mem_singleton t)
    rw [hbot] at this
    exact ht0 ((Submodule.mem_bot D).mp this)
  have hprinc : (maximalIdeal D).IsPrincipal := ⟨⟨t, by rw [hmax]⟩⟩
  exact ((IsDiscreteValuationRing.TFAE D hnf).out 0 4).mpr hprinc

variable {K Fbar : Type*} [Field K] [Field Fbar] [Algebra K Fbar]

theorem ord_pos_of_not_isUnit (x₁ : Place K Fbar) (w : ↥x₁.toValuationSubring) (hw0 : w ≠ 0)
    (hw : ¬ IsUnit w) : 0 < x₁.ord (w : Fbar) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥x₁.toValuationSubring
  obtain ⟨n, u, hwu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    apply hw
    rw [hwu, pow_zero, mul_one]
    exact Units.isUnit u
  have hval : (w : Fbar) = ((u : ↥x₁.toValuationSubring) : Fbar) * ((ϖ : Fbar) ^ (n : ℤ)) := by
    rw [zpow_natCast, hwu]
    simp
  rw [hval, x₁.ord_unit_smul_zpow u hϖ (n : ℤ)]
  exact_mod_cast Nat.pos_of_ne_zero hn

theorem place_eq_of_forall_mem (x₁ Q' : Place K Fbar)
    (hle : ∀ v : Fbar, v ∈ x₁.toValuationSubring → v ∈ Q'.toValuationSubring)
    (hfrac : ∀ q : Fbar, ∃ a b : Fbar, a ∈ x₁.toValuationSubring ∧ b ∈ x₁.toValuationSubring ∧
      b ≠ 0 ∧ q * b = a) : Q' = x₁ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥x₁.toValuationSubring
  have hϖ0 : (ϖ : Fbar) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  apply Place.ext
  apply le_antisymm
  · intro z hz
    by_contra hzV
    have hz0 : z ≠ 0 := by rintro rfl; exact hzV (zero_mem _)
    have hzi : z⁻¹ ∈ x₁.toValuationSubring :=
      (x₁.toValuationSubring.mem_or_inv_mem z).resolve_left hzV
    have hw0 : (⟨z⁻¹, hzi⟩ : ↥x₁.toValuationSubring) ≠ 0 :=
      fun h => (inv_ne_zero hz0) (congrArg Subtype.val h)
    have hwu : ¬ IsUnit (⟨z⁻¹, hzi⟩ : ↥x₁.toValuationSubring) := by
      intro hu
      obtain ⟨w', hw'⟩ := hu.exists_right_inv
      apply hzV
      have : (w' : Fbar) = z := by
        have h1 := congrArg Subtype.val hw'
        change z⁻¹ * (w' : Fbar) = 1 at h1
        rw [inv_mul_eq_one₀ hz0] at h1
        exact h1.symm
      rw [← this]; exact w'.2
    obtain ⟨n, u, hwun⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hϖ
    have hn : n ≠ 0 := by
      rintro rfl; apply hwu; rw [hwun, pow_zero, mul_one]; exact Units.isUnit u

    have htinv : (ϖ : Fbar)⁻¹ ∈ Q'.toValuationSubring := by
      have h1 : z⁻¹ = ((u : ↥x₁.toValuationSubring) : Fbar) * (ϖ : Fbar) ^ n := by
        have := congrArg Subtype.val hwun
        simpa using this
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have h3 : z * (((u : ↥x₁.toValuationSubring) : Fbar) * ((ϖ : Fbar) ^ k * (ϖ : Fbar))) = 1 := by
        rw [← pow_succ, ← h1, mul_inv_cancel₀ hz0]
      have h2 : (ϖ : Fbar)⁻¹ = z * ((u : ↥x₁.toValuationSubring) : Fbar) * (ϖ : Fbar) ^ k := by
        symm
        apply eq_inv_of_mul_eq_one_left
        calc z * ↑↑u * (ϖ : Fbar) ^ k * ↑ϖ = z * (↑↑u * ((ϖ : Fbar) ^ k * ↑ϖ)) := by ring
          _ = 1 := h3
      rw [h2]
      exact mul_mem (mul_mem hz (hle _ (u : ↥x₁.toValuationSubring).2)) (pow_mem (hle _ ϖ.2) _)

    apply Q'.ne_top'
    apply eq_top_iff.mpr
    intro q _
    obtain ⟨a, b, ha, hb, hb0, hq⟩ := hfrac q
    have hwb0 : (⟨b, hb⟩ : ↥x₁.toValuationSubring) ≠ 0 := fun h => hb0 (congrArg Subtype.val h)
    obtain ⟨m, u', hbu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hwb0 hϖ
    have hbval : b = ((u' : ↥x₁.toValuationSubring) : Fbar) * (ϖ : Fbar) ^ m := by
      have := congrArg Subtype.val hbu
      simpa using this
    have hq2 : q = a / b := (eq_div_iff hb0).mpr hq
    have hu'inv : (((u'⁻¹ : (↥x₁.toValuationSubring)ˣ) : ↥x₁.toValuationSubring) : Fbar) =
        (((u' : ↥x₁.toValuationSubring) : Fbar))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by
        rw [← MulMemClass.coe_mul, Units.inv_mul, OneMemClass.coe_one])
    have hq' : q = a * (((u'⁻¹ : (↥x₁.toValuationSubring)ˣ) : ↥x₁.toValuationSubring) : Fbar) *
        ((ϖ : Fbar)⁻¹) ^ m := by
      rw [hu'inv, inv_pow, mul_assoc, ← mul_inv, ← hbval, ← div_eq_mul_inv]
      exact hq2
    rw [hq']
    exact mul_mem (mul_mem (hle _ ha) (hle _ (Subtype.coe_prop _))) (pow_mem htinv _)
  · intro z hz
    exact hle z hz

end K4pBody

open K4pBody

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (𝒩 : Subring F) [IsLocalRing ↥𝒩]
    (h𝒩 : ∀ f : F, f ∈ 𝒩 → f ∈ R.integers)
    (hA : ∀ a : ↥A, algebraMap L F (a : L) ∈ 𝒩)
    (hres : ∀ g : ↥𝒩, ∃ a : ↥A, ¬ IsUnit (g - ⟨algebraMap L F (a : L), hA a⟩))
    (y : ↥𝒩) (hyu : ¬ IsUnit y) (hy0 : R.residue ⟨(y : F), h𝒩 y y.2⟩ ≠ 0)
    (hmax : ∀ f : ↥𝒩, ¬ IsUnit f →
      ∃ g h : ↥𝒩, R.residue ⟨(h : F), h𝒩 h h.2⟩ = 0 ∧ f = y * g + h)
    (hnoeth : IsNoetherianRing
      ↥(R.residue.comp (Subring.inclusion (show 𝒩 ≤ R.integers.toSubring from fun f hf => h𝒩 f hf))).range)
    (hfrac : ∀ z : Fbar, ∃ f g : ↥𝒩, R.residue ⟨(g : F), h𝒩 g g.2⟩ ≠ 0 ∧
      z * R.residue ⟨(g : F), h𝒩 g g.2⟩ = R.residue ⟨(f : F), h𝒩 f f.2⟩) :
    ∃ x₁ : Place (ResidueField A) Fbar,
      x₁.IsRational ∧
      (∀ z : Fbar, z ∈ x₁.toValuationSubring ↔ ∃ f : ↥𝒩, R.residue ⟨(f : F), h𝒩 f f.2⟩ = z) ∧
      (∀ f : ↥𝒩, ¬ IsUnit f → R.residue ⟨(f : F), h𝒩 f f.2⟩ ∈ x₁.toValuationSubring.nonunits) ∧
      (∀ f : ↥𝒩, ¬ IsUnit f → R.residue ⟨(f : F), h𝒩 f f.2⟩ ≠ 0 →
        0 < x₁.ord (R.residue ⟨(f : F), h𝒩 f f.2⟩)) ∧
      x₁.ord (R.residue ⟨(y : F), h𝒩 y y.2⟩) = 1 ∧
      (∀ (f : ↥𝒩) (a : ↥A), ¬ IsUnit (f - ⟨algebraMap L F (a : L), hA a⟩) →
        ∀ m : R.residue ⟨(f : F), h𝒩 f f.2⟩ ∈ x₁.toValuationSubring,
          IsLocalRing.residue ↥x₁.toValuationSubring ⟨_, m⟩ =
            algebraMap (ResidueField A) x₁.ResidueField (IsLocalRing.residue ↥A a)) ∧
      (∀ Q' : Place (ResidueField A) Fbar,
        (∀ f : ↥𝒩, R.residue ⟨(f : F), h𝒩 f f.2⟩ ∈ Q'.toValuationSubring) → Q' = x₁) := by
  classical

  set ψ : ↥𝒩 →+* Fbar :=
    R.residue.comp (Subring.inclusion (show 𝒩 ≤ R.integers.toSubring from fun f hf => h𝒩 f hf)) with hψdef
  have hψ : ∀ f : ↥𝒩, ψ f = R.residue ⟨(f : F), h𝒩 f f.2⟩ := fun f => rfl
  set D : Subring Fbar := ψ.range with hDdef
  haveI hDnoeth : IsNoetherianRing ↥D := hnoeth

  let ψ' : ↥𝒩 →+* ↥D := ψ.rangeRestrict
  have hψ'surj : Function.Surjective ψ' := ψ.rangeRestrict_surjective
  have hψ'val : ∀ f : ↥𝒩, ((ψ' f : ↥D) : Fbar) = ψ f := fun f => rfl

  have hker : ∀ f : ↥𝒩, ψ f = 0 → f ∈ maximalIdeal ↥𝒩 := by
    intro f hf
    have : RingHom.ker ψ ≠ ⊤ := by
      intro htop
      have h1 : (1 : ↥𝒩) ∈ RingHom.ker ψ := htop.symm ▸ Submodule.mem_top
      rw [RingHom.mem_ker, map_one] at h1
      exact one_ne_zero h1
    exact IsLocalRing.le_maximalIdeal this ((RingHom.mem_ker).mpr hf)

  have hunit : ∀ f : ↥𝒩, IsUnit (ψ' f) → IsUnit f := by
    intro f hf
    obtain ⟨w, hw⟩ := hf.exists_right_inv
    obtain ⟨g, rfl⟩ := hψ'surj w
    rw [← map_mul] at hw

    have hk : ψ (f * g - 1) = 0 := by
      have := congrArg (fun d : ↥D => (d : Fbar)) hw
      simp only [hψ'val, OneMemClass.coe_one] at this
      rw [map_sub, map_one, this, sub_self]
    have hm := hker _ hk
    by_contra hfu
    have hfg : f * g ∈ maximalIdeal ↥𝒩 := by
      rw [IsLocalRing.mem_maximalIdeal]
      intro hu
      exact hfu (isUnit_of_mul_isUnit_left hu)
    have : (1 : ↥𝒩) ∈ maximalIdeal ↥𝒩 := by
      have := Ideal.sub_mem _ hfg hm
      simpa using this
    exact (IsLocalRing.maximalIdeal.isMaximal ↥𝒩).ne_top
      ((Ideal.eq_top_iff_one _).mpr this)
  haveI hDloc : IsLocalRing ↥D := IsLocalRing.of_surjective' ψ' hψ'surj

  let t : ↥D := ψ' y
  have htval : (t : Fbar) = R.residue ⟨(y : F), h𝒩 y y.2⟩ := rfl
  have ht0 : t ≠ 0 := by
    intro h
    apply hy0
    rw [← htval, h]; rfl
  have htmax : maximalIdeal ↥D = Ideal.span {t} := by
    apply le_antisymm
    · intro d hd
      obtain ⟨f, rfl⟩ := hψ'surj d
      have hfu : ¬ IsUnit f := fun hu => (IsLocalRing.mem_maximalIdeal _).mp hd (hu.map ψ')
      obtain ⟨g, h, hh, hfe⟩ := hmax f hfu
      rw [Ideal.mem_span_singleton']
      refine ⟨ψ' g, ?_⟩
      apply Subtype.ext
      simp only [hfe, map_add, map_mul, Subring.coe_add, Subring.coe_mul, hψ'val]
      rw [hψ h, hh, add_zero, mul_comm]
      rfl
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (fun hu => hyu (hunit y hu))
  haveI hDVR : IsDiscreteValuationRing ↥D := isDVR_of_maximalIdeal_eq_span t ht0 htmax

  haveI hDfrac : IsFractionRing ↥D Fbar := by
    refine IsFractionRing.of_field (R := ↥D) (K := Fbar) ?_
    intro z
    obtain ⟨f, g, hg0, hz⟩ := hfrac z
    refine ⟨ψ' f, ψ' g, ?_⟩
    simp only [← hψ] at hg0 hz
    change z = ψ f / ψ g
    rw [eq_div_iff hg0, hz]
  haveI hDval : ValuationRing ↥D := ((IsDiscreteValuationRing.TFAE ↥D
    (IsDiscreteValuationRing.not_isField ↥D)).out 0 1).mp hDVR

  let V : ValuationSubring Fbar :=
    { toSubring := D
      mem_or_inv_mem' := by
        intro z
        rcases ValuationRing.isInteger_or_isInteger ↥D z with ⟨d, hd⟩ | ⟨d, hd⟩
        · exact Or.inl (hd ▸ d.2)
        · exact Or.inr (hd ▸ d.2) }
  have hVmem : ∀ z : Fbar, z ∈ V ↔ z ∈ D := fun z => Iff.rfl

  have hconst : ∀ a : ↥A, algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) =
      ψ ⟨algebraMap L F (a : L), hA a⟩ := by
    intro a
    rw [hψ, ← R.residue_algebraMap a]
  have hVconst : ∀ c : ResidueField ↥A, algebraMap (ResidueField ↥A) Fbar c ∈ V := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    rw [hVmem, hconst a]
    exact ⟨_, rfl⟩
  have hVnetop : V ≠ ⊤ := by
    intro htop
    have hmem : (R.residue ⟨(y : F), h𝒩 y y.2⟩)⁻¹ ∈ V := htop.symm ▸ ValuationSubring.mem_top _
    rw [hVmem] at hmem
    obtain ⟨g, hg⟩ := hmem
    apply hyu
    apply hunit
    refine isUnit_iff_exists_inv.mpr ⟨ψ' g, ?_⟩
    apply Subtype.ext
    change ψ y * ψ g = 1
    rw [hg, hψ, mul_inv_cancel₀ hy0]

  let eVD0 : ↥V ≃+* ↥D :=
    { toFun := fun w => ⟨(w : Fbar), w.2⟩
      invFun := fun d => ⟨(d : Fbar), d.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  haveI hVpir : IsPrincipalIdealRing ↥V :=
    IsPrincipalIdealRing.of_surjective (eVD0.symm : ↥D →+* ↥V) eVD0.symm.surjective

  let x₁ : Place (ResidueField ↥A) Fbar :=
    { toValuationSubring := V
      algebraMap_mem' := hVconst
      ne_top' := hVnetop
      isPrincipalIdealRing' := hVpir }
  have hx₁V : x₁.toValuationSubring = V := rfl
  clear_value x₁
  have hmemx : ∀ z : Fbar, z ∈ x₁.toValuationSubring ↔ ∃ f : ↥𝒩, ψ f = z := by
    intro z; rw [hx₁V]; exact Iff.rfl
  have hmemr : ∀ f : ↥𝒩, R.residue ⟨(f : F), h𝒩 f f.2⟩ ∈ x₁.toValuationSubring :=
    fun f => (hmemx _).mpr ⟨f, hψ f⟩
  let eVD : ↥x₁.toValuationSubring ≃+* ↥D :=
    { toFun := fun w => ⟨(w : Fbar), (hmemx _).mp w.2⟩
      invFun := fun d => ⟨(d : Fbar), (hmemx _).mpr d.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have heVD : ∀ w : ↥x₁.toValuationSubring, ((eVD w : ↥D) : Fbar) = (w : Fbar) := fun _ => rfl
  have hVunit : ∀ w : ↥x₁.toValuationSubring, IsUnit w ↔ IsUnit (eVD w) :=
    fun w => ⟨fun h => h.map eVD, fun h => by simpa using h.map eVD.symm⟩

  let tV : ↥x₁.toValuationSubring := ⟨R.residue ⟨(y : F), h𝒩 y y.2⟩, hmemr y⟩
  have htV : eVD tV = t := Subtype.ext rfl
  have htV0 : tV ≠ 0 := by
    intro h; apply ht0; rw [← htV, h, map_zero]

  have hVnonunit : ∀ (f : ↥𝒩) (hf : ¬ IsUnit f),
      ¬ IsUnit (⟨R.residue ⟨(f : F), h𝒩 f f.2⟩, hmemr f⟩ : ↥x₁.toValuationSubring) := by
    intro f hf hu
    rw [hVunit] at hu
    exact hf (hunit f (by convert hu using 1; rfl))
  have hVmax : maximalIdeal ↥x₁.toValuationSubring = Ideal.span {tV} := by
    apply le_antisymm
    · intro w hw
      have hw' : eVD w ∈ maximalIdeal ↥D := by
        rw [IsLocalRing.mem_maximalIdeal] at hw ⊢
        exact fun hu => hw ((hVunit w).mpr hu)
      rw [htmax, Ideal.mem_span_singleton'] at hw'
      obtain ⟨c, hc⟩ := hw'
      rw [Ideal.mem_span_singleton']
      refine ⟨eVD.symm c, ?_⟩
      apply eVD.injective
      rw [map_mul, RingEquiv.apply_symm_apply, htV, hc]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (hVnonunit y hyu)
  have htVirr : Irreducible tV :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal tV htV0 hVmax

  have halgres : ∀ c : ResidueField ↥A, algebraMap (ResidueField ↥A) x₁.ResidueField c =
      IsLocalRing.residue ↥x₁.toValuationSubring (algebraMap (ResidueField ↥A) ↥x₁.toValuationSubring c) :=
    fun c => rfl
  have heval : ∀ (f : ↥𝒩) (a : ↥A), ¬ IsUnit (f - ⟨algebraMap L F (a : L), hA a⟩) →
      ∀ m : R.residue ⟨(f : F), h𝒩 f f.2⟩ ∈ x₁.toValuationSubring,
        IsLocalRing.residue ↥x₁.toValuationSubring ⟨_, m⟩ =
          algebraMap (ResidueField ↥A) x₁.ResidueField (IsLocalRing.residue ↥A a) := by
    intro f a hfa m
    rw [halgres, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have key : (⟨_, m⟩ : ↥x₁.toValuationSubring) -
        algebraMap (ResidueField ↥A) ↥x₁.toValuationSubring (IsLocalRing.residue ↥A a) =
        ⟨R.residue ⟨((f - ⟨algebraMap L F (a : L), hA a⟩ : ↥𝒩) : F),
          h𝒩 _ (f - ⟨algebraMap L F (a : L), hA a⟩).2⟩, hmemr _⟩ := by
      apply Subtype.ext
      change R.residue ⟨(f : F), h𝒩 f f.2⟩ - algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) = _
      rw [hconst a]
      show ψ f - ψ ⟨algebraMap L F (a : L), hA a⟩ = ψ (f - ⟨algebraMap L F (a : L), hA a⟩)
      rw [map_sub]
    rw [key]
    exact hVnonunit _ hfa
  refine ⟨x₁, ?_, ?_, ?_, ?_, ?_, heval, ?_⟩
  ·
    intro r
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨f, hf⟩ : ∃ f : ↥𝒩, ψ f = (w : Fbar) := (hmemx _).mp w.2
    obtain ⟨a, ha⟩ := hres f
    refine ⟨IsLocalRing.residue ↥A a, ?_⟩
    have hw : w = ⟨_, hmemr f⟩ := Subtype.ext (by rw [← hf]; rfl)
    rw [hw, heval f a ha (hmemr f)]
  ·
    intro z
    rw [hmemx]
    exact ⟨fun ⟨f, hf⟩ => ⟨f, (hψ f) ▸ hf⟩, fun ⟨f, hf⟩ => ⟨f, (hψ f).symm ▸ hf⟩⟩
  ·
    intro f hf
    have := hVnonunit f hf
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal,
      ← ValuationSubring.coe_mem_nonunits_iff] at this
    exact this
  ·
    intro f hf hf0
    exact ord_pos_of_not_isUnit x₁ ⟨R.residue ⟨(f : F), h𝒩 f f.2⟩, hmemr f⟩
      (fun h => hf0 (congrArg Subtype.val h)) (hVnonunit f hf)
  ·
    exact x₁.ord_coe_irreducible htVirr
  ·
    intro Q' hQ'
    have hVQ : ∀ v : Fbar, v ∈ x₁.toValuationSubring → v ∈ Q'.toValuationSubring := by
      intro v hv
      obtain ⟨f, rfl⟩ : ∃ f : ↥𝒩, ψ f = v := (hmemx _).mp hv
      rw [hψ]; exact hQ' f
    refine place_eq_of_forall_mem x₁ Q' hVQ ?_
    intro q
    obtain ⟨f, g, hg0, hq⟩ := hfrac q
    exact ⟨_, _, hmemr f, hmemr g, hg0, hq⟩

end S_AlgebraicCurve_RegularProlongation_exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range (solution)
