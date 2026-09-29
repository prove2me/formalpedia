-- Prove2me | solution 1 for AlgebraicCurve.exists_place_residue_eq_algebraMap_of_maximalIdeal_eq_span_sup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0eeb8d7b-52c3-5f27-a304-2646aeb96857

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_place_residue_eq_algebraMap_of_maximalIdeal_eq_span_sup

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace ResiduePlace

variable {F : Type} [Field F]

theorem isUnit_iff_inv_mem (O : Subring F) (g : ↥O) :
    IsUnit g ↔ (g : F) ≠ 0 ∧ (g : F)⁻¹ ∈ O := by
  constructor
  · rintro ⟨u, rfl⟩
    have h2 : ((u : ↥O) : F) * (((u⁻¹ : (↥O)ˣ) : ↥O) : F) = 1 := congrArg Subtype.val u.mul_inv
    have hne : ((u : ↥O) : F) ≠ 0 := fun h0 => by rw [h0, zero_mul] at h2; exact zero_ne_one h2
    exact ⟨hne, by rw [(eq_inv_of_mul_eq_one_right h2).symm]; exact Subtype.coe_prop _⟩
  · rintro ⟨hne, hinv⟩
    exact ⟨⟨g, ⟨(g : F)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hne), Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩

end ResiduePlace

theorem solution
    {k : Type} [Field k] {Fbar : Type} [Field Fbar] [Algebra k Fbar]
    {F : Type} [Field F]
    (B : ValuationSubring F) (res : ↥B →+* Fbar) (hres : Function.Surjective res)
    (hker : RingHom.ker res = maximalIdeal ↥B)
    (S : Subring F) (hSB : ∀ f : ↥S, (f : F) ∈ B) (hS : IsLocalRing ↥S)
    (χ₀ : ↥S →+* k) (hχ₀ : RingHom.ker χ₀ = maximalIdeal ↥S)
    (hconst : ∀ c : k, ∃ a : ↥S, χ₀ a = c ∧ res ⟨(a : F), hSB a⟩ = algebraMap k Fbar c)
    (𝔮 : Ideal ↥S) (h𝔮 : ∀ f : ↥S, f ∈ 𝔮 ↔ (⟨(f : F), hSB f⟩ : ↥B) ∈ maximalIdeal ↥B)
    (t : ↥S) (hmax : maximalIdeal ↥S = Ideal.span {t} ⊔ 𝔮) (hne : 𝔮 ≠ maximalIdeal ↥S)
    (hnoeth : IsNoetherianRing (↥S ⧸ 𝔮))
    (hfrac : ∀ b : ↥B, ∃ g h : ↥S, h ∉ 𝔮 ∧ (b : F) * (h : F) = (g : F)) :
    ∃ Q : Place k Fbar, Q.IsRational ∧
      (∀ Q' : Place k Fbar, (∀ f : ↥S, res ⟨(f : F), hSB f⟩ ∈ Q'.toValuationSubring) → Q' = Q) ∧
      (∀ f : ↥S, ∃ hm : res ⟨(f : F), hSB f⟩ ∈ Q.toValuationSubring,
        IsLocalRing.residue ↥Q.toValuationSubring ⟨res ⟨(f : F), hSB f⟩, hm⟩ =
          algebraMap k Q.ResidueField (χ₀ f)) ∧
      Q.ord (res ⟨(t : F), hSB t⟩) = 1 := by
  classical

  let j : ↥S →+* ↥B :=
    { toFun := fun f => ⟨(f : F), hSB f⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hj : ∀ f : ↥S, j f = ⟨(f : F), hSB f⟩ := fun _ => rfl
  let ρ : ↥S →+* Fbar := res.comp j
  have hρ : ∀ f : ↥S, ρ f = res ⟨(f : F), hSB f⟩ := fun _ => rfl
  have hkerρ : ∀ f : ↥S, ρ f = 0 ↔ f ∈ 𝔮 := by
    intro f
    rw [h𝔮, ← hker, RingHom.mem_ker]
    exact Iff.rfl
  have hkerρ' : RingHom.ker ρ = 𝔮 := by
    ext f; rw [RingHom.mem_ker, hkerρ]
  have h𝔮max : 𝔮 ≤ maximalIdeal ↥S := hmax ▸ le_sup_right
  have htmax : t ∈ maximalIdeal ↥S := hmax ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self t)
  have ht𝔮 : t ∉ 𝔮 := by
    intro ht
    apply hne
    apply le_antisymm h𝔮max
    rw [hmax]
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr ht) le_rfl
  have hρt : ρ t ≠ 0 := fun h => ht𝔮 ((hkerρ t).mp h)

  set Sbar := ↥S ⧸ 𝔮 with hSbar
  let π : ↥S →+* Sbar := Ideal.Quotient.mk 𝔮
  have hπsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  let ρbar : Sbar →+* Fbar := Ideal.Quotient.lift 𝔮 ρ (fun f hf => (hkerρ f).mpr hf)
  have hρbar : ∀ f : ↥S, ρbar (π f) = ρ f := fun f => Ideal.Quotient.lift_mk 𝔮 ρ _
  have hρbar_inj : Function.Injective ρbar := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨f, rfl⟩ := hπsurj x
    rw [hρbar, hkerρ] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  haveI : Nontrivial Sbar := Ideal.Quotient.nontrivial_iff.mpr (fun h => ht𝔮 (h ▸ Submodule.mem_top))
  haveI : IsLocalRing Sbar := IsLocalRing.of_surjective' π hπsurj
  haveI : IsNoetherianRing Sbar := hnoeth
  haveI : IsDomain Sbar := Function.Injective.isDomain ρbar hρbar_inj
  have hmemmax : ∀ f : ↥S, f ∈ maximalIdeal ↥S → ∃ g s : ↥S, s ∈ 𝔮 ∧ f = g * t + s := by
    intro f hf
    rw [hmax] at hf
    obtain ⟨a, ha, s, hs, rfl⟩ := Submodule.mem_sup.mp hf
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    exact ⟨g, s, hs, rfl⟩
  have hπt_nonunit : ¬ IsUnit (π t) := by
    intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨g, rfl⟩ := hπsurj y
    rw [← map_mul, ← map_one π] at hy
    have h1 : t * g - 1 ∈ 𝔮 := (Ideal.Quotient.eq).mp hy
    have h2 : (1 : ↥S) ∈ maximalIdeal ↥S := by
      have : (1 : ↥S) = t * g - (t * g - 1) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ htmax) (h𝔮max h1)
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 isUnit_one
  have hmaxbar : maximalIdeal Sbar = Ideal.span {π t} := by
    apply le_antisymm
    · intro x hx
      obtain ⟨f, rfl⟩ := hπsurj x
      have hf : f ∈ maximalIdeal ↥S := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact (IsLocalRing.mem_maximalIdeal _).mp hx (hu.map π)
      obtain ⟨g, s, hs, rfl⟩ := hmemmax f hf
      rw [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hs, add_zero]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [Ideal.span_singleton_le_iff_mem, IsLocalRing.mem_maximalIdeal]
      exact hπt_nonunit
  have hprinc : (maximalIdeal Sbar).IsPrincipal := ⟨⟨π t, by rw [hmaxbar, Ideal.submodule_span_eq]⟩⟩
  haveI hPIR : IsPrincipalIdealRing Sbar :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain Sbar).out 0 4).mpr hprinc
  haveI hVR : ValuationRing Sbar :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain Sbar).out 1 4).mpr hprinc

  have hmemrange : ∀ z : Fbar, z ∈ ρbar.range ↔ ∃ f : ↥S, ρ f = z := by
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨f, rfl⟩ := hπsurj x
      exact ⟨f, (hρbar f).symm⟩
    · rintro ⟨f, rfl⟩
      exact ⟨π f, hρbar f⟩
  let O : ValuationSubring Fbar :=
    { ρbar.range with
      mem_or_inv_mem' := by
        intro z
        change z ∈ ρbar.range ∨ z⁻¹ ∈ ρbar.range
        obtain ⟨b, rfl⟩ := hres z
        obtain ⟨g, h, hh, hbh⟩ := hfrac b
        have hbh' : b * j h = j g := Subtype.ext hbh
        have hres_bh : res b * ρ h = ρ g := by rw [hρ, hρ, ← hj, ← hj, ← map_mul, hbh']
        have hρh : ρ h ≠ 0 := fun h0 => hh ((hkerρ h).mp h0)
        obtain ⟨c, hc⟩ := ValuationRing.cond (π g) (π h)
        rcases hc with hc | hc
        ·
          right
          by_cases hg0 : ρ g = 0
          · rw [hg0, mul_eq_zero] at hres_bh
            rcases hres_bh with h0 | h0
            · rw [h0, inv_zero]; exact zero_mem _
            · exact absurd h0 hρh
          · have e1 : ρ g * ρbar c = ρ h := by rw [← hρbar g, ← map_mul, hc, hρbar]
            have e2 : res b = ρ g / ρ h := by rw [eq_div_iff hρh, hres_bh]
            rw [e2, inv_div]
            refine ⟨c, ?_⟩
            rw [eq_div_iff hg0, mul_comm, e1]
        ·
          left
          have e1 : ρ h * ρbar c = ρ g := by rw [← hρbar h, ← map_mul, hc, hρbar]
          refine ⟨c, ?_⟩
          apply mul_left_cancel₀ hρh
          rw [e1, ← hres_bh, mul_comm] }
  have hmemO : ∀ z : Fbar, z ∈ O ↔ ∃ f : ↥S, ρ f = z := fun z => hmemrange z
  clear_value O
  have hρmemO : ∀ f : ↥S, ρ f ∈ O := fun f => (hmemO _).mpr ⟨f, rfl⟩

  let eO : Sbar →+* ↥O := ρbar.codRestrict O (fun x => by
    obtain ⟨f, rfl⟩ := hπsurj x
    rw [hρbar]; exact hρmemO f)
  have heO : ∀ x : Sbar, ((eO x : ↥O) : Fbar) = ρbar x := fun _ => rfl
  have heO_inj : Function.Injective eO := fun x y hxy => hρbar_inj (by rw [← heO, ← heO, hxy])
  have heO_surj : Function.Surjective eO := by
    intro z
    obtain ⟨f, hf⟩ := (hmemO _).mp (SetLike.coe_mem z)
    exact ⟨π f, Subtype.ext (by rw [heO, hρbar, hf])⟩
  haveI : IsPrincipalIdealRing ↥O := IsPrincipalIdealRing.of_surjective eO heO_surj

  have hconstO : ∀ c : k, algebraMap k Fbar c ∈ O := by
    intro c
    obtain ⟨a, -, ha⟩ := hconst c
    exact (hmemO _).mpr ⟨a, ha⟩
  have hunitO : ∀ f : ↥S, IsUnit (⟨ρ f, hρmemO f⟩ : ↥O) ↔ f ∉ maximalIdeal ↥S := by
    intro f
    have e : (⟨ρ f, hρmemO f⟩ : ↥O) = eO (π f) := Subtype.ext (by rw [heO, hρbar])
    rw [e]
    constructor
    · intro hu hf
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      obtain ⟨y, rfl⟩ := heO_surj v
      rw [← map_mul, ← map_one eO] at hv
      have h1 : π f * y = 1 := heO_inj hv
      have h2 : IsUnit (π f) := IsUnit.of_mul_eq_one _ h1
      apply (IsLocalRing.mem_maximalIdeal _).mp _ h2
      rw [hmaxbar]
      obtain ⟨g, s, hs, rfl⟩ := hmemmax f hf
      rw [map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hs, add_zero]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · intro hf
      have hu : IsUnit f := by
        by_contra hnu; exact hf ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      exact (hu.map π).map eO
  have hOtop : O ≠ ⊤ := by
    intro htop
    have hmem : (ρ t)⁻¹ ∈ O := htop ▸ ValuationSubring.mem_top _
    have hu : IsUnit (⟨ρ t, hρmemO t⟩ : ↥O) :=
      (ResiduePlace.isUnit_iff_inv_mem O.toSubring ⟨ρ t, hρmemO t⟩).mpr ⟨hρt, hmem⟩
    exact (hunitO t).mp hu htmax

  obtain ⟨Q, rfl⟩ : ∃ Q : Place k Fbar, Q.toValuationSubring = O :=
    ⟨{ toValuationSubring := O
       algebraMap_mem' := hconstO
       ne_top' := hOtop
       isPrincipalIdealRing' := inferInstance }, rfl⟩

  have hmemmaxO : ∀ f : ↥S, f ∈ maximalIdeal ↥S →
      (⟨ρ f, hρmemO f⟩ : ↥Q.toValuationSubring) ∈
        Ideal.span {(⟨ρ t, hρmemO t⟩ : ↥Q.toValuationSubring)} := by
    intro f hf
    obtain ⟨g, s, hs, rfl⟩ := hmemmax f hf
    have hs0 : ρ s = 0 := (hkerρ s).mpr hs
    have e : (⟨ρ (g * t + s), hρmemO _⟩ : ↥Q.toValuationSubring) =
        ⟨ρ g, hρmemO g⟩ * ⟨ρ t, hρmemO t⟩ :=
      Subtype.ext (by
        change ρ (g * t + s) = ρ g * ρ t
        rw [map_add, map_mul, hs0, add_zero])
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hmaxO : maximalIdeal ↥Q.toValuationSubring =
      Ideal.span {(⟨ρ t, hρmemO t⟩ : ↥Q.toValuationSubring)} := by
    apply le_antisymm
    · intro z hz
      obtain ⟨f, hf⟩ := (hmemO _).mp (SetLike.coe_mem z)
      have ez : z = ⟨ρ f, hρmemO f⟩ := Subtype.ext hf.symm
      rw [ez] at hz ⊢
      have hf' : f ∈ maximalIdeal ↥S := by
        by_contra hnf
        exact (IsLocalRing.mem_maximalIdeal _).mp hz ((hunitO f).mpr hnf)
      exact hmemmaxO f hf'
    · rw [Ideal.span_singleton_le_iff_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunitO]
      exact fun h => h htmax
  have hirr : Irreducible (⟨ρ t, hρmemO t⟩ : ↥Q.toValuationSubring) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
      (fun h0 => hρt (congrArg Subtype.val h0)) hmaxO

  have hresidue : ∀ f : ↥S,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨ρ f, hρmemO f⟩ = algebraMap k Q.ResidueField (χ₀ f) := by
    intro f
    obtain ⟨a, ha, hares⟩ := hconst (χ₀ f)
    have hfa : f - a ∈ maximalIdeal ↥S := by
      rw [← hχ₀, RingHom.mem_ker, map_sub, ha, sub_self]
    have hmem : (⟨ρ (f - a), hρmemO _⟩ : ↥Q.toValuationSubring) ∈ maximalIdeal ↥Q.toValuationSubring := by
      rw [hmaxO]; exact hmemmaxO _ hfa
    have e1 : (⟨ρ (f - a), hρmemO _⟩ : ↥Q.toValuationSubring) = ⟨ρ f, hρmemO f⟩ - ⟨ρ a, hρmemO a⟩ :=
      Subtype.ext (by change ρ (f - a) = ρ f - ρ a; rw [map_sub])
    rw [e1, ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hmem
    rw [hmem, IsScalarTower.algebraMap_apply k ↥Q.toValuationSubring Q.ResidueField]
    change IsLocalRing.residue _ (⟨ρ a, hρmemO a⟩ : ↥Q.toValuationSubring) =
      IsLocalRing.residue _ (algebraMap k ↥Q.toValuationSubring (χ₀ f))
    congr 1
    apply Subtype.ext
    rw [Place.coe_algebraMap]
    exact hares
  refine ⟨Q, ?_, ?_, fun f => ⟨hρmemO f, hresidue f⟩, Q.ord_coe_irreducible hirr⟩
  ·
    intro x
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨f, hf⟩ := (hmemO _).mp (SetLike.coe_mem z)
    have ez : z = ⟨ρ f, hρmemO f⟩ := Subtype.ext hf.symm
    exact ⟨χ₀ f, by rw [ez, hresidue]⟩
  ·
    intro Q' hQ'
    have hle : ∀ z : Fbar, z ∈ Q.toValuationSubring → z ∈ Q'.toValuationSubring := by
      intro z hz
      obtain ⟨f, rfl⟩ := (hmemO z).mp hz
      exact hQ' f
    apply Place.ext

    by_contra hneq
    have hlt : ∃ z : Fbar, z ∈ Q'.toValuationSubring ∧ z ∉ Q.toValuationSubring := by
      by_contra hall
      push_neg at hall
      exact hneq (le_antisymm (fun z hz => hall z hz) (fun z hz => hle z hz))
    obtain ⟨z, hzQ', hzO⟩ := hlt
    have hz0 : z ≠ 0 := fun h0 => hzO (h0 ▸ zero_mem _)
    have hzi : z⁻¹ ∈ Q.toValuationSubring := (Q.toValuationSubring.mem_or_inv_mem z).resolve_left hzO
    have hzi_max : (⟨z⁻¹, hzi⟩ : ↥Q.toValuationSubring) ∈ maximalIdeal ↥Q.toValuationSubring := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply hzO
      have := ((ResiduePlace.isUnit_iff_inv_mem Q.toValuationSubring.toSubring ⟨z⁻¹, hzi⟩).mp hu).2
      rwa [inv_inv] at this
    rw [hmaxO] at hzi_max
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hzi_max
    have hw' : (w : Fbar) * ρ t = z⁻¹ := congrArg Subtype.val hw
    have htinv : (ρ t)⁻¹ ∈ Q'.toValuationSubring := by
      have e : (ρ t)⁻¹ = z * (w : Fbar) := by
        have h3 : z * (w : Fbar) * ρ t = 1 := by rw [mul_assoc, hw', mul_inv_cancel₀ hz0]
        exact (eq_inv_of_mul_eq_one_left h3).symm
      rw [e]
      exact mul_mem hzQ' (hle _ w.2)

    apply Q'.ne_top'
    apply eq_top_iff.mpr
    intro y _
    by_cases hyO : y ∈ Q.toValuationSubring
    · exact hle y hyO
    · have hy0 : y ≠ 0 := fun h0 => hyO (h0 ▸ zero_mem _)
      have hyi : y⁻¹ ∈ Q.toValuationSubring := (Q.toValuationSubring.mem_or_inv_mem y).resolve_left hyO

      have hyi0 : (⟨y⁻¹, hyi⟩ : ↥Q.toValuationSubring) ≠ 0 :=
        fun h0 => inv_ne_zero hy0 (congrArg Subtype.val h0)
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hyi0 hirr
      have hu' : y⁻¹ = ((u : ↥Q.toValuationSubring) : Fbar) * (ρ t) ^ n := by
        have := congrArg Subtype.val hu
        simpa using this
      have h1 : ((u : ↥Q.toValuationSubring) : Fbar) * (((u⁻¹ : (↥Q.toValuationSubring)ˣ) :
          ↥Q.toValuationSubring) : Fbar) = 1 := congrArg Subtype.val u.mul_inv
      have e : y = ((u⁻¹ : (↥Q.toValuationSubring)ˣ) : ↥Q.toValuationSubring) * ((ρ t)⁻¹) ^ n := by
        rw [← inv_inv y, hu', mul_inv, inv_pow, (eq_inv_of_mul_eq_one_right h1)]
      rw [e]
      exact mul_mem (hle _ (SetLike.coe_mem _)) (pow_mem htinv n)

end S_AlgebraicCurve_exists_place_residue_eq_algebraMap_of_maximalIdeal_eq_span_sup
end P2MW
export P2MW.S_AlgebraicCurve_exists_place_residue_eq_algebraMap_of_maximalIdeal_eq_span_sup (solution)
