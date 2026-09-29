-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_laurentChart_isCompletionAlong_of_powerSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7cce80c9-aa07-51b9-b25b-a64bee470b3c

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_of_powerSeries

universe u v

open CategoryTheory

open AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ AlgebraicGeometry.Spec (.of R))
    {ι : Type v} (σ : ι → (AlgebraicGeometry.Spec (.of R) ⟶ X)) (h : 𝒱.IsSectional c σ) (i : ι)
    (θ : (𝒱.cover c).A0 →+* PowerSeries R) (hθC : ∀ r : R, θ (algebraMap R (𝒱.cover c).A0 r) = PowerSeries.C r)
    (hθ0 : ∀ (n : ℕ) (a : (𝒱.cover c).A0), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔
      a ∈ RingHom.ker (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom
        (σ i) (h.comp_eq i) (h.range_subset i)).toRingHom ^ n)
    (hθs : ∀ (n : ℕ) (p : PowerSeries R), ∃ a : (𝒱.cover c).A0, ∀ k : ℕ, k < n →
      PowerSeries.coeff k (θ a) = PowerSeries.coeff k p) :
    ∃ Λ : (𝒱.cover c).LaurentChart,
      (∀ a : (𝒱.cover c).A0, Λ.expand ((𝒱.cover c).ρ0 a) = HahnSeries.ofPowerSeries ℤ R (θ a)) ∧
        Λ.IsCompletionAlong (𝒱.cover c).ρ0
          (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom (σ i) (h.comp_eq i) (h.range_subset i)) := by
  classical
  have hU0 : IsAffineOpen 𝒱.U0 := 𝒱.isAffineOpen_U0

  have hle : ∀ j : ι, (⊤ : (Spec (.of R)).Opens) ≤ (σ j) ⁻¹ᵁ 𝒱.U0 := fun j x _ => h.range_subset j ⟨x, rfl⟩
  let e : ∀ j : ι, Γ(X, 𝒱.U0) →+* R := fun j =>
    ((σ j).appLE 𝒱.U0 ⊤ (hle j) ≫ (Scheme.ΓSpecIso (.of R)).hom).hom
  have he : ∀ j : ι,
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ j) (h.comp_eq j) (h.range_subset j)).toRingHom = e j :=
    fun j => rfl
  have he_app : ∀ (j : ι) (a : Γ(X, 𝒱.U0)),
      e j a = (Scheme.ΓSpecIso (.of R)).hom.hom (((σ j).appLE 𝒱.U0 ⊤ (hle j)).hom a) :=
    fun j a => rfl
  have hsurj : ∀ j : ι, Function.Surjective (e j) := fun j r =>
    ⟨((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ 𝒱.U0 le_top).hom r,
      (Scheme.TwoAffineOpenCover.sectionAlgHom (σ j) (h.comp_eq j) (h.range_subset j)).commutes r⟩

  have hθ0' : ∀ (n : ℕ) (a : Γ(X, 𝒱.U0)), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔
      a ∈ RingHom.ker (e i) ^ n := hθ0
  have hθs' : ∀ (n : ℕ) (p : PowerSeries R), ∃ a : Γ(X, 𝒱.U0), ∀ k : ℕ, k < n →
      PowerSeries.coeff k (θ a) = PowerSeries.coeff k p := hθs

  have char : ∀ (j : ι) (y : ↥(Spec (.of R))) (𝔮 : ↥(Spec Γ(X, 𝒱.U0))),
      hU0.fromSpec.base 𝔮 = (σ j).base y → ∀ a : Γ(X, 𝒱.U0), a ∈ 𝔮.asIdeal ↔ e j a ∈ y.asIdeal := by
    intro j y 𝔮 hq a
    have h1 : a ∉ 𝔮.asIdeal ↔ hU0.fromSpec.base 𝔮 ∈ X.basicOpen a := by
      rw [← PrimeSpectrum.mem_basicOpen]
      change 𝔮 ∈ PrimeSpectrum.basicOpen a ↔ 𝔮 ∈ hU0.fromSpec ⁻¹ᵁ X.basicOpen a
      rw [hU0.fromSpec_preimage_basicOpen]
      exact Iff.rfl
    have h2 : (σ j).base y ∈ X.basicOpen a ↔ e j a ∉ y.asIdeal := by
      rw [he_app, ← PrimeSpectrum.mem_basicOpen, ← basicOpen_eq_of_affine, Iso.hom_inv_id_apply]
      change y ∈ (σ j) ⁻¹ᵁ X.basicOpen a ↔ _
      rw [Scheme.preimage_basicOpen, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res]
      exact ⟨fun hy => ⟨trivial, hy⟩, fun hy => hy.2⟩
    have h3 := h1.trans (hq ▸ h2)
    constructor
    · intro ha
      by_contra hb
      exact (h3.mpr hb) ha
    · intro hb
      by_contra ha
      exact (h3.mp ha) hb

  have step1 : ∀ (j : ι) (y : ↥(Spec (.of R))) (𝔮 : ↥(Spec Γ(X, 𝒱.U0))),
      hU0.fromSpec.base 𝔮 = (σ j).base y → RingHom.ker (e j) ≤ 𝔮.asIdeal := by
    intro j y 𝔮 hq a ha
    rw [char j y 𝔮 hq a]
    rw [RingHom.mem_ker] at ha
    rw [ha]
    exact Ideal.zero_mem _

  have step1' : ∀ (j : ι) (𝔭 : ↥(Spec Γ(X, 𝒱.U0))), RingHom.ker (e j) ≤ 𝔭.asIdeal →
      hU0.fromSpec.base 𝔭 ∈ Set.range (σ j).base := by
    intro j 𝔭 hp'
    have hsurj := hsurj j
    haveI hprime : (Ideal.map (e j) 𝔭.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hsurj hp'
    let y : ↥(Spec (.of R)) := ⟨Ideal.map (e j) 𝔭.asIdeal, hprime⟩
    obtain ⟨𝔮, hq⟩ : (σ j).base y ∈ Set.range hU0.fromSpec.base := by
      rw [hU0.range_fromSpec]
      exact h.range_subset j ⟨y, rfl⟩
    refine ⟨y, ?_⟩
    rw [← hq]
    congr 1
    refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
    rw [char j y 𝔮 hq a]
    change e j a ∈ Ideal.map (e j) 𝔭.asIdeal ↔ a ∈ 𝔭.asIdeal
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hsurj]
    constructor
    · intro ha
      obtain ⟨b, hb, c', hc', rfl⟩ := Submodule.mem_sup.mp ha
      exact 𝔭.asIdeal.add_mem hb (hp' (by simp only [Ideal.mem_comap, Submodule.mem_bot] at hc'; exact hc'))
    · exact fun ha => Submodule.mem_sup_left ha

  let ψ : Γ(X, 𝒱.U0) →+* LaurentSeries R := (HahnSeries.ofPowerSeries ℤ R).comp θ
  let ψ' : Γ(X, 𝒱.U0) ⟶ CommRingCat.of (LaurentSeries R) := CommRingCat.ofHom ψ
  let g : Spec (.of (LaurentSeries R)) ⟶ X := Spec.map ψ' ≫ hU0.fromSpec
  have hg0 : ∀ z, g.base z ∈ 𝒱.U0 := by
    intro z
    have : g.base z ∈ Set.range ⇑hU0.fromSpec := ⟨(Spec.map ψ').base z, (Scheme.Hom.comp_apply _ _ z).symm⟩
    rwa [hU0.range_fromSpec] at this

  have hθI : ∀ a : Γ(X, 𝒱.U0), a ∈ RingHom.ker (e i) → PowerSeries.X ∣ θ a := by
    intro a ha
    rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hθ0' 1 a).mpr (by simpa only [pow_one] using ha) 0 zero_lt_one
  obtain ⟨t₀, ht₀⟩ := hθs' 2 PowerSeries.X
  have ht₀I : t₀ ∈ RingHom.ker (e i) := by
    have := (hθ0' 1 t₀).mp (fun k hk => by
      obtain rfl : k = 0 := by omega
      rw [ht₀ 0 (by norm_num), PowerSeries.coeff_zero_X])
    simpa only [pow_one] using this
  have ht₀unit : IsUnit (ψ t₀) := by
    obtain ⟨u, hu⟩ := (hθI t₀ ht₀I)
    have hu1 : PowerSeries.constantCoeff u = 1 := by
      have := ht₀ 1 (by norm_num)
      rw [hu, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one_X, PowerSeries.coeff_zero_eq_constantCoeff_apply]
        at this
      exact this
    have huu : IsUnit u := PowerSeries.isUnit_iff_constantCoeff.mpr (hu1 ▸ isUnit_one)
    change IsUnit (HahnSeries.ofPowerSeries ℤ R (θ t₀))
    rw [hu, map_mul, HahnSeries.ofPowerSeries_X]
    refine IsUnit.mul ?_ (huu.map _)
    exact isUnit_iff_exists_inv.mpr ⟨HahnSeries.single (-1 : ℤ) (1 : R), by
      rw [HahnSeries.single_mul_single, add_neg_cancel, mul_one, HahnSeries.single_zero_one]⟩

  have hg1 : ∀ z, g.base z ∈ 𝒱.U1 := by
    intro z
    by_contra hz
    have hz' : g.base z ∈ (𝒱.U1 : Set X)ᶜ := hz
    rw [h.compl_eq_iUnion, Set.mem_iUnion] at hz'
    obtain ⟨j, y, hy⟩ := hz'
    set 𝔮 : ↥(Spec Γ(X, 𝒱.U0)) := (Spec.map ψ').base z with h𝔮
    have hgz : g.base z = hU0.fromSpec.base 𝔮 := Scheme.Hom.comp_apply _ _ z
    have hq𝔮 : 𝔮.asIdeal = Ideal.comap ψ z.asIdeal := rfl
    have hIj : RingHom.ker (e j) ≤ Ideal.comap ψ z.asIdeal :=
      hq𝔮 ▸ step1 j y 𝔮 (hgz.symm.trans hy.symm)
    by_cases hji : j = i
    · subst hji
      have : ψ t₀ ∈ z.asIdeal := hIj ht₀I
      exact z.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ this ht₀unit)
    ·
      have hzP : Ideal.comap (HahnSeries.ofPowerSeries ℤ R) z.asIdeal ≠ ⊤ :=
        (Ideal.comap_isPrime (HahnSeries.ofPowerSeries ℤ R) z.asIdeal).ne_top
      obtain ⟨M, hM, hzM⟩ := Ideal.exists_le_maximal _ hzP
      have hXM : PowerSeries.X ∈ M := by
        by_contra hX
        obtain ⟨w, m, hm, hwm⟩ := hM.exists_inv hX
        have hmu : IsUnit m := by
          rw [PowerSeries.isUnit_iff_constantCoeff]
          have : PowerSeries.constantCoeff m = 1 := by
            have := congrArg PowerSeries.constantCoeff hwm
            simpa using this
          rw [this]; exact isUnit_one
        exact hM.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hmu)
      haveI : (Ideal.comap θ M).IsPrime := Ideal.comap_isPrime θ M
      let 𝔭 : ↥(Spec Γ(X, 𝒱.U0)) := ⟨Ideal.comap θ M, inferInstance⟩
      have hIi𝔭 : RingHom.ker (e i) ≤ 𝔭.asIdeal := fun a ha => by
        change θ a ∈ M
        obtain ⟨u, hu⟩ := hθI a ha
        rw [hu]; exact M.mul_mem_right _ hXM
      have hIj𝔭 : RingHom.ker (e j) ≤ 𝔭.asIdeal := hIj.trans (fun a ha => by
        change θ a ∈ M
        exact hzM ha)
      obtain ⟨yi, hyi⟩ := step1' i 𝔭 hIi𝔭
      obtain ⟨yj, hyj⟩ := step1' j 𝔭 hIj𝔭
      exact Set.disjoint_left.mp (h.pairwise_disjoint hji) ⟨yj, hyj⟩ ⟨yi, hyi⟩
  have hgle : (⊤ : (Spec (.of (LaurentSeries R))).Opens) ≤ g ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1) :=
    fun z _ => ⟨hg0 z, hg1 z⟩

  let E : Γ(X, 𝒱.U0 ⊓ 𝒱.U1) ⟶ CommRingCat.of (LaurentSeries R) :=
    g.appLE (𝒱.U0 ⊓ 𝒱.U1) ⊤ hgle ≫ (Scheme.ΓSpecIso (.of (LaurentSeries R))).hom
  have hE : ∀ a : (𝒱.cover c).A0, E.hom ((𝒱.cover c).ρ0 a) = ψ a := by
    intro a
    change ((X.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op ≫
      g.appLE (𝒱.U0 ⊓ 𝒱.U1) ⊤ hgle) ≫ (Scheme.ΓSpecIso (.of (LaurentSeries R))).hom).hom a = ψ a
    rw [Scheme.Hom.map_appLE]
    rw [show g.appLE 𝒱.U0 ⊤ (fun z _ => hg0 z) =
        hU0.fromSpec.appLE 𝒱.U0 ⊤ (by rw [hU0.fromSpec_preimage_self]) ≫ (Spec.map ψ').appLE ⊤ ⊤ le_rfl from
      (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm]
    have h1 : hU0.fromSpec.appLE 𝒱.U0 ⊤ (by rw [hU0.fromSpec_preimage_self]) = (Scheme.ΓSpecIso Γ(X, 𝒱.U0)).inv := by
      rw [Scheme.Hom.appLE, hU0.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      convert Category.comp_id _
      rfl
    have h2 : (Spec.map ψ').appLE ⊤ ⊤ le_rfl = (Spec.map ψ').appTop := by
      rw [Scheme.Hom.appLE, Scheme.Hom.appTop]
      convert Category.comp_id _
      rfl
      rfl
      rfl
    rw [h1, h2, Category.assoc, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rfl
  refine ⟨{ expand := E.hom, expand_algebraMap := fun r => ?_ }, hE, ?_⟩
  · change E.hom (algebraMap R (𝒱.cover c).A01 r) = _
    rw [← (𝒱.cover c).ρ0.commutes r, hE]
    change HahnSeries.ofPowerSeries ℤ R (θ (algebraMap R (𝒱.cover c).A0 r)) = _
    rw [hθC, HahnSeries.ofPowerSeries_C]
  · refine ⟨fun b => ⟨θ b, (hE b).symm⟩, fun n p => ?_, fun n b => ?_⟩
    · obtain ⟨a, ha⟩ := hθs n p
      refine ⟨a, fun k hk => ?_⟩
      change (E.hom ((𝒱.cover c).ρ0 a)).coeff k = _
      rw [hE]
      change (HahnSeries.ofPowerSeries ℤ R (θ a)).coeff k = _
      rw [HahnSeries.ofPowerSeries_apply_coeff]
      exact ha k hk
    · refine Iff.trans (forall₂_congr fun k _ => ?_) (hθ0 n b)
      change (E.hom ((𝒱.cover c).ρ0 b)).coeff k = 0 ↔ _
      rw [hE]
      change (HahnSeries.ofPowerSeries ℤ R (θ b)).coeff k = 0 ↔ _
      rw [HahnSeries.ofPowerSeries_apply_coeff]

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_of_powerSeries
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_isCompletionAlong_of_powerSeries (solution)
