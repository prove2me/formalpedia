-- Prove2me | solution 1 for AlgebraicGeometry.exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/2b380a10-c021-51e5-9f82-3b4ffea33435

import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point
import Theorems.Thm_Algebra_exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra Filter Topology

namespace ChartOpenEval

section General

universe u

theorem appTop_map_appLE_eq_id {R : CommRingCat.{u}} {Y : Scheme.{u}} (g : Y ⟶ Spec R) (P : Spec R ⟶ Y)
    (hPg : P ≫ g = 𝟙 _) (U : Y.Opens) (hP : ⊤ ≤ P ⁻¹ᵁ U) :
    g.appTop ≫ Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ P.appLE U ⊤ hP = 𝟙 _ := by
  have h1 : Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ P.appLE U ⊤ hP = P.appLE ⊤ ⊤ le_top :=
    Scheme.Hom.map_appLE _ _ _
  have h2 : P.appLE ⊤ ⊤ le_top = P.appTop := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [h1, h2, ← Scheme.Hom.comp_appTop, hPg, Scheme.Hom.id_appTop]

theorem eq_of_appLE_top_eq {Y T : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U) (f f' : T ⟶ Y)
    (hf : ⊤ ≤ f ⁻¹ᵁ U) (hf' : ⊤ ≤ f' ⁻¹ᵁ U) (h : f.appLE U ⊤ hf = f'.appLE U ⊤ hf') : f = f' := by
  have e1 := Scheme.Opens.toSpecΓ_SpecMap_appLE f U ⊤ hf
  have e2 := Scheme.Opens.toSpecΓ_SpecMap_appLE f' U ⊤ hf'
  rw [h, e2] at e1
  haveI : IsIso U.toSpecΓ := by rw [← hU.isoSpec_hom]; infer_instance
  have e3 : f.resLE U ⊤ hf = f'.resLE U ⊤ hf' := (cancel_mono U.toSpecΓ).mp e1.symm
  have e4 := Scheme.Hom.resLE_comp_ι f hf
  have e5 := Scheme.Hom.resLE_comp_ι f' hf'
  rw [e3, e5] at e4

  have := congrArg (fun φ => T.topIso.inv ≫ φ) e4
  simp only [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp] at this
  exact this.symm

end General

section Bridge

variable {Y : Scheme.{0}} {g : Y ⟶ Spec (CommRingCat.of ℂ)} (U : Y.Opens) [Algebra ℂ Γ(Y, U)]
  (halg : ∀ z : ℂ, algebraMap ℂ Γ(Y, U) z =
    (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom z)))

noncomputable def chi (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U) :
    Γ(Y, U) →ₐ[ℂ] ℂ where
  toFun s := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) s)
  map_one' := by simp
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' x y := by simp
  commutes' z := by
    rw [Algebra.algebraMap_self, RingHom.id_apply, halg z]
    have key := congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
      (φ.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom z))) (appTop_map_appLE_eq_id g P.1 P.2 U hP)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at key
    refine key.trans ?_
    exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)) z

theorem chi_apply (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g) (hP : ⊤ ≤ P.1 ⁻¹ᵁ U) (s : Γ(Y, U)) :
    chi U halg P hP s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) s) := rfl

theorem eq_of_chi_eq (hU : IsAffineOpen U) {P P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g}
    {hP : ⊤ ≤ P.1 ⁻¹ᵁ U} {hP' : ⊤ ≤ P'.1 ⁻¹ᵁ U} (h : chi U halg P hP = chi U halg P' hP') : P = P' := by
  apply Subtype.ext
  apply eq_of_appLE_top_eq U hU P.1 P'.1 hP hP'
  ext s
  have h1 := congrArg (fun χ : Γ(Y, U) →ₐ[ℂ] ℂ => χ s) h
  simp only [chi_apply] at h1
  have h2 := congrArg ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv) h1
  simpa using h2

end Bridge

theorem coe_ofComplex {z : ℂ} (hz : 0 < z.im) : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

end ChartOpenEval

open ChartOpenEval in
theorem solution
    (Y : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of ℂ)) (hsm : SmoothOfRelativeDimension 1 g)
    (W : Set UpperHalfPlane) (hW : IsOpen W)
    (h : UpperHalfPlane → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g) (hinj : Set.InjOn h W)

    (hHOL : ∀ (U : Y.Opens) (s : Γ(Y, U)),
      IsOpen {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} ∧
      ∃ F : ℂ → ℂ,
        DifferentiableOn ℂ F
          {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧ ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} ∧
        ∀ (z : ℂ), 0 < z.im → UpperHalfPlane.ofComplex z ∈ W →
          ∀ hU : ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U,
            F z = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((h (UpperHalfPlane.ofComplex z)).1.appLE U ⊤ hU) s))
    (τs : UpperHalfPlane) (hτs : τs ∈ W)

    (σ : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) g)
    (hconv : ∀ (U : Y.Opens), IsAffineOpen U → ∀ (hQ : ⊤ ≤ (h τs).1 ⁻¹ᵁ U),
      ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (σ n).1 ⁻¹ᵁ U,
        ∀ f : Γ(Y, U),
          Tendsto (fun n : ℕ => if hn : n₀ ≤ n then
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((σ n).1.appLE U ⊤ (hP n hn)) f) else 0)
            atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((h τs).1.appLE U ⊤ hQ) f)))) :
    ∃ (τ' : ℕ → UpperHalfPlane) (n₀ : ℕ), (∀ n, n₀ ≤ n → τ' n ∈ W ∧ h (τ' n) = σ n) ∧
      Tendsto τ' atTop (𝓝 τs) := by
  classical

  obtain ⟨U, hU, hσU, inst, halg, hdom, hft, hsmooth, hrank, σ₀, t, hσ₀, hdt⟩ :=
    AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point
      Y g hsm (h τs).1 (h τs).2
  letI : Algebra ℂ Γ(Y, U) := inst
  haveI : IsDomain Γ(Y, U) := hdom
  haveI : Algebra.FiniteType ℂ Γ(Y, U) := hft
  obtain ⟨r, 𝒰, hr, hσ₀𝒰, hbij, hhol, hopen⟩ :=
    Algebra.exists_bijOn_eval_differentiableOn_of_smooth_of_kaehlerDifferential Γ(Y, U) hsmooth hrank σ₀ t hdt

  have hσ₀' : ∀ s : Γ(Y, U),
      σ₀ s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((h τs).1.appLE U ⊤ hσU) s) := fun s => hσ₀ s
  have hχσ : chi U halg (h τs) hσU = σ₀ := by
    ext s; rw [chi_apply, hσ₀' s]

  set L : Set ℂ := {z : ℂ | 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧
      ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U} with hLdef
  have hL : IsOpen L := (hHOL U t).1
  choose F hFd hFv using (fun s : Γ(Y, U) => (hHOL U s).2)
  have hFval : ∀ (s : Γ(Y, U)) (z : ℂ) (hz : z ∈ L),
      F s z = chi U halg (h (UpperHalfPlane.ofComplex z)) hz.2.2 s :=
    fun s z hz => hFv s z hz.1 hz.2.1 hz.2.2

  set V : Set ℂ := {z | ∃ hz : z ∈ L, chi U halg (h (UpperHalfPlane.ofComplex z)) hz.2.2 ∈ 𝒰} with hVdef
  have hVL : V ⊆ L := fun z hz => hz.1
  have hVopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro z₀ hz₀
    obtain ⟨hz₀L, hz₀U⟩ := hz₀
    obtain ⟨fs, ε, hε, hball⟩ := hopen _ hz₀U
    have hA : ∀ᶠ z in 𝓝 z₀, z ∈ L := hL.mem_nhds hz₀L
    have hB : ∀ᶠ z in 𝓝 z₀, ∀ s ∈ fs, ‖F s z - F s z₀‖ < ε := by
      refine (Filter.eventually_all_finset fs).mpr fun s _ => ?_
      have hc : ContinuousAt (fun z => ‖F s z - F s z₀‖) z₀ :=
        ((((hFd s).continuousOn.continuousAt (hL.mem_nhds hz₀L)).sub continuousAt_const).norm)
      have := hc.eventually_lt continuousAt_const (show ‖F s z₀ - F s z₀‖ < ε by simpa using hε)
      exact this
    filter_upwards [hA, hB] with z hzL hzε
    refine ⟨hzL, hball _ fun s hs => ?_⟩
    rw [← hFval s z hzL, ← hFval s z₀ hz₀L]
    exact hzε s hs

  set zs : ℂ := (τs : ℂ) with hzsdef
  have hzs_im : 0 < zs.im := τs.im_pos
  have hofzs : UpperHalfPlane.ofComplex zs = τs := UpperHalfPlane.ofComplex_apply τs
  have hmemL : ∀ z : ℂ, z ∈ L ↔ 0 < z.im ∧ UpperHalfPlane.ofComplex z ∈ W ∧
      ⊤ ≤ (h (UpperHalfPlane.ofComplex z)).1 ⁻¹ᵁ U := fun z => Iff.rfl
  have htrans : ∀ (τ : UpperHalfPlane) (e : τ = τs), τ ∈ W ∧ ∃ hτ : ⊤ ≤ (h τ).1 ⁻¹ᵁ U,
      ∀ hτ' : ⊤ ≤ (h τ).1 ⁻¹ᵁ U, chi U halg (h τ) hτ' = σ₀ := by
    rintro τ rfl
    exact ⟨hτs, hσU, fun _ => hχσ⟩
  have hzsL : zs ∈ L := by
    obtain ⟨hw, hτ, -⟩ := htrans _ hofzs
    exact (hmemL zs).mpr ⟨hzs_im, hw, hτ⟩
  have hchizs : chi U halg (h (UpperHalfPlane.ofComplex zs)) hzsL.2.2 = σ₀ :=
    (htrans _ hofzs).2.2 _
  have hzsV : zs ∈ V := ⟨hzsL, by rw [hchizs]; exact hσ₀𝒰⟩

  set k : ℂ → ℂ := F t with hkdef
  have hk_inj : Set.InjOn k V := by
    intro z₁ h₁ z₂ h₂ hk
    obtain ⟨h₁L, h₁U⟩ := h₁
    obtain ⟨h₂L, h₂U⟩ := h₂
    have e1 : chi U halg (h (UpperHalfPlane.ofComplex z₁)) h₁L.2.2 =
        chi U halg (h (UpperHalfPlane.ofComplex z₂)) h₂L.2.2 := by
      apply hbij.injOn h₁U h₂U
      show chi U halg _ _ t = chi U halg _ _ t
      rw [← hFval t z₁ h₁L, ← hFval t z₂ h₂L]
      exact hk
    have e2 := eq_of_chi_eq U halg hU e1
    have e3 := hinj h₁L.2.1 h₂L.2.1 e2
    have e4 := congrArg (fun τ : UpperHalfPlane => (τ : ℂ)) e3
    simp only [coe_ofComplex h₁L.1, coe_ofComplex h₂L.1] at e4
    exact e4

  have hk_an : AnalyticAt ℂ k zs := (hFd t).analyticAt (hL.mem_nhds hzsL)
  have hmap : 𝓝 (k zs) ≤ map k (𝓝 zs) := by
    rcases hk_an.eventually_constant_or_nhds_le_map_nhds with hc | hle
    · exfalso
      have hVev : ∀ᶠ z in 𝓝 zs, z ∈ V := hVopen.mem_nhds hzsV
      have h1 : ∀ᶠ z in 𝓝[≠] zs, z ∈ ({zs}ᶜ : Set ℂ) ∧ (z ∈ V ∧ k z = k zs) :=
        eventually_mem_nhdsWithin.and ((hVev.and hc).filter_mono nhdsWithin_le_nhds)
      haveI := NormedField.nhdsNE_neBot zs
      obtain ⟨z, hz1, hz2, hz3⟩ := h1.exists
      exact hz1 (hk_inj hz2 hzsV hz3)
    · exact hle

  obtain ⟨n₀, hPn, hT⟩ := hconv U hU hσU
  obtain ⟨fs, ε, hε, hball⟩ := hopen σ₀ hσ₀𝒰
  have hev1 : ∀ᶠ n in atTop, ∃ hn : n₀ ≤ n, chi U halg (σ n) (hPn n hn) ∈ 𝒰 := by
    have hA : ∀ᶠ n in atTop, n₀ ≤ n := eventually_ge_atTop n₀
    have hB : ∀ᶠ n in atTop, ∀ s ∈ fs,
        dist (if hn : n₀ ≤ n then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((σ n).1.appLE U ⊤ (hPn n hn)) s) else 0)
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((h τs).1.appLE U ⊤ hσU) s)) < ε :=
      (Filter.eventually_all_finset fs).mpr fun s _ => (Metric.tendsto_nhds.mp (hT s)) ε hε
    filter_upwards [hA, hB] with n hn hB'
    refine ⟨hn, hball _ fun s hs => ?_⟩
    have := hB' s hs
    rw [dif_pos hn, dist_eq_norm, ← hσ₀' s] at this
    rw [chi_apply]
    exact this

  have hkzs : k zs = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((h τs).1.appLE U ⊤ hσU) t) := by
    show F t zs = _
    rw [hFval t zs hzsL, hchizs, hσ₀' t]
  have hTt : Tendsto (fun n : ℕ => if hn : n₀ ≤ n then
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((σ n).1.appLE U ⊤ (hPn n hn)) t) else 0) atTop (𝓝 (k zs)) := by
    rw [hkzs]; exact hT t
  set a : ℕ → ℂ := fun n : ℕ => if hn : n₀ ≤ n then
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((σ n).1.appLE U ⊤ (hPn n hn)) t) else 0 with hadef

  have hchoice : ∀ n : ℕ, ∃ z : ℂ, z ∈ V ∧ (a n ∈ k '' V → k z = a n) := by
    intro n
    by_cases hn : a n ∈ k '' V
    · obtain ⟨z, hz, e⟩ := hn
      exact ⟨z, hz, fun _ => e⟩
    · exact ⟨zs, hzsV, fun h' => (hn h').elim⟩
  choose τz hτzV hτzk using hchoice
  have hτz_tend : Tendsto τz atTop (𝓝 zs) := by
    rw [tendsto_nhds]
    intro N hNo hzsN
    have hN' : k '' (N ∩ V) ∈ 𝓝 (k zs) :=
      hmap (image_mem_map ((hNo.inter hVopen).mem_nhds ⟨hzsN, hzsV⟩))
    have hev : ∀ᶠ n in atTop, a n ∈ k '' (N ∩ V) := hTt hN'
    refine hev.mono fun n hn => ?_
    obtain ⟨z, ⟨hzN, hzV⟩, hz⟩ := hn
    have hin : a n ∈ k '' V := ⟨z, hzV, hz⟩
    have e : τz n = z := hk_inj (hτzV n) hzV ((hτzk n hin).trans hz.symm)
    show τz n ∈ N
    rw [e]; exact hzN
  have hev2 : ∀ᶠ n in atTop, a n ∈ k '' V := hTt (hmap (image_mem_map (hVopen.mem_nhds hzsV)))
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (hev1.and hev2)
  refine ⟨fun n => UpperHalfPlane.ofComplex (τz n), n₁, fun n hn => ?_, ?_⟩
  · obtain ⟨⟨hn0, hσn𝒰⟩, hin⟩ := hn₁ n hn
    obtain ⟨hzL, hz𝒰⟩ := hτzV n
    refine ⟨hzL.2.1, ?_⟩
    apply eq_of_chi_eq U halg hU (hP := hzL.2.2) (hP' := hPn n hn0)
    apply hbij.injOn hz𝒰 hσn𝒰
    show chi U halg _ _ t = chi U halg _ _ t
    rw [← hFval t _ hzL, chi_apply]
    have e := hτzk n hin
    simp only [hadef, dif_pos hn0] at e
    exact e
  · rw [UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.tendsto_nhds_iff]
    have e : (fun n => ((UpperHalfPlane.ofComplex (τz n) : UpperHalfPlane) : ℂ)) = τz :=
      funext fun n => coe_ofComplex (hVL (hτzV n)).1
    show Tendsto (fun n => ((UpperHalfPlane.ofComplex (τz n) : UpperHalfPlane) : ℂ)) atTop (𝓝 (τs : ℂ))
    rw [e]
    exact hτz_tend

end S_AlgebraicGeometry_exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE
end P2MW
export P2MW.S_AlgebraicGeometry_exists_tendsto_forall_eq_of_injOn_of_differentiableOn_appLE_of_tendsto_appLE (solution)
