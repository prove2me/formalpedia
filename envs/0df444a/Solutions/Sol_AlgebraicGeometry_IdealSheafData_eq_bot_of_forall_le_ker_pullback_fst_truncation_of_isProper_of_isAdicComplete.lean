-- Prove2me | solution 1 for AlgebraicGeometry.IdealSheafData.eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/8050b3a6-5668-5f13-bc23-f8462af1a301

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IdealSheafData_eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace P2mWs41KEY

lemma apply_eq_zero_of_comp_isIso {A B C : CommRingCat.{u}} (g : A ⟶ B) (e : B ⟶ C) [IsIso e] (x : A)
    (h : (g ≫ e) x = 0) : g x = 0 := by
  have h' : (g ≫ e ≫ inv e) x = 0 := by
    rw [← Category.assoc, CommRingCat.comp_apply, h, map_zero]
  simpa using h'

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

noncomputable def φ (U : X.affineOpens) : CommRingCat.of R ⟶ Γ(X, U.1) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.1 (by simp)

lemma fromSpec_comp (U : X.affineOpens) : U.2.fromSpec ≫ f = Spec.map (φ f U) := by
  rw [φ, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp)).symm

theorem mem_map_pow_of_le_ker (I : Ideal R) (n : ℕ)
    (sR : Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : sR = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (J : X.IdealSheafData) (hJ : J ≤ (pullback.fst f sR).ker)
    (U : X.affineOpens) (s : Γ(X, U.1)) (hs : s ∈ J.ideal U) :
    s ∈ (I ^ (n + 1)).map (φ f U).hom := by
  classical
  subst hsR
  let BK : Ideal Γ(X, U.1) := (I ^ (n + 1)).map (φ f U).hom
  let q : Γ(X, U.1) →+* Γ(X, U.1) ⧸ BK := Ideal.Quotient.mk BK
  let ψ : R ⧸ I ^ (n + 1) →+* Γ(X, U.1) ⧸ BK := Ideal.quotientMap BK (φ f U).hom Ideal.le_comap_map
  have hψ : ψ.comp (Ideal.Quotient.mk (I ^ (n + 1))) = q.comp (φ f U).hom := Ideal.quotientMap_comp_mk _

  let c : Spec (CommRingCat.of (Γ(X, U.1) ⧸ BK)) ⟶ X := Spec.map (CommRingCat.ofHom q) ≫ U.2.fromSpec
  have w : c ≫ f = Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))) := by
    simp only [c]
    rw [Category.assoc, fromSpec_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
  let t := pullback.lift c (Spec.map (CommRingCat.ofHom ψ)) w
  have ht : t ≫ pullback.fst f _ = c := pullback.lift_fst _ _ _

  have hs0 : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))).app U.1 s = 0 := by
    have := hJ U hs
    rw [Scheme.Hom.ker_apply] at this
    exact RingHom.mem_ker.mp this
  have h1 : (t ≫ pullback.fst f _).app U.1 s = 0 := by
    have hs0' : ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))).app U.1).hom s = 0 := hs0
    rw [Scheme.Hom.comp_app]
    change (t.app _).hom (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))).app U.1).hom s) = 0
    rw [hs0', map_zero]
  have h2 : c.app U.1 s = 0 := by
    rw [Scheme.Hom.congr_app ht.symm U.1]
    change ((Spec (CommRingCat.of (Γ(X, U.1) ⧸ BK))).presheaf.map _).hom (((t ≫ pullback.fst f _).app U.1).hom s) = 0
    have h1' : ((t ≫ pullback.fst f _).app U.1).hom s = 0 := h1
    rw [h1', map_zero]

  have hcU : c ⁻¹ᵁ U.1 = ⊤ := by
    simp only [c, Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self, Scheme.Hom.preimage_top]
  have step1 : c.app U.1 = ((Scheme.ΓSpecIso Γ(X, U.1)).inv ≫
      (Spec Γ(X, U.1)).presheaf.map (eqToHom U.2.fromSpec_preimage_self).op) ≫
      (Spec.map (CommRingCat.ofHom q)).app (U.2.fromSpec ⁻¹ᵁ U.1) := by
    rw [← IsAffineOpen.fromSpec_app_self]; rfl
  have step2 := Scheme.Hom.naturality (Spec.map (CommRingCat.ofHom q)) (eqToHom U.2.fromSpec_preimage_self).op
  have step3 : (Scheme.ΓSpecIso Γ(X, U.1)).inv ≫ (Spec.map (CommRingCat.ofHom q)).app ⊤ =
      CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ BK))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)).symm
  have hj : ((TopologicalSpace.Opens.map (Spec.map (CommRingCat.ofHom q)).base).map
      (eqToHom U.2.fromSpec_preimage_self).op.unop).op = (eqToHom hcU).op :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hC : c.app U.1 = (CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U.1) ⧸ BK))).inv) ≫
      (Spec (CommRingCat.of (Γ(X, U.1) ⧸ BK))).presheaf.map (eqToHom hcU).op := by
    rw [step1, Category.assoc]
    erw [step2]
    rw [← Category.assoc]
    erw [step3]
    rw [hj]
    rfl
  rw [hC] at h2
  have h4 := apply_eq_zero_of_comp_isIso _ _ s h2
  have h5 := apply_eq_zero_of_comp_isIso _ _ s h4
  exact Ideal.Quotient.eq_zero_iff_mem.mp h5

theorem germ_mem_maximalIdeal_of_mem_map (I : Ideal R) (U : X.affineOpens) (x : X) (hxU : x ∈ U.1)
    (hx : I ≤ (f.base x).asIdeal) (r : Γ(X, U.1)) (hr : r ∈ I.map (φ f U).hom) :
    X.presheaf.germ U.1 x hxU r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by

  have key : ∀ i ∈ I, X.presheaf.germ U.1 x hxU ((φ f U).hom i) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
    intro i hi
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

    have e : X.presheaf.germ U.1 x hxU ((φ f U).hom i) =
        (f.stalkMap x).hom ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base x) trivial
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv i)) := by
      rw [Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial]
      simp only [φ, Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
      erw [TopCat.Presheaf.germ_res_apply]
    rw [e]
    intro hu
    have hu' := (isUnit_map_iff (f.stalkMap x).hom _).mp hu
    rw [← Scheme.mem_basicOpen, AlgebraicGeometry.basicOpen_eq_of_affine] at hu'
    exact hu' (hx hi)

  have : I.map (φ f U).hom ≤ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.germ U.1 x hxU).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    exact key i hi
  exact this hr

theorem exists_basicOpen_ideal_eq_bot [IsNoetherianRing R] (I : Ideal R)
    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (J : X.IdealSheafData) (hJ : ∀ n : ℕ, J ≤ (pullback.fst f (sR n)).ker)
    (U : X.affineOpens) [IsNoetherianRing Γ(X, U.1)] (x : X) (hxU : x ∈ U.1) (hx : I ≤ (f.base x).asIdeal) :
    ∃ g : Γ(X, U.1), x ∈ X.basicOpen g ∧ J.ideal (X.affineBasicOpen g) = ⊥ := by
  classical
  let IB : Ideal Γ(X, U.1) := I.map (φ f U).hom

  have hfix : ∀ s ∈ J.ideal U, ∃ r ∈ IB, r * s = s := by
    intro s hs
    have hmem : s ∈ (⨅ i : ℕ, IB ^ i • ⊤ : Submodule Γ(X, U.1) Γ(X, U.1)) := by
      refine (Submodule.mem_iInf _).mpr fun i => ?_
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
      cases i with
      | zero => simp
      | succ n =>
        have := mem_map_pow_of_le_ker f I n (sR n) (hsR n) J (hJ n) U s hs
        rwa [Ideal.map_pow] at this
    obtain ⟨r, hr⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff IB s).mp hmem
    exact ⟨r, r.2, by simpa [smul_eq_mul] using hr⟩

  obtain ⟨S, hS⟩ := IsNoetherian.noetherian (J.ideal U)
  have hSmem : ∀ s ∈ S, s ∈ J.ideal U := fun s hs => hS ▸ Ideal.subset_span hs
  choose r hr using fun s (hs : s ∈ S) => hfix s (hSmem s hs)
  let g : Γ(X, U.1) := ∏ s ∈ S.attach, (1 - r s.1 s.2)
  have hgS : ∀ s ∈ S, g * s = 0 := by
    intro s hs
    obtain ⟨k, hk⟩ : (1 - r s hs) ∣ g := Finset.dvd_prod_of_mem (fun t : {t // t ∈ S} => (1 - r t.1 t.2)) (Finset.mem_attach S ⟨s, hs⟩)
    rw [hk, mul_comm (1 - r s hs) k, mul_assoc, sub_mul, one_mul, (hr s hs).2, sub_self, mul_zero]
  refine ⟨g, ?_, ?_⟩
  ·
    rw [X.mem_basicOpen g x hxU, map_prod]
    refine Finset.prod_induction _ (fun u => IsUnit u) (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro t _
    rw [map_sub, map_one]
    have hm := germ_mem_maximalIdeal_of_mem_map f I U x hxU hx (r t.1 t.2) (hr t.1 t.2).1
    refine (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left ?_
    exact (IsLocalRing.mem_maximalIdeal _).mp hm
  ·
    rw [← J.map_ideal_basicOpen U g, ← hS, Ideal.map_span]
    refine Ideal.span_eq_bot.mpr ?_
    rintro _ ⟨s, hs, rfl⟩
    haveI := U.2.isLocalization_basicOpen g
    change algebraMap Γ(X, U.1) Γ(X, X.basicOpen g) s = 0
    rw [IsLocalization.map_eq_zero_iff (.powers g)]
    exact ⟨⟨g, Submonoid.mem_powers g⟩, hgS s hs⟩

end P2mWs41KEY

open P2mWs41KEY in
theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]

    (sR : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ Spec (CommRingCat.of R))
    (hsR : ∀ n : ℕ, sR n = Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (n + 1)))))
    (J : X.IdealSheafData) (hJ : ∀ n : ℕ, J ≤ (Limits.pullback.fst f (sR n)).ker) :
    J = ⊥ := by
  classical
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  refine le_bot_iff.mp fun U => ?_
  intro s hs
  rw [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply, Ideal.mem_bot]

  apply TopCat.Presheaf.section_ext X.sheaf U.1 s 0
  intro y hy

  obtain ⟨x₀, hx₀, hcl⟩ := (isClosed_closure (s := ({y} : Set X))).exists_closed_singleton ⟨y, subset_closure rfl⟩
  have hspec : y ⤳ x₀ := specializes_iff_mem_closure.mpr hx₀
  have hP : I ≤ (f.base x₀).asIdeal := by
    have hcl' : IsClosed ({f.base x₀} : Set (Spec (CommRingCat.of R))) := by
      simpa [Set.image_singleton] using f.isClosedMap _ hcl
    have hmax := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp hcl'
    exact (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hmax⟩)

  have hx₀top : x₀ ∈ (⨆ U : X.affineOpens, (U : X.Opens)) := by rw [iSup_affineOpens_eq_top]; trivial
  obtain ⟨U₀, hU₀⟩ := TopologicalSpace.Opens.mem_iSup.mp hx₀top
  haveI : IsNoetherianRing Γ(X, U₀.1) := IsLocallyNoetherian.component_noetherian U₀
  obtain ⟨g, hxg, hJg⟩ := exists_basicOpen_ideal_eq_bot f I sR hsR J hJ U₀ x₀ hU₀ hP
  have hyg : y ∈ X.basicOpen g := hspec.mem_open (X.basicOpen g).isOpen hxg

  obtain ⟨h, hhU, hyh⟩ := (X.affineBasicOpen g).2.exists_basicOpen_le ⟨y, hy⟩ hyg
  have hJh : J.ideal (X.affineBasicOpen h) = ⊥ := by
    rw [← J.map_ideal_basicOpen, hJg, Ideal.map_bot]; rfl
  have hres : (X.presheaf.map (homOfLE hhU).op) s = 0 := by
    have := J.ideal_le_comap_ideal (U := X.affineBasicOpen h) (V := U) hhU hs
    rw [Ideal.mem_comap, hJh, Ideal.mem_bot] at this
    exact this
  have e1 : X.presheaf.germ U.1 y hy s = 0 := by
    have := (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hhU) y hyh s).symm
    rw [hres, map_zero] at this
    exact this
  show X.presheaf.germ U.1 y hy s = X.presheaf.germ U.1 y hy 0
  rw [e1, map_zero]

end S_AlgebraicGeometry_IdealSheafData_eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete
end P2MW
export P2MW.S_AlgebraicGeometry_IdealSheafData_eq_bot_of_forall_le_ker_pullback_fst_truncation_of_isProper_of_isAdicComplete (solution)
