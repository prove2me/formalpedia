-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.hasDevissageStep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/c59c50da-63b7-56db-90f6-e9b4c10f17df

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_AlgebraicGeometry_Scheme_isIntegral_subscheme_vanishingIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_hasDevissageStep

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_hasDevissageStep.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme.basicOpen_res Surjective Scheme.IdealSheafData.coe_support_vanishingIdeal Scheme.Hom Spec Scheme Scheme.IdealSheafData.vanishingIdeal Scheme.IdealSheafData.vanishingIdeal_ideal IsSeparated IsLocallyNoetherian.component_noetherian IsNoetherian Scheme.Hom.app_eq_appLE Scheme.IdealSheafData OModulePresheaf.appLE_algebraMap OModulePresheaf.pushforward OModulePresheaf.DevissageStep OModulePresheaf.HasDevissageStep Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated OModulePresheaf.AffSES Scheme.OrderedAffineCover OModulePresheaf OModulePresheaf.IsCoherent OModulePresheaf.IsQuasicoherent OModulePresheaf.SupportedIn Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom Scheme.TwoAffineOpenCover.restrictAlgHom Scheme.isIntegral_subscheme_vanishingIdeal"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "zero ker appLE_algebraMap pushforward DevissageStep HasDevissageStep Hom AffSES d IsCoherent IsQuasicoherent SupportedIn res res_smul res_refl isScalarTower mk module obj res_comp addCommGroup moduleSections"
namespace G5B
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

section AnnIdealPMod

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

def annIdealSubAff (I : V.IdealSheafData) (F : OModulePresheaf π)
    (W : V.affineOpens) : Submodule Γ(V, W.1) (F.obj W.1) :=
  { carrier := {x | ∀ a ∈ I.ideal W, a • x = 0}
    add_mem' := fun hx hy a ha => by rw [smul_add, hx a ha, hy a ha, add_zero]
    zero_mem' := fun a _ => smul_zero a
    smul_mem' := fun c x hx a ha => by rw [smul_comm, hx a ha, smul_zero] }

def annIdealSub (I : V.IdealSheafData) (F : OModulePresheaf π) (U : V.Opens) :
    Submodule R (F.obj U) :=
  ⨅ (W : V.affineOpens) (hW : W.1 ≤ U),
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π W.1).toModule; haveI := F.isScalarTower W.1
    Submodule.comap (F.res hW) ((annIdealSubAff π I F W).restrictScalars R)

theorem mem_annIdealSub (I : V.IdealSheafData) (F : OModulePresheaf π) (U : V.Opens)
    (x : F.obj U) :
    x ∈ annIdealSub π I F U
      ↔ ∀ (W : V.affineOpens) (hW : W.1 ≤ U), ∀ a ∈ I.ideal W, a • F.res hW x = 0 := by
  simp only [annIdealSub, Submodule.mem_iInf, Submodule.mem_comap,
    Submodule.restrictScalars_mem]
  rfl

theorem annIdealSub_res (I : V.IdealSheafData) (F : OModulePresheaf π)
    {U U' : V.Opens} (h : U ≤ U') (x : F.obj U')
    (hx : x ∈ annIdealSub π I F U') :
    F.res h x ∈ annIdealSub π I F U := by
  rw [mem_annIdealSub] at hx ⊢
  intro W hW a ha
  rw [← LinearMap.comp_apply, ← F.res_comp]
  exact hx W (hW.trans h) a ha

theorem annIdealSub_Γsmul (I : V.IdealSheafData) (F : OModulePresheaf π)
    (U : V.Opens) (c : Γ(V, U)) (x : F.obj U)
    (hx : x ∈ annIdealSub π I F U) :
    c • x ∈ annIdealSub π I F U := by
  rw [mem_annIdealSub] at hx ⊢
  intro W hW a ha
  rw [F.res_smul, smul_comm, hx W hW a ha, smul_zero]

def annIdealPMod (I : V.IdealSheafData) (F : OModulePresheaf π) : OModulePresheaf π where
  obj U := annIdealSub π I F U
  addCommGroup U := inferInstance
  module U := inferInstance
  moduleSections U :=
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
    { smul := fun c x => ⟨c • x.1, annIdealSub_Γsmul π I F U c x.1 x.2⟩
      one_smul := fun x => Subtype.ext (one_smul _ x.1)
      mul_smul := fun a b x => Subtype.ext (mul_smul a b x.1)
      smul_zero := fun a => Subtype.ext (smul_zero a)
      smul_add := fun a x y => Subtype.ext (smul_add a x.1 y.1)
      add_smul := fun a b x => Subtype.ext (add_smul a b x.1)
      zero_smul := fun x => Subtype.ext (zero_smul _ x.1) }
  isScalarTower U := by
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; haveI := F.isScalarTower U
    letI : Module Γ(V, U) (annIdealSub π I F U) :=
      { smul := fun c x => ⟨c • x.1, annIdealSub_Γsmul π I F U c x.1 x.2⟩
        one_smul := fun x => Subtype.ext (one_smul _ x.1)
        mul_smul := fun a b x => Subtype.ext (mul_smul a b x.1)
        smul_zero := fun a => Subtype.ext (smul_zero a)
        smul_add := fun a x y => Subtype.ext (smul_add a x.1 y.1)
        add_smul := fun a b x => Subtype.ext (add_smul a b x.1)
        zero_smul := fun x => Subtype.ext (zero_smul _ x.1) }
    exact ⟨fun r a x => Subtype.ext (smul_assoc r a x.1)⟩
  res {U U'} h := LinearMap.codRestrict (annIdealSub π I F U)
    ((F.res h).comp (annIdealSub π I F U').subtype)
    (fun x => annIdealSub_res π I F h x.1 x.2)
  res_smul {U U'} h a x := Subtype.ext (F.res_smul h a x.1)
  res_refl U := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (F.res_refl U) x.1)
  res_comp h h' := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (F.res_comp h h') x.1)

theorem annIdealSub_affine (I : V.IdealSheafData) (F : OModulePresheaf π)
    (U : V.affineOpens) (x : F.obj U.1) :
    x ∈ annIdealSub π I F U.1 ↔ ∀ a ∈ I.ideal U, a • x = 0 := by
  rw [mem_annIdealSub]
  refine ⟨fun h a ha => ?_, fun h W hW a ha => ?_⟩
  · have := h U le_rfl a ha
    rwa [LinearMap.congr_fun (F.res_refl U.1) x] at this
  ·

    have ha' : a ∈ (I.ideal U).map (V.presheaf.map (homOfLE hW).op).hom := I.map_ideal hW ▸ ha
    refine Submodule.span_induction (fun c hc => ?_) (zero_smul _ _)
      (fun y z _ _ hy hz => by rw [add_smul, hy, hz, add_zero])
      (fun c y _ hy => by rw [smul_eq_mul, mul_smul, hy, smul_zero]) ha'
    obtain ⟨b, hb, rfl⟩ := hc
    exact (F.res_smul hW b x).symm.trans (by rw [h b hb]; exact map_zero _)

theorem vanishingIdeal_ideal_eq_top (Z : Closeds V) (U : V.affineOpens)
    (hU : ((U : V.Opens) : Set V) ∩ Z = ∅) :
    (Scheme.IdealSheafData.vanishingIdeal Z).ideal U = ⊤ := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  refine top_unique fun a _ => (PrimeSpectrum.mem_vanishingIdeal _ _).mpr fun p hp => ?_
  exact absurd (Set.mem_inter (U.2.range_fromSpec ▸ Set.mem_range_self p)
    (Set.mem_preimage.mp hp)) (Set.eq_empty_iff_forall_notMem.mp hU _)

theorem annIdealPMod_suppIn (Z : Closeds V) (F : OModulePresheaf π) :
    OModulePresheaf.SupportedIn
      (annIdealPMod π (Scheme.IdealSheafData.vanishingIdeal Z) F) Z := by
  intro U hU
  refine ⟨fun x y => Subtype.ext ?_⟩
  have htop := vanishingIdeal_ideal_eq_top Z U hU
  have hx := (annIdealSub_affine π _ F U x.1).mp x.2 1 (htop ▸ Submodule.mem_top)
  have hy := (annIdealSub_affine π _ F U y.1).mp y.2 1 (htop ▸ Submodule.mem_top)
  rw [one_smul] at hx hy; rw [hx, hy]

theorem annIdealPMod_isQCF [IsLocallyNoetherian V]
    (I : V.IdealSheafData) (F : OModulePresheaf π) (hFq : OModulePresheaf.IsQuasicoherent F) :
    OModulePresheaf.IsQuasicoherent (annIdealPMod π I F) := fun U f => by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; haveI := F.isScalarTower U.1
  haveI := IsLocallyNoetherian.component_noetherian U
  let ρ := (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom
  refine ⟨fun x => ?_, fun y hy => (hFq U f).2 y.1 (congrArg Subtype.val hy) |>.imp
    fun n hn => Subtype.ext hn⟩

  obtain ⟨n, y', hy'⟩ := (hFq U f).1 x.1
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (I.ideal U) : (I.ideal U).FG)
  have hres0 : ∀ a ∈ (I.ideal U), F.res (V.basicOpen_le f) (a • y') = 0 := fun a ha => by
    have h0 : (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom a • (x.1 : F.obj _) = 0 :=
      (annIdealSub_affine π I F (V.affineBasicOpen f) x.1).mp x.2 (ρ a)
        (I.map_ideal (U := V.affineBasicOpen f) (V.basicOpen_le f) ▸ Ideal.mem_map_of_mem ρ ha)
    rw [F.res_smul, hy', smul_comm, h0, smul_zero]
  choose Ma hMa using fun a : s => (hFq U f).2 (a.1 • y') (hres0 a.1 (hs ▸ Ideal.subset_span a.2))
  refine ⟨s.attach.sup Ma + n, ⟨f ^ s.attach.sup Ma • y',
    (annIdealSub_affine π I F U _).mpr fun a ha => ?_⟩, Subtype.ext ?_⟩
  · rw [← hs] at ha
    refine Submodule.span_induction (fun b hb => ?_) (by rw [zero_smul])
      (fun b₁ b₂ _ _ h₁ h₂ => by rw [add_smul, h₁, h₂, add_zero])
      (fun d b _ hb => by rw [smul_eq_mul, mul_smul, hb, smul_zero]) ha
    rw [smul_comm, ← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_attach s ⟨b, hb⟩)),
      pow_add, mul_smul, hMa ⟨b, hb⟩, smul_zero]
  · show F.res (V.basicOpen_le f) (f ^ s.attach.sup Ma • y') = ρ (f ^ (s.attach.sup Ma + n)) • x.1
    rw [F.res_smul, hy']
    show ρ (f ^ s.attach.sup Ma) • ρ (f ^ n) • (x.1 : F.obj _) = ρ (f ^ (s.attach.sup Ma + n)) • x.1
    rw [← mul_smul, ← map_mul, ← pow_add]

end AnnIdealPMod

section AnnPull

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
variable (Z : Closeds V) (F : OModulePresheaf π)

abbrev subschemeInc := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι

local notation "iZ" => subschemeInc Z
local notation "IZ" => Scheme.IdealSheafData.vanishingIdeal Z

abbrev G₂ : OModulePresheaf π := annIdealPMod π IZ F

theorem G₂_ann (U : V.affineOpens) (x : (G₂ π Z F).obj U.1)
    (a : Γ(V, U.1)) (ha : a ∈ (IZ).ideal U) : a • x.1 = 0 :=
  (annIdealSub_affine π IZ F U x.1).mp x.2 a ha

theorem G₂_cf_id (U : V.affineOpens) (f c : Γ(V, U.1))
    (hfc : (1 : Γ(V, U.1)) - c * f ∈ (IZ).ideal U)
    (x : (G₂ π Z F).obj U.1) (k : ℕ) : (c * f) ^ k • x.1 = x.1 := by
  have hcf : (c * f) • x.1 = x.1 := by
    have h0 := G₂_ann π Z F U x _ hfc
    rw [sub_smul, one_smul, sub_eq_zero] at h0; exact h0.symm
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, hcf, ih]

theorem G₂_res_bij_basicOpen [IsLocallyNoetherian V]
    (hFq : OModulePresheaf.IsQuasicoherent F) (U : V.affineOpens) (f : Γ(V, U.1))
    (hf : ((U : V.Opens) : Set V) ∩ Z ⊆ V.basicOpen f) :
    Function.Bijective
      ((G₂ π Z F).res (U := (V.affineBasicOpen f).1) (V.basicOpen_le f)) := by
  obtain ⟨c, hfc⟩ : ∃ c, (1 : Γ(V, U.1)) - c * f ∈ (IZ).ideal U := by

    have htop : (IZ).ideal U ⊔ Ideal.span {f} = ⊤ := by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
      by_contra habs
      obtain ⟨m, hmax, hle⟩ := Ideal.exists_le_maximal _ habs
      set p : PrimeSpectrum Γ(V, U.1) := ⟨m, hmax.isPrime⟩
      have hpS : p ∈ U.2.fromSpec ⁻¹' (Z : Set V) := by
        have hScl : IsClosed (U.2.fromSpec ⁻¹' (Z : Set V)) :=
          Z.2.preimage U.2.fromSpec.continuous
        have key : PrimeSpectrum.zeroLocus
            (↑(PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set V))) : Set Γ(V, U.1))
            = U.2.fromSpec ⁻¹' (Z : Set V) :=
          (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).trans hScl.closure_eq
        exact key ▸ fun a ha => hle (Ideal.mem_sup_left ha)
      have hDf : p ∈ U.2.fromSpec ⁻¹ᵁ V.basicOpen f :=
        hf ⟨U.2.range_fromSpec ▸ Set.mem_range_self p, Set.mem_preimage.mp hpS⟩
      exact (PrimeSpectrum.mem_basicOpen f p).mp (U.2.fromSpec_preimage_basicOpen f ▸ hDf)
        (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
      (htop ▸ (Submodule.mem_top : (1 : Γ(V, U.1)) ∈ _))
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hb
    exact ⟨c, by rw [show (1 : Γ(V, U.1)) - c * f = a from by linear_combination -hab]; exact ha⟩
  refine ⟨fun x y hxy => Subtype.ext ?_, fun y => ?_⟩
  ·
    have hres0 : F.res (V.basicOpen_le f) (x.1 - y.1) = 0 := by
      have hval := congrArg Subtype.val hxy
      rw [map_sub, sub_eq_zero]; exact hval
    obtain ⟨M, hM⟩ := (hFq U f).2 (x.1 - y.1) hres0
    have hid : (c * f) ^ M • (x.1 - y.1) = x.1 - y.1 :=
      G₂_cf_id π Z F U f c hfc ⟨x.1 - y.1, sub_mem x.2 y.2⟩ M
    rw [← sub_eq_zero, ← hid, mul_pow, mul_smul, hM, smul_zero]
  ·

    haveI := IsLocallyNoetherian.component_noetherian U
    letI : Module Γ(V, V.basicOpen f) (F.obj (V.affineBasicOpen f).1) := F.moduleSections (V.basicOpen f)
    let ρ := (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom
    obtain ⟨n, z, hz⟩ := (hFq U f).1 y.1

    have hres0 : ∀ a ∈ (IZ).ideal U, F.res (V.basicOpen_le f) (a • z) = 0 := fun a ha => by
      have hρa : ρ a ∈ (IZ).ideal (V.affineBasicOpen f) :=
        (IZ).map_ideal (U := V.affineBasicOpen f) (V := U) (V.basicOpen_le f)
          ▸ Ideal.mem_map_of_mem ρ ha
      rw [F.res_smul, hz]
      exact G₂_ann π Z F (V.affineBasicOpen f)
        ⟨ρ (f ^ n) • y.1, annIdealSub_Γsmul π IZ F _ (ρ (f ^ n)) y.1 y.2⟩
        (ρ a) hρa

    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian ((IZ).ideal U) : ((IZ).ideal U).FG)
    choose Ma hMa using fun a : s =>
      (hFq U f).2 (a.1 • z) (hres0 a.1 (hs ▸ Ideal.subset_span a.2))
    set M := s.attach.sup Ma
    have hzann : ∀ a ∈ (IZ).ideal U, a • (f ^ M • z) = 0 := fun a ha => by
      rw [← hs] at ha
      refine Submodule.span_induction (fun b hb => ?_) (by rw [zero_smul])
        (fun b₁ b₂ _ _ h₁ h₂ => by rw [add_smul, h₁, h₂, add_zero])
        (fun d b _ hb => by rw [smul_eq_mul, mul_smul, hb, smul_zero]) ha
      have hle : Ma ⟨b, hb⟩ ≤ M := Finset.le_sup (Finset.mem_attach s ⟨b, hb⟩)
      rw [smul_comm, ← Nat.sub_add_cancel hle, pow_add, mul_smul, hMa ⟨b, hb⟩, smul_zero]
    have hfMz : f ^ M • z ∈ annIdealSub π IZ F U.1 :=
      (annIdealSub_affine π IZ F U (f ^ M • z)).mpr hzann
    refine ⟨⟨c ^ (M + n) • (f ^ M • z),
      annIdealSub_Γsmul π IZ F U.1 _ _ hfMz⟩, Subtype.ext ?_⟩

    have hfcD : (1 : Γ(V, V.basicOpen f)) - ρ c * ρ f ∈ (IZ).ideal (V.affineBasicOpen f) := by
      have h' := (IZ).map_ideal (U := V.affineBasicOpen f) (V := U) (V.basicOpen_le f)
        ▸ Ideal.mem_map_of_mem ρ hfc
      rwa [map_sub, map_one, map_mul] at h'
    show F.res (V.basicOpen_le f) (c ^ (M + n) • (f ^ M • z)) = y.1
    rw [F.res_smul, F.res_smul, hz]
    show ρ (c ^ (M + n)) • ρ (f ^ M) • ρ (f ^ n) • y.1 = y.1
    rw [map_pow, map_pow, map_pow, ← mul_smul, ← mul_smul, mul_assoc, ← pow_add, ← mul_pow]
    exact G₂_cf_id π Z F (V.affineBasicOpen f) (ρ f) (ρ c) hfcD y (M + n)

theorem G₂_res_bij_basicOpen' [IsLocallyNoetherian V]
    (hFq : OModulePresheaf.IsQuasicoherent F) (U : V.affineOpens) (f : Γ(V, U.1))
    (hf : ((U : V.Opens) : Set V) ∩ Z ⊆ V.basicOpen f) {W : V.Opens}
    (hW : W = V.basicOpen f) (hWle : W ≤ U.1) :
    Function.Bijective ((G₂ π Z F).res (U := W) hWle) := by
  subst hW; exact G₂_res_bij_basicOpen π Z F hFq U f hf

theorem G₂_res_bij [IsSeparated π] [IsLocallyNoetherian V]
    (hFq : OModulePresheaf.IsQuasicoherent F) {U U' : V.affineOpens} (hle : U'.1 ≤ U.1)
    (hdisj : (((U : V.Opens) : Set V) \ U'.1) ∩ Z = ∅) :
    Function.Bijective ((G₂ π Z F).res (U := U'.1) (U' := U.1) hle) := by

  set C : Opens (PrimeSpectrum Γ(V, U.1)) := U.2.fromSpec ⁻¹ᵁ U'.1
  set Cc : Set (PrimeSpectrum Γ(V, U.1)) := (↑C)ᶜ
  have hScl : IsClosed (U.2.fromSpec ⁻¹' (Z : Set V)) := Z.2.preimage U.2.fromSpec.continuous
  have hzl : PrimeSpectrum.zeroLocus
      (↑(PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set V))) : Set Γ(V, U.1))
      = U.2.fromSpec ⁻¹' (Z : Set V) :=
    (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).trans hScl.closure_eq
  have hzlC : PrimeSpectrum.zeroLocus
      (↑(PrimeSpectrum.vanishingIdeal Cc) : Set Γ(V, U.1)) = Cc :=
    (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).trans C.2.isClosed_compl.closure_eq
  have htop : PrimeSpectrum.vanishingIdeal Cc ⊔ (IZ).ideal U = ⊤ := by
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
    by_contra habs
    obtain ⟨m, hmax, hmle⟩ := Ideal.exists_le_maximal _ habs
    set p : PrimeSpectrum Γ(V, U.1) := ⟨m, hmax.isPrime⟩
    have hpZ : p ∈ U.2.fromSpec ⁻¹' (Z : Set V) :=
      hzl ▸ fun a ha => hmle (Ideal.mem_sup_right ha)
    have hpCc : p ∈ Cc := hzlC ▸ fun a ha => hmle (Ideal.mem_sup_left ha)
    exact Set.eq_empty_iff_forall_notMem.mp hdisj (U.2.fromSpec p)
      ⟨⟨U.2.range_fromSpec ▸ Set.mem_range_self p, fun h => hpCc h⟩, Set.mem_preimage.mp hpZ⟩

  obtain ⟨j, hj, a, ha, hja⟩ := Submodule.mem_sup.mp
    (htop ▸ (Submodule.mem_top : (1 : Γ(V, U.1)) ∈ _))
  have hjU' : V.basicOpen j ≤ U'.1 := fun x hx => by
    obtain ⟨p, rfl⟩ : x ∈ Set.range U.2.fromSpec :=
      U.2.range_fromSpec ▸ (V.basicOpen_le j hx)
    have hp : p ∈ PrimeSpectrum.basicOpen j :=
      U.2.fromSpec_preimage_basicOpen j ▸ (hx : p ∈ U.2.fromSpec ⁻¹ᵁ V.basicOpen j)
    by_contra hpc
    exact (PrimeSpectrum.mem_basicOpen j p).mp hp
      ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hj p hpc)
  have hfZ : ((U : V.Opens) : Set V) ∩ Z ⊆ V.basicOpen j := fun x ⟨hxU, hxZ⟩ => by
    obtain ⟨p, rfl⟩ := U.2.range_fromSpec ▸ hxU
    have hap : a ∈ p.asIdeal := by
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal] at ha
      exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp ha p (Set.mem_preimage.mpr hxZ)
    have hjp : j ∉ p.asIdeal := fun hjp =>
      p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ (hja ▸ p.asIdeal.add_mem hjp hap) isUnit_one)
    show p ∈ U.2.fromSpec ⁻¹ᵁ V.basicOpen j
    rw [U.2.fromSpec_preimage_basicOpen j]
    exact (PrimeSpectrum.mem_basicOpen j p).mpr hjp

  let j' := (V.presheaf.map (homOfLE hle).op).hom j
  have heq : V.basicOpen j' = V.basicOpen j :=
    (Scheme.basicOpen_res _ _ _).trans (inf_eq_right.mpr hjU')
  have hfZ' : ((U' : V.Opens) : Set V) ∩ Z ⊆ V.basicOpen j' :=
    fun x ⟨hxU', hxZ⟩ => heq.symm ▸ hfZ ⟨hle hxU', hxZ⟩
  have h1 : Function.Bijective
      ((G₂ π Z F).res (U := V.basicOpen j) (V.basicOpen_le j)) :=
    G₂_res_bij_basicOpen' π Z F hFq U j hfZ rfl (V.basicOpen_le j)
  have h2 : Function.Bijective
      ((G₂ π Z F).res (U := V.basicOpen j) (U' := U'.1) hjU') :=
    G₂_res_bij_basicOpen' π Z F hFq U' j' hfZ' heq.symm hjU'
  have hcomp : ⇑((G₂ π Z F).res (U := V.basicOpen j) (V.basicOpen_le j))
      = ⇑((G₂ π Z F).res hjU') ∘ ⇑((G₂ π Z F).res hle) := by
    rw [← LinearMap.coe_comp]
    exact congrArg _ ((G₂ π Z F).res_comp hjU' hle)
  exact (h2.of_comp_iff' _).mp (hcomp ▸ h1)

@[reducible]
def G₂_modZ (U : V.affineOpens) :
    Module Γ((IZ).subscheme, iZ ⁻¹ᵁ U.1) ((G₂ π Z F).obj U.1) := by
  letI : SMul Γ((IZ).subscheme, iZ ⁻¹ᵁ U.1) ((G₂ π Z F).obj U.1) :=
    ⟨fun s x => (((IZ).subschemeι_app_surjective U s).choose : Γ(V, U.1)) • x⟩
  refine Function.Surjective.moduleLeft ((IZ).subschemeι.app U.1).hom
    ((IZ).subschemeι_app_surjective U) fun c x => Subtype.ext ?_
  set c' := ((IZ).subschemeι_app_surjective U (((IZ).subschemeι.app U.1).hom c)).choose
  have hker : c' - c ∈ (IZ).ideal U := by
    rw [← (IZ).ker_subschemeι_app U, RingHom.mem_ker, map_sub,
      ((IZ).subschemeι_app_surjective U _).choose_spec, sub_self]
  show c' • x.1 = c • x.1
  have := G₂_ann π Z F U x (c' - c) hker
  rwa [sub_smul, sub_eq_zero] at this

theorem G₂_modZ_smul (U : V.affineOpens) (c : Γ(V, U.1))
    (x : (G₂ π Z F).obj U.1) :
    letI := G₂_modZ π Z F U
    ((IZ).subschemeι.app U.1).hom c • x = c • x := Subtype.ext <| by
  set c' := ((IZ).subschemeι_app_surjective U (((IZ).subschemeι.app U.1).hom c)).choose
  have hker : c' - c ∈ (IZ).ideal U := by
    rw [← (IZ).ker_subschemeι_app U, RingHom.mem_ker, map_sub,
      ((IZ).subschemeι_app_surjective U _).choose_spec, sub_self]
  show c' • x.1 = c • x.1
  have := G₂_ann π Z F U x (c' - c) hker
  rwa [sub_smul, sub_eq_zero] at this

def annPullIdx (W : (IZ).subscheme.Opens) : Type u :=
  { U : V.affineOpens // iZ ⁻¹ᵁ U.1 ≤ W }

@[reducible]
def G₂_modZW (W : (IZ).subscheme.Opens) (U : annPullIdx Z W) :
    Module Γ((IZ).subscheme, W) ((G₂ π Z F).obj U.1.1) :=
  letI := G₂_modZ π Z F U.1
  Module.compHom _ ((IZ).subscheme.presheaf.map (homOfLE U.2).op).hom

def annPullSub (W : (IZ).subscheme.Opens) :
    Submodule R (∀ U : annPullIdx Z W, (G₂ π Z F).obj U.1.1) where
  carrier := {x | ∀ (U U' : annPullIdx Z W) (h : U.1.1 ≤ U'.1.1),
    (G₂ π Z F).res h (x U') = x U}
  add_mem' := fun {x y} hx hy U U' h => by
    show (G₂ π Z F).res h (x U' + y U') = x U + y U
    rw [map_add, hx U U' h, hy U U' h]
  zero_mem' := fun U U' h => by
    show (G₂ π Z F).res h 0 = 0; exact map_zero _
  smul_mem' := fun c x hx U U' h => by
    show (G₂ π Z F).res h (c • x U') = c • x U
    rw [map_smul, hx U U' h]

theorem G₂_modZW_smul (W : (IZ).subscheme.Opens)
    (U : annPullIdx Z W) (c : Γ((IZ).subscheme, W)) (ℓ : Γ(V, U.1.1))
    (hℓ : ((IZ).subschemeι.app U.1.1).hom ℓ
      = ((IZ).subscheme.presheaf.map (homOfLE U.2).op).hom c)
    (x : (G₂ π Z F).obj U.1.1) :
    letI := G₂_modZW π Z F W U
    c • x = ℓ • x := by
  letI := G₂_modZ π Z F U.1
  show ((IZ).subscheme.presheaf.map (homOfLE U.2).op).hom c • x = ℓ • x
  rw [← hℓ]; exact G₂_modZ_smul π Z F U.1 ℓ x

theorem annPullSub_Γsmul (W : (IZ).subscheme.Opens) (c : Γ((IZ).subscheme, W))
    (x : ∀ U : annPullIdx Z W, (G₂ π Z F).obj U.1.1)
    (hx : x ∈ annPullSub π Z F W) :
    letI := fun U => G₂_modZW π Z F W U
    (fun U => c • x U) ∈ annPullSub π Z F W := fun U U' h => by
  letI := fun V₀ => G₂_modZW π Z F W V₀

  obtain ⟨ℓ', hℓ'⟩ := (IZ).subschemeι_app_surjective U'.1
    (((IZ).subscheme.presheaf.map (homOfLE U'.2).op).hom c)
  have hnat : ((IZ).subschemeι.app U.1.1).hom ((V.presheaf.map (homOfLE h).op).hom ℓ')
      = ((IZ).subscheme.presheaf.map (homOfLE U.2).op).hom c := by
    rw [← CommRingCat.comp_apply, (IZ).subschemeι.naturality, CommRingCat.comp_apply, hℓ',
      ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  show (G₂ π Z F).res h (c • x U') = c • x U
  rw [G₂_modZW_smul π Z F W U' c ℓ' hℓ' (x U'),
    (G₂ π Z F).res_smul h ℓ' (x U'), hx U U' h,
    G₂_modZW_smul π Z F W U c _ hnat (x U)]

@[reducible]
def annPullΓmod (W : (IZ).subscheme.Opens) :
    Module Γ((IZ).subscheme, W) (annPullSub π Z F W) :=
  letI := fun U => G₂_modZW π Z F W U
  letI : Module Γ((IZ).subscheme, W)
      (∀ U : annPullIdx Z W, (G₂ π Z F).obj U.1.1) :=
    Pi.module _ _ _
  { smul := fun c x => ⟨fun U => c • x.1 U, annPullSub_Γsmul π Z F W c x.1 x.2⟩
    one_smul := fun x => Subtype.ext (funext fun U => one_smul _ _)
    mul_smul := fun a b x => Subtype.ext (funext fun U => mul_smul a b _)
    smul_zero := fun a => Subtype.ext (funext fun U => smul_zero a)
    smul_add := fun a x y => Subtype.ext (funext fun U => smul_add a _ _)
    add_smul := fun a b x => Subtype.ext (funext fun U => add_smul a b _)
    zero_smul := fun x => Subtype.ext (funext fun U => zero_smul _ _) }

def annPullPMod : OModulePresheaf (iZ ≫ π) where
  obj W := annPullSub π Z F W
  addCommGroup W := inferInstance
  module W := inferInstance
  moduleSections W := annPullΓmod π Z F W
  isScalarTower W := by
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) W).toModule
    letI := annPullΓmod π Z F W
    refine ⟨fun r c x => Subtype.ext (funext fun U => ?_)⟩
    letI := G₂_modZW π Z F W U
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1.1).toModule
    haveI := (G₂ π Z F).isScalarTower U.1.1
    show (r • c) • x.1 U = r • (c • x.1 U)
    obtain ⟨ℓ, hℓ⟩ := (IZ).subschemeι_app_surjective U.1
      (((IZ).subscheme.presheaf.map (homOfLE U.2).op).hom c)
    have hrℓ : ((IZ).subschemeι.app U.1.1).hom (r • ℓ)
        = ((IZ).subscheme.presheaf.map (homOfLE U.2).op).hom (r • c) := by
      letI := Scheme.TwoAffineOpenCover.algebraOfHom π U.1.1
      letI := Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) W
      letI := Scheme.TwoAffineOpenCover.algebraOfHom (iZ ≫ π) (iZ ⁻¹ᵁ U.1.1)
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, hℓ]
      refine congrArg (· * _) (Eq.trans ?_
        (?_ : _ = algebraMap R Γ((IZ).subscheme, iZ ⁻¹ᵁ U.1.1) r).symm)
      · rw [Scheme.Hom.app_eq_appLE]
        exact OModulePresheaf.appLE_algebraMap (iZ) U.1.1 r
      · exact (Scheme.TwoAffineOpenCover.restrictAlgHom (iZ ≫ π) U.2).commutes r
    rw [G₂_modZW_smul π Z F W U (r • c) (r • ℓ) hrℓ (x.1 U),
      G₂_modZW_smul π Z F W U c ℓ hℓ (x.1 U), smul_assoc]
  res {W W'} h :=
    { toFun := fun x => ⟨fun U => x.1 ⟨U.1, U.2.trans h⟩,
        fun U U' hle => x.2 ⟨U.1, U.2.trans h⟩ ⟨U'.1, U'.2.trans h⟩ hle⟩
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  res_smul {W W'} h c x := Subtype.ext (funext fun U => by
    letI := G₂_modZW π Z F W' ⟨U.1, U.2.trans h⟩
    letI := G₂_modZW π Z F W U
    show (c • x.1 ⟨U.1, U.2.trans h⟩ : (G₂ π Z F).obj U.1.1)
      = ((IZ).subscheme.presheaf.map (homOfLE h).op).hom c • x.1 ⟨U.1, U.2.trans h⟩
    obtain ⟨ℓ, hℓ⟩ := (IZ).subschemeι_app_surjective U.1
      (((IZ).subscheme.presheaf.map (homOfLE (U.2.trans h)).op).hom c)
    rw [G₂_modZW_smul π Z F W' ⟨U.1, U.2.trans h⟩ c ℓ hℓ,
      G₂_modZW_smul π Z F W U _ ℓ
        (hℓ.trans (by rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl))])
  res_refl W := LinearMap.ext fun x => Subtype.ext (funext fun U => by
    show x.1 ⟨U.1, _⟩ = x.1 U; congr 1)
  res_comp h h' := LinearMap.ext fun x => Subtype.ext (funext fun U => by
    show x.1 ⟨U.1, _⟩ = x.1 ⟨U.1, _⟩; congr 1)

def annPull_eval (U : V.affineOpens) :
    (annPullPMod π Z F).obj (iZ ⁻¹ᵁ U.1) →ₗ[R] (G₂ π Z F).obj U.1 where
  toFun x := x.1 ⟨U, le_rfl⟩
  map_add' x y := rfl
  map_smul' c x := rfl

theorem preimage_le_hdisj {U U' : V.Opens} (h : iZ ⁻¹ᵁ U' ≤ iZ ⁻¹ᵁ U) :
    ((U' : Set V) \ U) ∩ Z = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]; rintro x ⟨⟨hxU', hxU⟩, hxZ⟩
  obtain ⟨z, rfl⟩ : x ∈ Set.range iZ := (IZ).range_subschemeι.symm ▸
    (show x ∈ ((IZ).support : Set V) from
      Scheme.IdealSheafData.coe_support_vanishingIdeal Z ▸ hxZ)
  exact hxU (h hxU')

theorem annPull_eval_bij [IsSeparated π] [IsLocallyNoetherian V]
    (hFq : OModulePresheaf.IsQuasicoherent F) (U : V.affineOpens) :
    Function.Bijective (annPull_eval π Z F U) := by

  let V₀ : annPullIdx Z (iZ ⁻¹ᵁ U.1) → annPullIdx Z (iZ ⁻¹ᵁ U.1) :=
    fun U' => ⟨⟨U'.1.1 ⊓ U.1, Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated π U'.1.2 U.2⟩,
      (Opens.map (iZ).base).monotone inf_le_right⟩
  have hbij : ∀ U', Function.Bijective
      ((G₂ π Z F).res (U := (V₀ U').1.1) (U' := U'.1.1) inf_le_left) := fun U' =>
    G₂_res_bij π Z F hFq (U := U'.1) (U' := (V₀ U').1) inf_le_left
      (by simpa only [Opens.coe_inf, Set.diff_self_inter, V₀]
        using preimage_le_hdisj Z U'.2)
  refine ⟨fun x y hxy => Subtype.ext (funext fun U' => (hbij U').1 ?_), fun y => ?_⟩
  ·
    rw [x.2 (V₀ U') U' inf_le_left, y.2 (V₀ U') U' inf_le_left,
      ← x.2 (V₀ U') ⟨U, le_rfl⟩ inf_le_right, ← y.2 (V₀ U') ⟨U, le_rfl⟩ inf_le_right]
    exact congrArg _ hxy
  ·
    let e := fun U' => Equiv.ofBijective _ (hbij U')
    have hsymm : ∀ U' w, (G₂ π Z F).res (U' := U'.1.1) inf_le_left
        ((e U').symm w) = w := fun U' w => (e U').apply_symm_apply w
    refine ⟨⟨fun U' => (e U').symm ((G₂ π Z F).res inf_le_right y),
      fun U'' U' hle => (hbij U'').1 ?_⟩, (e ⟨U, le_rfl⟩).symm_apply_eq.mpr rfl⟩

    rw [hsymm U'', ← LinearMap.comp_apply, ← (G₂ π Z F).res_comp inf_le_left hle,
      (G₂ π Z F).res_comp
        (inf_le_inf_right U.1 hle : (V₀ U'').1.1 ≤ (V₀ U').1.1) inf_le_left,
      LinearMap.comp_apply, hsymm U', ← LinearMap.comp_apply,
      ← (G₂ π Z F).res_comp]

end AnnPull

section QuotG3

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
variable (Z : Closeds V) (F : OModulePresheaf π)

local notation "IZ" => Scheme.IdealSheafData.vanishingIdeal Z

@[reducible]
def quotAnnΓmod (U : V.Opens) :
    Module Γ(V, U) (F.obj U ⧸ annIdealSub π IZ F U) := by
  set p := annIdealSub π IZ F U
  letI : SMul Γ(V, U) (F.obj U ⧸ p) :=
    { smul := fun a => Quotient.map' (a • ·) fun x y h => by
        rw [Submodule.quotientRel_def] at h ⊢
        rw [← smul_sub]; exact annIdealSub_Γsmul π IZ F U a (x - y) h }
  have key : ∀ (a : Γ(V, U)) (y : F.obj U), a • p.mkQ y = p.mkQ (a • y) := fun _ _ => rfl
  exact
  { smul := (· • ·)
    one_smul := fun x => by obtain ⟨y, rfl⟩ := p.mkQ_surjective x; rw [key, one_smul]
    mul_smul := fun a b x => by
      obtain ⟨y, rfl⟩ := p.mkQ_surjective x; rw [key, key, key, mul_smul]
    smul_zero := fun a => by rw [← map_zero p.mkQ, key, smul_zero]
    smul_add := fun a x₁ x₂ => by
      obtain ⟨y₁, rfl⟩ := p.mkQ_surjective x₁; obtain ⟨y₂, rfl⟩ := p.mkQ_surjective x₂
      rw [← map_add, key, smul_add, map_add, key, key]
    add_smul := fun a b x => by
      obtain ⟨y, rfl⟩ := p.mkQ_surjective x; rw [key, key, key, ← map_add, add_smul]
    zero_smul := fun x => by
      obtain ⟨y, rfl⟩ := p.mkQ_surjective x; rw [key, zero_smul, map_zero] }

theorem quotAnnΓmod_mk (U : V.Opens) (a : Γ(V, U)) (y : F.obj U) :
    letI := quotAnnΓmod π Z F U
    a • (annIdealSub π IZ F U).mkQ y
      = (annIdealSub π IZ F U).mkQ (a • y) :=
  rfl

def quotAnnPMod : OModulePresheaf π where
  obj U := F.obj U ⧸ annIdealSub π IZ F U
  addCommGroup U := inferInstance
  module U := inferInstance
  moduleSections U := quotAnnΓmod π Z F U
  isScalarTower U := by
    letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U).toModule; letI := quotAnnΓmod π Z F U
    haveI := F.isScalarTower U
    refine ⟨fun r a x => ?_⟩
    obtain ⟨y, rfl⟩ := (annIdealSub π IZ F U).mkQ_surjective x
    rw [quotAnnΓmod_mk, quotAnnΓmod_mk, ← map_smul, smul_assoc]
  res h := Submodule.mapQ _ _ (F.res h) (fun x hx => annIdealSub_res π IZ F h x hx)
  res_smul {U U'} h a x := by
    letI := quotAnnΓmod π Z F U'
    letI := quotAnnΓmod π Z F U
    obtain ⟨y, rfl⟩ := (annIdealSub π IZ F U').mkQ_surjective x
    rw [quotAnnΓmod_mk]
    show (annIdealSub π IZ F U).mkQ (F.res h (a • y)) = _
    rw [F.res_smul h a y, ← quotAnnΓmod_mk]
    rfl
  res_refl U := by
    refine LinearMap.ext fun x => Quotient.inductionOn' x fun y => ?_
    exact congrArg (Submodule.Quotient.mk) (LinearMap.congr_fun (F.res_refl U) y)
  res_comp h h' := by
    refine LinearMap.ext fun x => Quotient.inductionOn' x fun y => ?_
    exact congrArg (Submodule.Quotient.mk) (LinearMap.congr_fun (F.res_comp h h') y)

def devSES [IsSeparated π] [IsLocallyNoetherian V]
    (hFq : OModulePresheaf.IsQuasicoherent F) :
    OModulePresheaf.AffSES
      (OModulePresheaf.pushforward π (subschemeInc Z) (annPullPMod π Z F))
      F (quotAnnPMod π Z F) where
  inc :=
    { app := fun U => (annIdealSub π IZ F U.1).subtype
        ∘ₗ annPull_eval π Z F U
      app_smul := fun U a x => by

        have key := G₂_modZW_smul π Z F (subschemeInc Z ⁻¹ᵁ U.1) ⟨U, le_rfl⟩
          (((IZ).subschemeι.appLE U.1 _ le_rfl).hom a) a
          (by rw [← Scheme.Hom.app_eq_appLE,
                show (homOfLE (le_rfl : _ ≤ subschemeInc Z ⁻¹ᵁ U.1)).op = 𝟙 _ from rfl,
                (IZ).subscheme.presheaf.map_id]; rfl)
          (x.1 ⟨U, le_rfl⟩)
        exact congrArg Subtype.val key
      naturality := fun {U U'} h => LinearMap.ext fun x =>
        (congrArg Subtype.val (x.2 ⟨U, (Opens.map (subschemeInc Z).base).monotone h⟩
          ⟨U', le_rfl⟩ h)).symm }
  proj :=
    { app := fun U => (annIdealSub π IZ F U.1).mkQ
      app_smul := fun U a x => (quotAnnΓmod_mk π Z F U.1 a x).symm
      naturality := fun {U U'} h => rfl }
  injective := fun U => Subtype.val_injective.comp (annPull_eval_bij π Z F hFq U).1
  surjective := fun U => Submodule.mkQ_surjective _
  exact := fun U => le_antisymm
    (LinearMap.range_le_ker_iff.mpr (LinearMap.ext fun x =>
      (Submodule.Quotient.mk_eq_zero _).mpr (x.1 ⟨U, le_rfl⟩).2))
    (fun y hy => by
      obtain ⟨x, hx⟩ := (annPull_eval_bij π Z F hFq U).2
        ⟨y, (Submodule.Quotient.mk_eq_zero _).mp hy⟩
      exact ⟨x, congrArg Subtype.val hx⟩)

theorem annPull_eval_Γsmul [IsSeparated π] [IsLocallyNoetherian V]
    (hFq : OModulePresheaf.IsQuasicoherent F) (U : V.affineOpens) (a : Γ(V, U.1))
    (x : (OModulePresheaf.pushforward π (subschemeInc Z)
      (annPullPMod π Z F)).obj U.1) :
    annPull_eval π Z F U (a • x) = a • annPull_eval π Z F U x :=
  Subtype.val_injective ((devSES π Z F hFq).inc.app_smul U a x)

theorem annPull_eval_nat {U U' : V.affineOpens} (h : U.1 ≤ U'.1)
    (x : (OModulePresheaf.pushforward π (subschemeInc Z)
      (annPullPMod π Z F)).obj U'.1) :
    annPull_eval π Z F U
        ((OModulePresheaf.pushforward π (subschemeInc Z)
          (annPullPMod π Z F)).res h x)
      = (annIdealPMod π IZ F).res h (annPull_eval π Z F U' x) :=
  (x.2 ⟨U, (Opens.map (subschemeInc Z).base).monotone h⟩ ⟨U', le_rfl⟩ h).symm

theorem closedPushAnnPull_isCoherent [IsSeparated π] [IsLocallyNoetherian V]
    (hFc : OModulePresheaf.IsCoherent F) (hFq : OModulePresheaf.IsQuasicoherent F) :
    OModulePresheaf.IsCoherent (OModulePresheaf.pushforward π (subschemeInc Z)
      (annPullPMod π Z F)) := fun U => by
  haveI := IsLocallyNoetherian.component_noetherian U; haveI := hFc U
  exact Module.Finite.of_injective
    ({ toFun := (devSES π Z F hFq).inc.app U, map_add' := map_add _
       map_smul' := (devSES π Z F hFq).inc.app_smul U } : _ →ₗ[Γ(V, U.1)] F.obj U.1)
    ((devSES π Z F hFq).injective U)

theorem closedPushAnnPull_isQCF [IsSeparated π] [IsLocallyNoetherian V]
    (hFq : OModulePresheaf.IsQuasicoherent F) :
    OModulePresheaf.IsQuasicoherent (OModulePresheaf.pushforward π (subschemeInc Z)
      (annPullPMod π Z F)) := fun U f => by
  have hbijU := annPull_eval_bij π Z F hFq U
  have hbijD := annPull_eval_bij π Z F hFq (V.affineBasicOpen f)
  have hnat := annPull_eval_nat π Z F (U := V.affineBasicOpen f) (U' := U)
    (V.basicOpen_le f)
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨n, z, hz⟩ := (annIdealPMod_isQCF π IZ F hFq U f).1
      (annPull_eval π Z F (V.affineBasicOpen f) x)
    obtain ⟨y, hy⟩ := hbijU.2 z
    exact ⟨n, y, hbijD.1 <| (hnat y).trans <| (congrArg _ hy).trans <| hz.trans
      (annPull_eval_Γsmul π Z F hFq (V.affineBasicOpen f) _ x).symm⟩
  · obtain ⟨n, hn⟩ := (annIdealPMod_isQCF π IZ F hFq U f).2
      (annPull_eval π Z F U y)
      ((hnat y).symm.trans <| (congrArg _ hy).trans
        (annPull_eval π Z F (V.affineBasicOpen f)).map_zero)
    exact ⟨n, hbijU.1 <| (annPull_eval_Γsmul π Z F hFq U _ y).trans <|
      hn.trans (annPull_eval π Z F U).map_zero.symm⟩

theorem closedPushAnnPull_suppIn [IsSeparated π] [IsLocallyNoetherian V]
    (hFq : OModulePresheaf.IsQuasicoherent F) :
    OModulePresheaf.SupportedIn (OModulePresheaf.pushforward π (subschemeInc Z)
      (annPullPMod π Z F)) Z := fun U hU => by
  haveI := annIdealPMod_suppIn π Z F U hU
  exact (annPull_eval_bij π Z F hFq U).1.subsingleton

theorem quotAnnPMod_isCoherent [IsLocallyNoetherian V]
    (hFc : OModulePresheaf.IsCoherent F) :
    OModulePresheaf.IsCoherent (quotAnnPMod π Z F) := fun U => by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; haveI := F.isScalarTower U.1
  haveI := IsLocallyNoetherian.component_noetherian U
  haveI := hFc U
  let mkΓ : F.obj U.1 →ₗ[Γ(V, U.1)] (quotAnnPMod π Z F).obj U.1 :=
    { toFun := (annIdealSub π IZ F U.1).mkQ
      map_add' := map_add _
      map_smul' := fun a y => (quotAnnΓmod_mk π Z F U.1 a y).symm }
  exact Module.Finite.of_surjective mkΓ (Submodule.mkQ_surjective _)

theorem quotAnnPMod_isQCF [IsLocallyNoetherian V]
    (hFq : OModulePresheaf.IsQuasicoherent F) :
    OModulePresheaf.IsQuasicoherent (quotAnnPMod π Z F) := fun U f => by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; haveI := F.isScalarTower U.1
  haveI := IsLocallyNoetherian.component_noetherian U
  set Df : V.affineOpens := ⟨V.basicOpen f, U.2.basicOpen f⟩
  let ρ := (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  ·
    obtain ⟨x', rfl⟩ := (annIdealSub π IZ F Df.1).mkQ_surjective x
    obtain ⟨n, z, hz⟩ := (hFq U f).1 x'
    exact ⟨n, (annIdealSub π IZ F U.1).mkQ z,
      (congrArg _ hz).trans (quotAnnΓmod_mk π Z F Df.1 _ x').symm⟩
  ·
    obtain ⟨y', rfl⟩ := (annIdealSub π IZ F U.1).mkQ_surjective y
    have hy' : F.res (V.basicOpen_le f) y' ∈ annIdealSub π IZ F Df.1 :=
      (Submodule.Quotient.mk_eq_zero _).mp hy
    have hres0 : ∀ a ∈ (IZ).ideal U, F.res (V.basicOpen_le f) (a • y') = 0 := fun a ha => by
      have hρa : ρ a ∈ (IZ).ideal Df :=
        (IZ).map_ideal (U := Df) (V := U) (V.basicOpen_le f) ▸ Ideal.mem_map_of_mem ρ ha
      rw [F.res_smul]
      exact (annIdealSub_affine π IZ F Df _).mp hy' (ρ a) hρa
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian ((IZ).ideal U) : ((IZ).ideal U).FG)
    choose Ma hMa using fun a : s =>
      (hFq U f).2 (a.1 • y') (hres0 a.1 (hs ▸ Ideal.subset_span a.2))
    refine ⟨s.attach.sup Ma, (Submodule.Quotient.mk_eq_zero _).mpr
      ((annIdealSub_affine π IZ F U (f ^ s.attach.sup Ma • y')).mpr
        fun a ha => ?_)⟩
    rw [← hs] at ha
    refine Submodule.span_induction (fun b hb => ?_) (by rw [zero_smul])
      (fun b₁ b₂ _ _ h₁ h₂ => by rw [add_smul, h₁, h₂, add_zero])
      (fun d b _ hb => by rw [smul_eq_mul, mul_smul, hb, smul_zero]) ha
    have hle : Ma ⟨b, hb⟩ ≤ s.attach.sup Ma := Finset.le_sup (Finset.mem_attach s ⟨b, hb⟩)
    rw [smul_comm, ← Nat.sub_add_cancel hle, pow_add, mul_smul, hMa ⟨b, hb⟩, smul_zero]

theorem quotAnnPMod_subsingleton (U : V.affineOpens)
    (hAnn : ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal Z).ideal U, ∀ x : F.obj U.1, a • x = 0) :
    Subsingleton ((quotAnnPMod π Z F).obj U.1) := by
  have htop : annIdealSub π IZ F U.1 = ⊤ := top_unique fun x _ =>
    (annIdealSub_affine π IZ F U x).mpr fun a ha => hAnn a ha x
  exact ⟨fun x y => by
    obtain ⟨x', rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y', rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact (Submodule.Quotient.eq _).mpr (htop ▸ Submodule.mem_top)⟩

end QuotG3

theorem devStep'_exists {R : Type u} [CommRing R] [IsNoetherianRing R]
    {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π] [IsNoetherian V]
    (F : OModulePresheaf π) (hFc : OModulePresheaf.IsCoherent F)
    (hFq : OModulePresheaf.IsQuasicoherent F) (Y : Closeds V)
    (hYne : (Y : Set V).Nonempty) (hFs : OModulePresheaf.SupportedIn F Y)
    (hAnn : ∀ U : V.affineOpens, ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal Y).ideal U,
      ∀ x : F.obj U.1, a • x = 0) :
    Nonempty (OModulePresheaf.DevissageStep F Y) := by

  obtain ⟨S, hSirr, hSeq⟩ := NoetherianSpace.exists_finset_irreducible Y
  have hSne : S.Nonempty := Finset.nonempty_of_ne_empty fun hS => hYne.ne_empty
    (congrArg SetLike.coe (hSeq.trans (hS ▸ Finset.sup_empty)))
  obtain ⟨Z₀, hZ₀S, hZ₀max⟩ := S.exists_maximal hSne
  have hZ₀irr : IsIrreducible (Z₀ : Set V) := hSirr ⟨Z₀, hZ₀S⟩
  have hZ₀le : Z₀ ≤ Y := hSeq ▸ Finset.le_sup (f := id) hZ₀S

  let Z₁ : Closeds V := ⟨closure ((Y : Set V) \ Z₀), isClosed_closure⟩
  have hZ₁le : Z₁ ≤ Y := Y.2.closure_subset_iff.mpr Set.diff_subset
  have hZ₀not : ¬ (Z₀ : Set V) ⊆ Z₁ := fun hZ₀Z₁ => by
    classical

    have hcov : (Y : Set V) \ Z₀ ⊆ ↑((S.erase Z₀).sup id) := fun y ⟨hyY, hyZ₀⟩ => by
      have : y ∈ (↑(S.sup id) : Set V) := hSeq ▸ hyY
      simp only [Closeds.coe_finset_sup, id, Function.comp_def, Finset.sup_set_eq_biUnion,
        Set.mem_iUnion, exists_prop] at this ⊢
      obtain ⟨Z', hZ'S, hyZ'⟩ := this
      exact ⟨Z', Finset.mem_erase.mpr ⟨fun h => hyZ₀ (h ▸ hyZ'), hZ'S⟩, hyZ'⟩
    have hZ₀cov : (Z₀ : Set V) ⊆ ↑((S.erase Z₀).sup id) :=
      hZ₀Z₁.trans (((S.erase Z₀).sup id).2.closure_subset_iff.mpr hcov)

    have hsU : (↑((S.erase Z₀).sup id) : Set V)
        = ⋃₀ ↑((S.erase Z₀).image (SetLike.coe : Closeds V → Set V)) := by
      simp [Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.sUnion_image, and_comm]
    obtain ⟨t, htT, hZ₀t⟩ := (isIrreducible_iff_sUnion_isClosed.mp hZ₀irr)
      ((S.erase Z₀).image SetLike.coe)
      (fun z hz => by obtain ⟨Z', _, rfl⟩ := Finset.mem_image.mp hz; exact Z'.2)
      (hsU ▸ hZ₀cov)
    obtain ⟨Z', hZ'e, rfl⟩ := Finset.mem_image.mp htT
    exact (Finset.mem_erase.mp hZ'e).1
      (le_antisymm (hZ₀max (Finset.mem_of_mem_erase hZ'e) hZ₀t) hZ₀t)
  refine ⟨{
    Z₀ := Z₀
    isIntegral := Scheme.isIntegral_subscheme_vanishingIdeal Z₀ hZ₀irr
    Z₀_le := hZ₀le
    Z₀_nonempty := hZ₀irr.nonempty
    H := annPullPMod π Z₀ F
    isCoherent_pushforward := closedPushAnnPull_isCoherent π Z₀ F hFc hFq
    isQuasicoherent_pushforward := closedPushAnnPull_isQCF π Z₀ F hFq
    supportedIn_pushforward := closedPushAnnPull_suppIn π Z₀ F hFq
    G₃ := quotAnnPMod π Z₀ F
    ses := devSES π Z₀ F hFq
    Z₁ := Z₁
    Z₁_lt := lt_of_le_of_ne hZ₁le fun hYZ₁ => hZ₀not (hYZ₁ ▸ hZ₀le)
    isCoherent_G₃ := quotAnnPMod_isCoherent π Z₀ F hFc
    isQuasicoherent_G₃ := quotAnnPMod_isQCF π Z₀ F hFq
    supportedIn_G₃ := fun U hU => quotAnnPMod_subsingleton π Z₀ F U fun a ha x => ?_ }⟩

  have hUY : ((U : V.Opens) : Set V) ∩ Y = ((U : V.Opens) : Set V) ∩ Z₀ :=
    le_antisymm (fun y ⟨hyU, hyY⟩ => ⟨hyU, by_contra fun hyZ₀ =>
        Set.eq_empty_iff_forall_notMem.mp hU y ⟨hyU, subset_closure ⟨hyY, hyZ₀⟩⟩⟩)
      (Set.inter_subset_inter_right _ hZ₀le)
  have hIeq : (Scheme.IdealSheafData.vanishingIdeal Z₀).ideal U
      = (Scheme.IdealSheafData.vanishingIdeal Y).ideal U := by
    rw [Scheme.IdealSheafData.vanishingIdeal_ideal, Scheme.IdealSheafData.vanishingIdeal_ideal]
    congr 1; ext p; constructor <;> intro hp
    · exact (hUY ▸ ⟨U.2.range_fromSpec ▸ Set.mem_range_self p, Set.mem_preimage.mp hp⟩
        : _ ∈ ((U : V.Opens) : Set V) ∩ Y).2
    · exact (hUY ▸ ⟨U.2.range_fromSpec ▸ Set.mem_range_self p, Set.mem_preimage.mp hp⟩
        : _ ∈ ((U : V.Opens) : Set V) ∩ Z₀).2
  exact hAnn U a (hIeq ▸ ha) x

theorem hasDevissageStep : OModulePresheaf.HasDevissageStep.{u} := by
  intro R _ _ V π _ _ F hFc hFq Y hYne hFs hAnn
  exact devStep'_exists π F hFc hFq Y hYne hFs hAnn

end AlgebraicGeometry.OModulePresheaf.G5B

end

universe u

theorem solution : AlgebraicGeometry.OModulePresheaf.HasDevissageStep.{u} :=
  AlgebraicGeometry.OModulePresheaf.G5B.hasDevissageStep

end S_AlgebraicGeometry_OModulePresheaf_hasDevissageStep
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_hasDevissageStep (solution)
