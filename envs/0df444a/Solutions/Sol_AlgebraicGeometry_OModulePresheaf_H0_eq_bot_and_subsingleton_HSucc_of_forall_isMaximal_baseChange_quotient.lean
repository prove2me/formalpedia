-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f80c3396-c236-56c8-80f2-2d5a57e0a433

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace RelAcyclicEngine

variable {B : Type u} [CommRing B]

theorem subsingleton_of_forall_isMaximal (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M]
    (h : ∀ (𝔪 : Ideal B) (_ : 𝔪.IsMaximal), ∀ x : (B ⧸ 𝔪) ⊗[B] M, x = 0) : Subsingleton M := by
  classical
  by_contra hM
  rw [not_subsingleton_iff_nontrivial] at hM
  have hann : Module.annihilator B M ≠ ⊤ := by
    intro htop
    have h1 : (1 : B) ∈ Module.annihilator B M := htop ▸ Submodule.mem_top
    rw [Module.mem_annihilator] at h1
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact hx (by simpa using h1 x)
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hann
  have htop : (𝔪 • ⊤ : Submodule B M) = ⊤ := by
    rw [← Submodule.Quotient.subsingleton_iff]
    refine ⟨fun a b => ?_⟩
    let e := TensorProduct.quotTensorEquivQuotSMul M 𝔪
    rw [← e.apply_symm_apply a, ← e.apply_symm_apply b, h 𝔪 h𝔪 (e.symm a), h 𝔪 h𝔪 (e.symm b)]
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪
    (⊤ : Submodule B M) Module.Finite.fg_top (by rw [htop])
  have hrann : r ∈ Module.annihilator B M := Module.mem_annihilator.2 fun m => hr m trivial
  have h1 : (1 : B) ∈ 𝔪 := by
    have := 𝔪.sub_mem (hle hrann) hr1
    simpa using this
  exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem flat_ker_of_surjective {C P : Type u} [AddCommGroup C] [Module B C] [AddCommGroup P] [Module B P]
    [Module.Flat B C] [Module.Flat B P] (f : C →ₗ[B] P) (hf : Function.Surjective f) :
    Module.Flat B (LinearMap.ker f) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ g hg
  have h1 : Function.Injective ((LinearMap.ker f).subtype.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat f hf _ (LinearMap.ker f).injective_subtype
      (LinearMap.exact_subtype_ker_map f) N
  have h2 : Function.Injective (g.rTensor C) := Module.Flat.rTensor_preserves_injective_linearMap g hg
  have hcomp : ((LinearMap.ker f).subtype.lTensor N') ∘ₗ (g.rTensor (LinearMap.ker f))
      = (g.rTensor C) ∘ₗ ((LinearMap.ker f).subtype.lTensor N) := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have : Function.Injective (((LinearMap.ker f).subtype.lTensor N') ∘ₗ (g.rTensor (LinearMap.ker f))) := by
    rw [hcomp]; exact h2.comp h1
  exact Function.Injective.of_comp this

section Complex

variable (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module B (C i)]
  (d : ∀ i, C i →ₗ[B] C (i + 1))

def dZ (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (i : ℕ) : C i →ₗ[B] LinearMap.ker (d (i + 1)) :=
  (d i).codRestrict (LinearMap.ker (d (i + 1))) fun x => by
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hdd]; rfl

theorem subtype_comp_dZ (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (i : ℕ) :
    (LinearMap.ker (d (i + 1))).subtype ∘ₗ dZ C d hdd i = d i := by
  ext x; rfl

theorem ker_dZ (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (i : ℕ) :
    LinearMap.ker (dZ C d hdd i) = LinearMap.ker (d i) := by
  ext x; simp [dZ]

theorem range_dZ (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (i : ℕ) :
    LinearMap.range (dZ C d hdd i)
      = (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype := by
  ext ⟨x, hx⟩
  simp only [LinearMap.mem_range, Submodule.mem_comap, Submodule.coe_subtype]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩; exact ⟨y, Subtype.ext hy⟩

def Inv (i : ℕ) : Prop :=
  Module.Flat B (LinearMap.ker (d i)) ∧
    ∀ (𝔪 : Ideal B) (_ : 𝔪.IsMaximal),
      Function.Injective ((LinearMap.ker (d i)).subtype.lTensor (B ⧸ 𝔪)) ∧
        LinearMap.range ((LinearMap.ker (d i)).subtype.lTensor (B ⧸ 𝔪))
          = LinearMap.ker ((d i).lTensor (B ⧸ 𝔪))

theorem inv_of_subsingleton (i : ℕ) [Subsingleton (C i)] : Inv C d i := by
  refine ⟨inferInstance, fun 𝔪 _ => ⟨fun a b _ => Subsingleton.elim a b, ?_⟩⟩
  haveI : Subsingleton ((B ⧸ 𝔪) ⊗[B] C i) := inferInstance
  exact Subsingleton.elim _ _

theorem step (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (hflat : ∀ i, Module.Flat B (C i))
    (hfin : ∀ i, Module.Finite B
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib : ∀ (𝔪 : Ideal B) (_ : 𝔪.IsMaximal) (i : ℕ),
      LinearMap.ker ((d (i + 1)).lTensor (B ⧸ 𝔪)) ≤ LinearMap.range ((d i).lTensor (B ⧸ 𝔪)))
    (i : ℕ) (hI : Inv C d (i + 1)) :
    Function.Surjective (dZ C d hdd i) ∧ Inv C d i := by
  classical
  obtain ⟨hZflat, hZ⟩ := hI
  haveI := hZflat
  haveI := hflat i
  set Z := LinearMap.ker (d (i + 1)) with hZdef
  set d' : C i →ₗ[B] Z := dZ C d hdd i with hd'

  have hsurjk : ∀ (𝔪 : Ideal B) (_ : 𝔪.IsMaximal), Function.Surjective (d'.lTensor (B ⧸ 𝔪)) := by
    intro 𝔪 h𝔪 w
    obtain ⟨hinj, hrange⟩ := hZ 𝔪 h𝔪
    have hw : (Z.subtype.lTensor (B ⧸ 𝔪)) w ∈ LinearMap.ker ((d (i + 1)).lTensor (B ⧸ 𝔪)) := by
      rw [← hrange]; exact LinearMap.mem_range_self _ w
    obtain ⟨v, hv⟩ := hfib 𝔪 h𝔪 i hw
    refine ⟨v, hinj ?_⟩
    rw [← hv, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, subtype_comp_dZ]

  have hH : Subsingleton (Z ⧸ LinearMap.range d') := by
    haveI hfinH : Module.Finite B (↥Z ⧸ LinearMap.range d') := by
      have h := hfin i; rwa [← range_dZ C d hdd i] at h
    refine subsingleton_of_forall_isMaximal (B := B) (Z ⧸ LinearMap.range d') fun 𝔪 h𝔪 x => ?_
    obtain ⟨y, rfl⟩ := LinearMap.lTensor_surjective (B ⧸ 𝔪) (LinearMap.range d').mkQ_surjective x
    obtain ⟨v, rfl⟩ := hsurjk 𝔪 h𝔪 y
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : (LinearMap.range d').mkQ ∘ₗ d' = 0 := by
      ext c; simp
    rw [this, LinearMap.lTensor_zero]; rfl
  have hsurj : Function.Surjective d' := by
    rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]; exact hH
  refine ⟨hsurj, ?_, fun 𝔪 h𝔪 => ?_⟩
  ·
    have := flat_ker_of_surjective d' hsurj
    rwa [ker_dZ] at this
  · obtain ⟨hinj, hrange⟩ := hZ 𝔪 h𝔪
    have hex : Function.Exact (LinearMap.ker (d i)).subtype d' := by
      have := LinearMap.exact_subtype_ker_map d'
      rwa [ker_dZ] at this
    refine ⟨?_, ?_⟩
    · exact LinearMap.lTensor_injective_of_exact_of_flat d' hsurj _
        (LinearMap.ker (d i)).injective_subtype hex (B ⧸ 𝔪)
    · rw [← LinearMap.exact_iff.1 (lTensor_exact (B ⧸ 𝔪) hex hsurj)]

      conv_rhs => rw [← subtype_comp_dZ C d hdd i, LinearMap.lTensor_comp]
      exact (LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.2 hinj)).symm

theorem acyclic (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0) (hflat : ∀ i, Module.Flat B (C i))
    (n : ℕ) (hbdd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin0 : Module.Finite B (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite B
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib0 : ∀ (𝔪 : Ideal B) (_ : 𝔪.IsMaximal), LinearMap.ker ((d 0).lTensor (B ⧸ 𝔪)) = ⊥)
    (hfib : ∀ (𝔪 : Ideal B) (_ : 𝔪.IsMaximal) (i : ℕ),
      LinearMap.ker ((d (i + 1)).lTensor (B ⧸ 𝔪)) ≤ LinearMap.range ((d i).lTensor (B ⧸ 𝔪))) :
    LinearMap.ker (d 0) = ⊥ ∧
      ∀ i, Subsingleton
        (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) := by

  have key : ∀ m i, n ≤ i + m → Inv C d i := by
    intro m
    induction m with
    | zero =>
      intro i hi
      haveI := hbdd i (by omega)
      exact inv_of_subsingleton C d i
    | succ m ih =>
      intro i hi
      exact (step C d hdd hflat hfin hfib i (ih (i + 1) (by omega))).2
  have hInv : ∀ i, Inv C d i := fun i => key n i (by omega)
  refine ⟨?_, fun i => ?_⟩
  · obtain ⟨-, hZ⟩ := hInv 0
    haveI := hfin0
    have hsub : Subsingleton (LinearMap.ker (d 0)) :=
      subsingleton_of_forall_isMaximal (B := B) _ fun 𝔪 h𝔪 x => by
        obtain ⟨hinj, hrange⟩ := hZ 𝔪 h𝔪
        rw [hfib0 𝔪 h𝔪, LinearMap.range_eq_bot] at hrange
        apply hinj
        rw [hrange, map_zero, LinearMap.zero_apply]
    exact (Submodule.eq_bot_iff _).2 fun x hx =>
      congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker (d 0)) 0)
  · have hs := (step C d hdd hflat hfin hfib i (hInv (i + 1))).1
    rw [← LinearMap.range_eq_top, range_dZ] at hs
    exact Submodule.Quotient.subsingleton_iff.2 hs

end Complex

end RelAcyclicEngine

namespace RelAcyclicGlue

variable {B : Type u} [CommRing B] {P : Scheme.{u}} (ϖ : P ⟶ Spec (CommRingCat.of B))

theorem inter_zero (𝔚 : P.OrderedAffineCover) (s : 𝔚.Idx 0) : 𝔚.inter s = 𝔚.U (s.1 0) :=
  le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)

def idx0 (𝔚 : P.OrderedAffineCover) (i : 𝔚.ι) : 𝔚.Idx 0 :=
  ⟨fun _ => i, fun a b hab => by
    exfalso; have ha := a.isLt; have hb := b.isLt; rw [Fin.lt_def] at hab; omega⟩

theorem flat_of_forall_flat_sections (𝔚 : P.OrderedAffineCover)
    (hflat : ∀ (i : ℕ) (s : 𝔚.Idx i),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom ϖ (𝔚.inter s); Module.Flat B Γ(P, 𝔚.inter s)) :
    Flat ϖ := by
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat) (f := ϖ)
    (fun s : 𝔚.Idx 0 => ⟨𝔚.inter s, (inter_zero 𝔚 s) ▸ 𝔚.isAffineOpen _⟩) ?_ ?_
  · rw [eq_top_iff, ← 𝔚.iSup_eq_top]
    refine iSup_le fun i => le_iSup_of_le (idx0 𝔚 i) ?_
    change 𝔚.U i ≤ 𝔚.inter (idx0 𝔚 i)
    rw [inter_zero]; rfl
  · intro s
    have h := hflat 0 s
    have := (RingHom.Flat.respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (.of B)).inv
      (ϖ.appLE ⊤ (𝔚.inter s) le_top)).1 ?_
    · exact this
    · exact h

theorem subsingleton_cochain (F : OModulePresheaf ϖ) (𝔚 : P.OrderedAffineCover) (i : ℕ)
    (hi : Fintype.card 𝔚.ι ≤ i) : Subsingleton (F.cochain 𝔚 i) := by
  haveI : IsEmpty (𝔚.Idx i) := ⟨fun s => by
    have := Fintype.card_le_of_injective _ s.2.injective
    simp only [Fintype.card_fin] at this
    omega⟩
  infer_instance

end RelAcyclicGlue

open RelAcyclicGlue in
theorem solution
    {B : Type u} [CommRing B] {P : Scheme.{u}} (ϖ : P ⟶ Spec (CommRingCat.of B)) [IsSeparated ϖ]
    (𝔚 : P.OrderedAffineCover)
    (hflat : ∀ (i : ℕ) (s : 𝔚.Idx i),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom ϖ (𝔚.inter s); Module.Flat B Γ(P, 𝔚.inter s))
    (N : P.Modules) (hN : Scheme.Modules.IsInvertible N)
    (hfin : (OModulePresheaf.ofModules ϖ N).CechFinite 𝔚)
    (hfib : ∀ (𝔪 : Ideal B) (_ : 𝔪.IsMaximal),
      (OModulePresheaf.ofModules (Limits.pullback.snd ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))
          ((Scheme.Modules.pullback (Limits.pullback.fst ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))).obj N)).H0
          (𝔚.baseChange ϖ (B ⧸ 𝔪)) = ⊥ ∧
        ∀ i, Subsingleton
          ((OModulePresheaf.ofModules (Limits.pullback.snd ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))
            ((Scheme.Modules.pullback (Limits.pullback.fst ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))).obj N)).HSucc
            (𝔚.baseChange ϖ (B ⧸ 𝔪)) i)) :
    (OModulePresheaf.ofModules ϖ N).H0 𝔚 = ⊥ ∧ ∀ i, Subsingleton ((OModulePresheaf.ofModules ϖ N).HSucc 𝔚 i) := by
  haveI : Flat ϖ := flat_of_forall_flat_sections ϖ 𝔚 hflat
  have htriv := hN.exists_trivialization
  have hflatC : ∀ i, Module.Flat B ((OModulePresheaf.ofModules ϖ N).cochain 𝔚 i) := fun i =>
    AlgebraicGeometry.OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial ϖ N htriv 𝔚 i
  have hdd : ∀ i, (OModulePresheaf.ofModules ϖ N).d 𝔚 (i + 1) ∘ₗ (OModulePresheaf.ofModules ϖ N).d 𝔚 i = 0 := fun i =>
    AlgebraicGeometry.OModulePresheaf.d_comp_d (OModulePresheaf.ofModules ϖ N) 𝔚 i
  have hbdd : ∀ i, Fintype.card 𝔚.ι ≤ i → Subsingleton ((OModulePresheaf.ofModules ϖ N).cochain 𝔚 i) :=
    fun i hi => subsingleton_cochain ϖ (OModulePresheaf.ofModules ϖ N) 𝔚 i hi

  have hfibT : ∀ (𝔪 : Ideal B) (_ : 𝔪.IsMaximal),
      LinearMap.ker (((OModulePresheaf.ofModules ϖ N).d 𝔚 0).lTensor (B ⧸ 𝔪)) = ⊥ ∧
        ∀ i, LinearMap.ker (((OModulePresheaf.ofModules ϖ N).d 𝔚 (i + 1)).lTensor (B ⧸ 𝔪))
          ≤ LinearMap.range (((OModulePresheaf.ofModules ϖ N).d 𝔚 i).lTensor (B ⧸ 𝔪)) := by
    intro 𝔪 h𝔪
    obtain ⟨hH0, hHS⟩ := hfib 𝔪 h𝔪
    obtain ⟨E, hEd, -⟩ :=
      AlgebraicGeometry.OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial ϖ 𝔚 N htriv (B ⧸ 𝔪)
    have hE : ∀ (i : ℕ) (x : (B ⧸ 𝔪) ⊗[B] (OModulePresheaf.ofModules ϖ N).cochain 𝔚 i),
        E (i + 1) ((((OModulePresheaf.ofModules ϖ N).d 𝔚 i).lTensor (B ⧸ 𝔪)) x)
          = (OModulePresheaf.ofModules
              (Limits.pullback.snd ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))).obj N)).d
              (𝔚.baseChange ϖ (B ⧸ 𝔪)) i (E i x) := by
      intro i x
      have h := LinearMap.congr_fun (hEd i) x
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe] at h
      have hbc : ((OModulePresheaf.ofModules ϖ N).d 𝔚 i).baseChange (B ⧸ 𝔪) x
          = (((OModulePresheaf.ofModules ϖ N).d 𝔚 i).lTensor (B ⧸ 𝔪)) x :=
        congrFun (LinearMap.baseChange_eq_ltensor (A := B ⧸ 𝔪) ((OModulePresheaf.ofModules ϖ N).d 𝔚 i)) x
      rw [hbc] at h
      exact h
    refine ⟨?_, fun i => ?_⟩
    · rw [LinearMap.ker_eq_bot']
      intro x hx
      have h1 : E 1 ((((OModulePresheaf.ofModules ϖ N).d 𝔚 0).lTensor (B ⧸ 𝔪)) x) = 0 := by
        rw [hx, map_zero]
      rw [hE 0 x, ← LinearMap.mem_ker] at h1
      have h3 : E 0 x = 0 := (Submodule.mem_bot _).1 (hH0.le h1)
      exact (E 0).injective (h3.trans (E 0).map_zero.symm)
    · intro y hy
      have h1 : E (i + 1) y ∈ LinearMap.ker ((OModulePresheaf.ofModules
              (Limits.pullback.snd ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst ϖ (Scheme.TwoAffineOpenCover.specMap B (B ⧸ 𝔪)))).obj N)).d
              (𝔚.baseChange ϖ (B ⧸ 𝔪)) (i + 1)) := by
        rw [LinearMap.mem_ker, ← hE (i + 1) y]
        rw [LinearMap.mem_ker] at hy
        rw [hy, map_zero]
      have h2 := Submodule.Quotient.subsingleton_iff.1 (hHS i)
      have h3 := (Submodule.eq_top_iff'.1 h2) ⟨E (i + 1) y, h1⟩
      obtain ⟨z, hz⟩ := h3
      obtain ⟨w, rfl⟩ := (E i).surjective z
      refine ⟨w, (E (i + 1)).injective ?_⟩
      rw [hE i w, hz]
      rfl
  exact RelAcyclicEngine.acyclic (fun i => (OModulePresheaf.ofModules ϖ N).cochain 𝔚 i) (fun i => (OModulePresheaf.ofModules ϖ N).d 𝔚 i) hdd hflatC
    (Fintype.card 𝔚.ι) hbdd hfin.1 hfin.2 (fun 𝔪 h𝔪 => (hfibT 𝔪 h𝔪).1) (fun 𝔪 h𝔪 => (hfibT 𝔪 h𝔪).2)

end S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_of_forall_isMaximal_baseChange_quotient (solution)
