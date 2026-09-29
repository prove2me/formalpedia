-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.eulerChar_eq_add_of_affSES
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3e1f302c-647f-5bcf-a40e-f9ad75e32ef6

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace P2mEulerAdd

open AlgebraicGeometry.OModulePresheaf

variable {k : Type u} [Field k] {V : Scheme.{u}} {π : V ⟶ Spec (.of k)}

noncomputable def cx (F : OModulePresheaf π) (K : V.OrderedAffineCover) : CochainComplex (ModuleCat.{u} k) ℕ :=
  CochainComplex.of (fun i => ModuleCat.of k (F.cochain K i)) (fun i => ModuleCat.ofHom (F.d K i))
    (fun i => ModuleCat.hom_ext (by
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_zero]
      exact F.d_comp_d K i))

theorem cx_d_hom (F : OModulePresheaf π) (K : V.OrderedAffineCover) (i : ℕ) :
    ((cx F K).d i (i + 1)).hom = F.d K i := by
  simp [cx]

theorem cx_d_zero_zero_hom (F : OModulePresheaf π) (K : V.OrderedAffineCover) :
    ((cx F K).d 0 0).hom = 0 := by
  have : (cx F K).d 0 0 = 0 := (cx F K).shape 0 0 (by simp)
  rw [this]
  rfl

variable [IsSeparated π]

noncomputable def cxMap {F G : OModulePresheaf π} (φ : AffHom F G) (K : V.OrderedAffineCover) :
    cx F K ⟶ cx G K :=
  CochainComplex.ofHom (fun i => ModuleCat.ofHom (φ.cochainMap K i)) (fun i => ModuleCat.hom_ext (by
    simp only [ModuleCat.hom_comp, cx_d_hom]
    exact (φ.cochainMap_comp_d K i).symm))

theorem cxMap_f_hom {F G : OModulePresheaf π} (φ : AffHom F G) (K : V.OrderedAffineCover) (i : ℕ) :
    ((cxMap φ K).f i).hom = φ.cochainMap K i := rfl

variable {F₁ F₂ F₃ : OModulePresheaf π} (S : AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)

omit [IsSeparated π] in
theorem proj_inc_apply (U : V.affineOpens) (x : F₁.obj U.1) : S.proj.app U (S.inc.app U x) = 0 :=
  LinearMap.mem_ker.mp ((S.exact U) ▸ LinearMap.mem_range_self (S.inc.app U) x)

theorem cochainMap_injective (i : ℕ) : Function.Injective (S.inc.cochainMap K i) :=
  fun _ _ h => funext fun s => S.injective (K.affineInter π s) (congrFun h s)

theorem cochainMap_surjective (i : ℕ) : Function.Surjective (S.proj.cochainMap K i) := fun y =>
  ⟨fun s => (S.surjective (K.affineInter π s) (y s)).choose,
    funext fun s => (S.surjective (K.affineInter π s) (y s)).choose_spec⟩

theorem cochainMap_exact (i : ℕ) : Function.Exact (S.inc.cochainMap K i) (S.proj.cochainMap K i) := by
  intro y
  constructor
  · intro hy
    have hs : ∀ s : K.Idx i, y s ∈ LinearMap.range (S.inc.app (K.affineInter π s)) := fun s => by
      rw [S.exact]
      exact LinearMap.mem_ker.mpr (congrFun hy s)
    exact ⟨fun s => (hs s).choose, funext fun s => (hs s).choose_spec⟩
  · rintro ⟨x, rfl⟩
    exact funext fun s => proj_inc_apply S (K.affineInter π s) (x s)

noncomputable def T : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (cxMap S.inc K) (cxMap S.proj K) (by
    ext i : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun s => ?_)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f, ModuleCat.hom_comp, ModuleCat.hom_zero,
      cxMap_f_hom, LinearMap.comp_apply, LinearMap.zero_apply]
    exact proj_inc_apply S (K.affineInter π s) (x s))

theorem T_shortExact : (T S K).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro i
  exact ModuleCat.shortComplex_shortExact _ (cochainMap_exact S K i) (cochainMap_injective S K i)
    (cochainMap_surjective S K i)

section Ident

omit [IsSeparated π]

theorem quotEquiv_aux {M N P : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [AddCommGroup P] [Module k P] (f f' : M →ₗ[k] N) (g g' : N →ₗ[k] P) (hf : f' = f) (hg : g' = g)
    (h' : ∀ x, g' (f' x) = 0) :
    Nonempty ((LinearMap.ker g' ⧸ LinearMap.range (f'.codRestrict (LinearMap.ker g') h')) ≃ₗ[k]
      (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype)) := by
  subst hf hg
  exact ⟨Submodule.quotEquivOfEq _ _ (LinearMap.range_codRestrict _ _ _)⟩

theorem quotEquiv_aux₀ {M N P : Type u} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
    [AddCommGroup P] [Module k P] (f' : M →ₗ[k] N) (g g' : N →ₗ[k] P) (hf : f' = 0) (hg : g' = g)
    (h' : ∀ x, g' (f' x) = 0) :
    Nonempty ((LinearMap.ker g' ⧸ LinearMap.range (f'.codRestrict (LinearMap.ker g') h')) ≃ₗ[k]
      LinearMap.ker g) := by
  subst hf hg
  refine ⟨Submodule.quotEquivOfEqBot _ ?_⟩
  rw [LinearMap.range_eq_bot]
  ext x
  rfl

variable (F : OModulePresheaf π)

theorem nonempty_equiv_HSucc (i : ℕ) : Nonempty (((cx F K).homology (i + 1)) ≃ₗ[k] F.HSucc K i) := by
  let e₁ := ((cx F K).homologyIsoSc' i (i + 1) (i + 2) (CochainComplex.prev_nat_succ i)
    (CochainComplex.next ℕ (i + 1))).toLinearEquiv
  let e₂ := ((cx F K).sc' i (i + 1) (i + 2)).moduleCatHomologyIso.toLinearEquiv
  obtain ⟨e₃⟩ := quotEquiv_aux (F.d K i) ((cx F K).d i (i + 1)).hom (F.d K (i + 1))
    ((cx F K).d (i + 1) (i + 2)).hom (cx_d_hom F K i) (cx_d_hom F K (i + 1))
    ((cx F K).sc' i (i + 1) (i + 2)).moduleCat_zero_apply
  exact ⟨e₁ ≪≫ₗ e₂ ≪≫ₗ e₃⟩

theorem nonempty_equiv_H0 : Nonempty (((cx F K).homology 0) ≃ₗ[k] F.H0 K) := by
  let e₁ := ((cx F K).homologyIsoSc' 0 0 1 CochainComplex.prev_nat_zero
    (CochainComplex.next ℕ 0)).toLinearEquiv
  let e₂ := ((cx F K).sc' 0 0 1).moduleCatHomologyIso.toLinearEquiv
  obtain ⟨e₃⟩ := quotEquiv_aux₀ ((cx F K).d 0 0).hom (F.d K 0)
    ((cx F K).d 0 1).hom (cx_d_zero_zero_hom F K) (cx_d_hom F K 0)
    ((cx F K).sc' 0 0 1).moduleCat_zero_apply
  exact ⟨e₁ ≪≫ₗ e₂ ≪≫ₗ e₃⟩

theorem finrank_homology_eq (i : ℕ) : Module.finrank k ((cx F K).homology i) = F.cechFinrank K i := by
  cases i with
  | zero => obtain ⟨e⟩ := nonempty_equiv_H0 K F; exact e.finrank_eq
  | succ i => obtain ⟨e⟩ := nonempty_equiv_HSucc K F i; exact e.finrank_eq

theorem finite_homology (h : F.CechFinite K) (i : ℕ) : Module.Finite k ((cx F K).homology i) := by
  cases i with
  | zero => obtain ⟨e⟩ := nonempty_equiv_H0 K F; haveI := h.1; exact Module.Finite.equiv e.symm
  | succ i => obtain ⟨e⟩ := nonempty_equiv_HSucc K F i; haveI := h.2 i; exact Module.Finite.equiv e.symm

theorem subsingleton_homology_card_succ :
    Subsingleton ((cx F K).homology (Fintype.card K.ι + 1)) := by
  obtain ⟨e⟩ := nonempty_equiv_HSucc K F (Fintype.card K.ι)
  haveI := (F.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le K).2.2.1 (Fintype.card K.ι)
    (Nat.le_succ _)
  exact e.toEquiv.subsingleton

end Ident

theorem injective_homologyMap_zero : Function.Injective (HomologicalComplex.homologyMap (T S K).f 0) := by
  haveI : Mono ((T S K).f.f 0) := (ModuleCat.mono_iff_injective _).mpr (cochainMap_injective S K 0)
  haveI := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel (T S K).f 0
    (fun i (h : i + 1 = 0) => by omega)
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

include S in
theorem main (h₁ : F₁.CechFinite K) (h₂ : F₂.CechFinite K) (h₃ : F₃.CechFinite K) :
    F₂.eulerChar K = F₁.eulerChar K + F₃.eulerChar K := by
  have hT := T_shortExact S K
  set N := Fintype.card K.ι + 1 with hN

  let A : ℕ → Type u := fun i => (cx F₁ K).homology i
  let B : ℕ → Type u := fun i => (cx F₂ K).homology i
  let C : ℕ → Type u := fun i => (cx F₃ K).homology i
  haveI hA : ∀ i, Module.Finite k (A i) := finite_homology K F₁ h₁
  haveI hB : ∀ i, Module.Finite k (B i) := finite_homology K F₂ h₂
  haveI hC : ∀ i, Module.Finite k (C i) := finite_homology K F₃ h₃
  let f : ∀ i, A i →ₗ[k] B i := fun i => (HomologicalComplex.homologyMap (T S K).f i).hom
  let g : ∀ i, B i →ₗ[k] C i := fun i => (HomologicalComplex.homologyMap (T S K).g i).hom
  let δ : ∀ i, C i →ₗ[k] A (i + 1) := fun i => (hT.δ i (i + 1) rfl).hom
  have hfg : ∀ i, Function.Exact (f i) (g i) := fun i =>
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hT.homology_exact₂ i)
  have hgδ : ∀ i, Function.Exact (g i) (δ i) := fun i =>
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hT.homology_exact₃ i (i + 1) rfl)
  have hδf : ∀ i, Function.Exact (δ i) (f (i + 1)) := fun i =>
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hT.homology_exact₁ i (i + 1) rfl)
  have hf0 : Function.Injective (f 0) := injective_homologyMap_zero S K
  haveI hAN : Subsingleton (A N) := subsingleton_homology_card_succ K F₁
  have key := LinearMap.sum_neg_one_pow_mul_finrank_eq_zero_of_exact A B C f g δ hf0 hfg hgδ hδf N hAN

  have key' : ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i *
      ((F₁.cechFinrank K i : ℤ) - F₂.cechFinrank K i + F₃.cechFinrank K i) = 0 := by
    rw [← key]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← finrank_homology_eq K F₁ i, ← finrank_homology_eq K F₂ i, ← finrank_homology_eq K F₃ i]
  have hle : Fintype.card K.ι ≤ N := Nat.le_succ _
  rw [((F₁.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le K).2.2.2 inferInstance).2 N hle,
    ((F₂.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le K).2.2.2 inferInstance).2 N hle,
    ((F₃.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le K).2.2.2 inferInstance).2 N hle]
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at key'
  linarith

end P2mEulerAdd

theorem solution
    {k : Type u} [Field k] {V : Scheme.{u}} {π : V ⟶ Spec (.of k)} [IsSeparated π]
    {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₁ : F₁.CechFinite K) (h₂ : F₂.CechFinite K) (h₃ : F₃.CechFinite K) :
    F₂.eulerChar K = F₁.eulerChar K + F₃.eulerChar K :=
  P2mEulerAdd.main S K h₁ h₂ h₃

end S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES (solution)
