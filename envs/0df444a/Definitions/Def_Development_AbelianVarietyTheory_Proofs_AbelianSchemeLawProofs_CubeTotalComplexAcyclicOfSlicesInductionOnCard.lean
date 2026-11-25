-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T04:32:12.911091+00:00
-- url     : https://prove2.me/theorems/df1eaa5a-d0cf-47ed-a246-ffeb8b3158fa
-- title:
--   Cube Total Complex Acyclic Of Slices Induction On Card
-- statement:
--   Definitions and structural lemmas for Cube Total Complex Acyclic Of Slices Induction On Card, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_cubeComplex_acyclic_of_bijective
import Theorems.Thm_GlobalTheory_cubeComplex_acyclic_of_faces
import Theorems.Thm_GlobalTheory_cubeFunctor_shortExact
import Theorems.Thm_GlobalTheory_isIso_cechComplexMap
import Theorems.Thm_GlobalTheory_isIso_cubeLowerProj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
namespace GlobalTheory
namespace Cube
section Comap
variable {ι κ : Type} {R : Type u} [Ring R]
def comap (g : Finset κ → Finset ι) (hg : Monotone g) (A : Cube.{v} ι R) : Cube.{v} κ R :=
  mk (fun s => A.obj (g s)) (fun h => res A (hg h))
    (fun _ _ => res_self A _ _) (fun _ _ _ => res_res A _ _ _)
theorem comap_congr {g g' : Finset κ → Finset ι} (hg : Monotone g) (hg' : Monotone g')
    (h : ∀ s, g s = g' s) (A : Cube.{v} ι R) : comap g hg A = comap g' hg' A := by
  obtain rfl : g = g' := funext h
  rfl
def comapMap (g : Finset κ → Finset ι) (hg : Monotone g) {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    comap g hg A ⟶ comap g hg B :=
  homMk (fun s => (φ.app (g s)).hom) fun _ _ => app_res φ _ _
variable [LinearOrder ι] [LinearOrder κ]
theorem monotone_union_map (f : κ ↪o ι) (s : Finset ι) :
    Monotone fun t : Finset κ => s ∪ t.map f.toEmbedding :=
  fun _ _ h => Finset.union_subset_union_right (Finset.map_subset_map.2 h)
def slice (f : κ ↪o ι) (s : Finset ι) (A : Cube.{v} ι R) : Cube.{v} κ R :=
  comap (fun t => s ∪ t.map f.toEmbedding) (monotone_union_map f s) A
theorem slice_empty (f : κ ↪o ι) (A : Cube.{v} ι R) : slice f ∅ A = lowerFace f A :=
  comap_congr _ (fun _ _ h => Finset.map_subset_map.2 h) (fun _ => Finset.empty_union _) A
noncomputable def part (e : κ ↪o ι) (u : Finset ι) : Finset κ := u.preimage e e.injective.injOn
@[simp]
theorem mem_part (e : κ ↪o ι) (u : Finset ι) (k : κ) : k ∈ part e u ↔ e k ∈ u :=
  Finset.mem_preimage
theorem monotone_part (e : κ ↪o ι) : Monotone (part e) :=
  fun _ _ h _ hk => (mem_part e _ _).2 (h ((mem_part e _ _).1 hk))
end Comap
section Supp
variable {ι : Type} {R : Type u} [Ring R]
open Classical in

noncomputable def supp (A : Cube.{v} ι R) (P : Set (Finset ι)) (hP : P.OrdConnected) :
    Cube.{v} ι R :=
  mk (fun s => ModuleCat.of R (PLift (s ∈ P) → A.obj s))
    (fun {s _} h => LinearMap.pi fun _ =>
      if hs : s ∈ P then res A h ∘ₗ LinearMap.proj (PLift.up hs) else 0)
    (fun s x => funext fun ⟨hs⟩ => by simp [hs])
    (fun {s t w} h h' x => funext fun ⟨hw⟩ => by
      by_cases hs : s ∈ P
      · have ht : t ∈ P := hP.out hs hw ⟨h, h'⟩
        simp [hs, ht]
      · by_cases ht : t ∈ P <;> simp [hs, ht])
variable {A B : Cube.{v} ι R} {P P' : Set (Finset ι)} {hP : P.OrdConnected}
  {hP' : P'.OrdConnected}
noncomputable def suppEquiv (A : Cube.{v} ι R) (hP : P.OrdConnected) {s : Finset ι}
    (hs : s ∈ P) : (supp A P hP).obj s ≃ₗ[R] A.obj s where
  toFun x := (x : PLift (s ∈ P) → A.obj s) ⟨hs⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a := (fun _ => a : PLift (s ∈ P) → A.obj s)
  left_inv _ := rfl
  right_inv _ := rfl
theorem subsingleton_supp (A : Cube.{v} ι R) (hP : P.OrdConnected) {s : Finset ι}
    (hs : s ∉ P) : Subsingleton ((supp A P hP).obj s) :=
  ⟨fun _ _ => funext fun h => absurd h.down hs⟩
theorem suppEquiv_res {s t : Finset ι} (h : s ⊆ t) (hs : s ∈ P) (ht : t ∈ P)
    (x : (supp A P hP).obj s) :
    suppEquiv A hP ht (res (supp A P hP) h x) = res A h (suppEquiv A hP hs x) :=
  congrArg (fun g : (supp A P hP).obj s →ₗ[R] A.obj t => g x) (dif_pos hs)
theorem supp_ext {s : Finset ι} {x y : (supp A P hP).obj s}
    (h : ∀ hs : s ∈ P, suppEquiv A hP hs x = suppEquiv A hP hs y) : x = y :=
  funext fun hs => h hs.down
theorem supp_congr (A : Cube.{v} ι R) (h : ∀ s, s ∈ P ↔ s ∈ P') :
    supp A P hP = supp A P' hP' := by
  obtain rfl : P = P' := Set.ext h
  rfl
theorem comap_supp {κ : Type} (g : Finset κ → Finset ι) (hg : Monotone g) (A : Cube.{v} ι R) :
    comap g hg (supp A P hP) = supp (comap g hg A) (g ⁻¹' P) (hP.preimage_mono hg) := rfl
open Classical in

noncomputable def suppMapApp (φ : A ⟶ B) (hP : P.OrdConnected) (hP' : P'.OrdConnected)
    (s : Finset ι) : (supp A P hP).obj s →ₗ[R] (supp B P' hP').obj s :=
  LinearMap.pi (φ := fun _ : PLift (s ∈ P') => B.obj s) fun _ =>
    if hs : s ∈ P then (φ.app s).hom ∘ₗ (suppEquiv A hP hs).toLinearMap else 0
theorem suppEquiv_suppMapApp (φ : A ⟶ B) {s : Finset ι} (hs : s ∈ P) (hs' : s ∈ P')
    (x : (supp A P hP).obj s) :
    suppEquiv B hP' hs' (suppMapApp φ hP hP' s x) = (φ.app s).hom (suppEquiv A hP hs x) :=
  congrArg (fun g : (supp A P hP).obj s →ₗ[R] B.obj s => g x) (dif_pos hs)
noncomputable def suppMap (φ : A ⟶ B) (hP : P.OrdConnected) (hP' : P'.OrdConnected)
    (h : ∀ ⦃s t : Finset ι⦄, s ⊆ t → s ∈ P → t ∈ P' → (t ∈ P ↔ s ∈ P')) :
    supp A P hP ⟶ supp B P' hP' :=
  homMk (suppMapApp φ hP hP') fun {s t} hst x => by
    by_cases hs : s ∈ P
    · refine supp_ext fun ht' => ?_
      by_cases ht : t ∈ P
      · have hs' := (h hst hs ht').1 ht
        rw [suppEquiv_suppMapApp φ ht, suppEquiv_res hst hs, suppEquiv_res hst hs',
          suppEquiv_suppMapApp φ hs, app_res]
      · have hs' := mt (h hst hs ht').2 ht
        have := subsingleton_supp A hP ht
        have := subsingleton_supp B hP' hs'
        rw [Subsingleton.elim (res _ hst x) 0, Subsingleton.elim (suppMapApp φ hP hP' s x) 0]
        simp only [map_zero]
    · have := subsingleton_supp A hP hs
      rw [Subsingleton.elim x 0]
      simp only [map_zero]
theorem suppMapApp_bijective (φ : A ⟶ B) {s : Finset ι} (h : s ∈ P ↔ s ∈ P')
    (hφ : s ∈ P → Function.Bijective (φ.app s).hom) :
    Function.Bijective (suppMapApp φ hP hP' s) := by
  by_cases hs : s ∈ P
  · rw [← Function.Bijective.of_comp_iff' (suppEquiv B hP' (h.1 hs)).bijective]
    have : suppEquiv B hP' (h.1 hs) ∘ suppMapApp φ hP hP' s =
        (φ.app s).hom ∘ suppEquiv A hP hs := funext (suppEquiv_suppMapApp φ hs _)
    rw [this]
    exact (hφ hs).comp (suppEquiv A hP hs).bijective
  · have := subsingleton_supp A hP hs
    have := subsingleton_supp B hP' (mt h.2 hs)
    exact ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
theorem isIso_of_bijective (φ : A ⟶ B) (h : ∀ s, Function.Bijective (φ.app s).hom) : IsIso φ :=
  haveI : ∀ s, IsIso (φ.app s) := fun s => (ConcreteCategory.isIso_iff_bijective _).2 (h s)
  NatIso.isIso_of_isIso_app φ
noncomputable def suppIso (φ : A ⟶ B) (hP : P.OrdConnected)
    (hφ : ∀ s ∈ P, Function.Bijective (φ.app s).hom) : supp A P hP ≅ supp B P hP :=
  @asIso _ _ _ _ (suppMap φ hP hP fun _ _ _ hs ht => iff_of_true ht hs)
    (isIso_of_bijective _ fun s => suppMapApp_bijective φ Iff.rfl (hφ s))
noncomputable def suppIsoSelf (A : Cube.{v} ι R) (hP : P.OrdConnected) (h : ∀ s, s ∈ P) :
    supp A P hP ≅ A :=
  isoMk (fun s => suppEquiv A hP (h s)) fun hst x => suppEquiv_res hst _ _ x
noncomputable def suppSuppIso (A : Cube.{v} ι R) (hP : P.OrdConnected) (hP' : P'.OrdConnected) :
    supp (supp A P hP) P' hP' ≅ supp A (P ∩ P') (hP.inter hP') := by
  classical
  refine isoMk (fun s => if hs : s ∈ P ∩ P' then
      suppEquiv _ hP' hs.2 ≪≫ₗ suppEquiv _ hP hs.1 ≪≫ₗ (suppEquiv A (hP.inter hP') hs).symm
    else
      haveI := subsingleton_supp A (hP.inter hP') hs
      haveI : Subsingleton ((supp (supp A P hP) P' hP').obj s) :=
        ⟨fun _ _ => supp_ext fun hs' => supp_ext fun hs'' => absurd ⟨hs'', hs'⟩ hs⟩
      LinearEquiv.ofSubsingleton _ _) fun {s t} hst x => ?_
  by_cases hs : s ∈ P ∩ P'
  · refine supp_ext fun ht => ?_
    rw [suppEquiv_res hst hs]
    simp only [dif_pos hs, dif_pos ht, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [suppEquiv_res hst hs.2, suppEquiv_res hst hs.1]
  · have : x = 0 := supp_ext fun hs' => supp_ext fun hs'' => absurd ⟨hs'', hs'⟩ hs
    rw [this]
    simp only [map_zero]
open Classical in

noncomputable def suppIncl (A : Cube.{v} ι R) (hP : P.OrdConnected) (hU : IsUpperSet P) :
    supp A P hP ⟶ A :=
  homMk (fun s => if hs : s ∈ P then (suppEquiv A hP hs).toLinearMap else 0) fun {s t} hst x => by
    by_cases hs : s ∈ P
    · have ht : t ∈ P := hU hst hs
      simp only [dif_pos hs, dif_pos ht, LinearEquiv.coe_coe]
      exact suppEquiv_res hst hs ht x
    · have := subsingleton_supp A hP hs
      rw [Subsingleton.elim x 0]
      simp only [map_zero]
theorem suppIncl_app (A : Cube.{v} ι R) (hP : P.OrdConnected) (hU : IsUpperSet P) {s : Finset ι}
    (hs : s ∈ P) : ((suppIncl A hP hU).app s).hom = (suppEquiv A hP hs).toLinearMap :=
  dif_pos hs
variable {P₁ P₂ : Set (Finset ι)}
noncomputable def suppSequence (A : Cube.{v} ι R) (hP₁ : P₁.OrdConnected) (hP : P.OrdConnected)
    (hP₂ : P₂.OrdConnected) (h : ∀ s, s ∈ P ↔ s ∈ P₁ ∨ s ∈ P₂) (hd : ∀ s ∈ P₁, s ∉ P₂)
    (hu : ∀ ⦃s t : Finset ι⦄, s ⊆ t → s ∈ P₁ → t ∈ P → t ∈ P₁) : ShortComplex (Cube.{v} ι R) :=
  ShortComplex.mk
    (suppMap (𝟙 A) hP₁ hP fun s _ hst hs ht => iff_of_true (hu hst hs ht) ((h s).2 (Or.inl hs)))
    (suppMap (𝟙 A) hP hP₂ fun s t hst hs ht => iff_of_true ((h t).2 (Or.inr ht))
      (((h s).1 hs).resolve_left fun hs₁ => hd t (hu hst hs₁ ((h t).2 (Or.inr ht))) ht))
    (by
      ext s x
      by_cases hs : s ∈ P₁
      · exact (subsingleton_supp A hP₂ (hd s hs)).elim _ _
      · rw [(subsingleton_supp A hP₁ hs).elim x 0]
        simp only [map_zero])
theorem suppSequence_shortExact (A : Cube.{v} ι R) (hP₁ : P₁.OrdConnected) (hP : P.OrdConnected)
    (hP₂ : P₂.OrdConnected) (h : ∀ s, s ∈ P ↔ s ∈ P₁ ∨ s ∈ P₂) (hd : ∀ s ∈ P₁, s ∉ P₂)
    (hu : ∀ ⦃s t : Finset ι⦄, s ⊆ t → s ∈ P₁ → t ∈ P → t ∈ P₁) (s : Finset ι) :
    ((suppSequence A hP₁ hP hP₂ h hd hu).map ((evaluation _ _).obj s)).ShortExact := by
  have key : Function.Exact (suppMapApp (𝟙 A) hP₁ hP s) (suppMapApp (𝟙 A) hP hP₂ s) ∧
      Function.Injective (suppMapApp (𝟙 A) hP₁ hP s) ∧
      Function.Surjective (suppMapApp (𝟙 A) hP hP₂ s) := by
    by_cases hs : s ∈ P₁
    · have := subsingleton_supp A hP₂ (hd s hs)
      have hb : Function.Bijective (suppMapApp (𝟙 A) hP₁ hP s) :=
        suppMapApp_bijective _ (iff_of_true hs ((h s).2 (Or.inl hs))) fun _ =>
          Function.bijective_id
      exact ⟨fun y => iff_of_true (Subsingleton.elim _ _) (hb.2 y), hb.1,
        Function.surjective_to_subsingleton _⟩
    · have := subsingleton_supp A hP₁ hs
      have hb : Function.Bijective (suppMapApp (𝟙 A) hP hP₂ s) :=
        suppMapApp_bijective _ (by simp [h s, hs]) fun _ => Function.bijective_id
      refine ⟨fun y => ?_, Function.injective_of_subsingleton _, hb.2⟩
      rw [map_eq_zero_iff _ hb.1]
      exact ⟨fun hy => ⟨0, by rw [map_zero, hy]⟩, by
        rintro ⟨x, rfl⟩; rw [Subsingleton.elim x 0, map_zero]⟩
  exact ModuleCat.shortComplex_shortExact _ key.1 key.2.1 key.2.2
end Supp
end Cube
section Zero
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
noncomputable def cubeHomologyMapIso {A B : Cube.{v} ι R} (φ : A ≅ B) (n : ℕ) :
    (cubeComplex A).homology n ≅ (cubeComplex B).homology n :=
  homologyMapIso ((cubeFunctor ι R).mapIso φ) n
noncomputable def cechHomologyMapIso {A B : Cube.{v} ι R} (φ : A ≅ B) (n : ℕ) :
    (cechComplex A).homology n ≅ (cechComplex B).homology n :=
  homologyMapIso ((cechFunctor ι R).mapIso φ) n
theorem cubeComplex_acyclic_of_iso {A B : Cube.{v} ι R} (φ : A ≅ B)
    (h : (cubeComplex A).Acyclic) : (cubeComplex B).Acyclic :=
  fun n => (h n).of_iso ((cubeFunctor ι R).mapIso φ)
theorem isZero_cubeComplex_X_of_subsingleton (A : Cube.{v} ι R) (p : ℕ)
    (h : ∀ s : Finset ι, s.card = p → Subsingleton (A.obj s)) : IsZero ((cubeComplex A).X p) :=
  haveI : Subsingleton (Cube.Term A p) := ⟨fun _ _ => funext fun s => (h s.1 s.2).elim _ _⟩
  ModuleCat.isZero_of_subsingleton (ModuleCat.of R (Cube.Term A p))
theorem isZero_cubeComplex_of_subsingleton (A : Cube.{v} ι R)
    (h : ∀ s : Finset ι, Subsingleton (A.obj s)) : IsZero (cubeComplex A) := by
  rw [IsZero.iff_id_eq_zero]
  exact HomologicalComplex.hom_ext _ _ fun p =>
    (isZero_cubeComplex_X_of_subsingleton A p fun s _ => h s).eq_of_src _ _
theorem cubeComplex_acyclic_of_subsingleton (A : Cube.{v} ι R)
    (h : ∀ s : Finset ι, Subsingleton (A.obj s)) : (cubeComplex A).Acyclic :=
  fun p => ExactAt.of_isZero (isZero_cubeComplex_X_of_subsingleton A p fun s _ => h s)
theorem isIso_cubeLowerProj_of_subsingleton (e : κ ↪o ι) (A : Cube.{v} ι R)
    (h : ∀ u : Finset ι, (∃ j ∈ u, j ∉ Set.range e) → Subsingleton (A.obj u)) :
    IsIso (cubeLowerProj e A) := by
  have : ∀ p, IsIso ((cubeLowerProj e A).f p) := fun p => by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (Cube.termLower e A p)
    constructor
    · intro x y hxy
      funext ⟨t, ht⟩
      by_cases h' : ∃ j ∈ t, j ∉ Set.range e
      · exact (h t h').elim _ _
      · push_neg at h'
        obtain ⟨s, rfl⟩ : ∃ s : Finset κ, t = s.map e.toEmbedding := by
          refine ⟨Cube.part e t, Finset.ext fun j => ?_⟩
          simp only [Finset.mem_map, Cube.mem_part]
          refine ⟨fun hj => ?_, by rintro ⟨k, hk, rfl⟩; exact hk⟩
          obtain ⟨k, rfl⟩ := h' j hj
          exact ⟨k, hj, rfl⟩
        exact congrFun hxy ⟨s, (Finset.card_map _).symm.trans ht⟩
    · intro y
      have hsub : ∀ t : Finset ι, (Cube.part e t).map e.toEmbedding ⊆ t := fun t j hj => by
        obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hj
        exact (Cube.mem_part e t k).1 hk
      refine ⟨fun t => Cube.res A (hsub t.1)
        (Cube.extend (Cube.lowerFace e A) p y (Cube.part e t.1)), funext fun s => ?_⟩
      have key : ∀ (s' : Finset κ) (_ : s' = s.1) (h : s'.map e.toEmbedding ⊆
          s.1.map e.toEmbedding),
          Cube.res A h (Cube.extend (Cube.lowerFace e A) p y s') = y s := by
        rintro _ rfl h
        rw [Cube.extend_apply_of_eq _ y s.2]
        exact Cube.res_self A h _
      exact key _ (Cube.preimage_map_orderEmbedding s.1) _
  exact HomologicalComplex.Hom.isIso_of_components _
theorem isIso_cubeUpperIncl_of_subsingleton {e : κ ↪o ι} {i : ι} (he : Set.range e = {i}ᶜ)
    (A : Cube.{v} ι R) (h : ∀ u : Finset ι, i ∉ u → Subsingleton (A.obj u)) :
    IsIso (cubeUpperIncl he A) :=
  (cubeFaceSequence_shortExact he A).isIso_f_iff.2
    (isZero_cubeComplex_of_subsingleton _ fun s => h _ (Cube.notMem_map_of_range_eq he s))
noncomputable def cubeHomologySuccIsoCech (A : Cube.{v} ι R) (h : Subsingleton (A.obj ∅)) :
    ∀ n : ℕ, (cubeComplex A).homology (n + 1) ≅ (cechComplex A).homology n
  | 0 => ((cubeComplex A).isoHomologyπ 0 1 (by simp)
        ((isZero_cubeComplex_X_of_subsingleton A 0 fun s hs => by
          rwa [Finset.card_eq_zero.1 hs]).eq_of_src _ _)).symm ≪≫
      cubeCyclesIso A 1 ≪≫ (cechHomologyZeroIso A).symm
  | n + 1 => (cechHomologySuccIso A n).symm
theorem isIso_homologyMap_g_of_acyclic {S : ShortComplex (CochainComplex (ModuleCat.{v} R) ℕ)}
    (hS : S.ShortExact) (h : S.X₁.Acyclic) (n : ℕ) : IsIso (homologyMap S.g n) := by
  have h0 : ∀ n, IsZero (S.X₁.homology n) := fun n => (exactAt_iff_isZero_homology _ _).1 (h n)
  have : Mono (homologyMap S.g n) := (hS.homology_exact₂ n).mono_g ((h0 n).eq_of_src _ _)
  have : Epi (homologyMap S.g n) :=
    (hS.homology_exact₃ n (n + 1) rfl).epi_f ((h0 (n + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _
end Zero
section Slices
variable {κ : Type} [LinearOrder κ] {R : Type u} [Ring R]
theorem cubeTotalComplex_acyclic_of_slices_induction_on_card (n : ℕ) :
    ∀ (μ : Type) [LinearOrder μ] (f : κ ↪o μ) (I : Finset μ) (_ : ∀ j, j ∈ I ↔ j ∉ Set.range f)
      (_ : I.card = n) (A : Cube.{v} μ R)
      (_ : ∀ s ⊆ I, (cubeComplex (Cube.slice f s A)).Acyclic), (cubeComplex A).Acyclic := by
  induction n with
  | zero =>
    intro μ _ f I hI hn A hA
    obtain rfl := Finset.card_eq_zero.1 hn
    have hf : Function.Surjective f := fun j => by simpa using hI j
    have := isIso_cubeLowerProj hf A
    have h := hA ∅ (subset_refl _)
    rw [Cube.slice_empty] at h
    exact fun p => (h p).of_iso (asIso (cubeLowerProj f A)).symm
  | succ n ih =>
    intro μ _ f I hI hn A hA
    obtain ⟨i, hi⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
    have hfi : ∀ k, f k ≠ i := fun k hk => (hI i).1 hi ⟨k, hk⟩
    let f' : κ ↪o {j : μ // j ≠ i} :=
      OrderEmbedding.ofMapLEIff (fun k => ⟨f k, hfi k⟩) fun _ _ => f.le_iff_le
    have hI' : ∀ j, j ∈ I.subtype (· ≠ i) ↔ j ∉ Set.range f' := fun j => by
      rw [Finset.mem_subtype, hI]
      exact not_congr ⟨fun ⟨k, hk⟩ => ⟨k, Subtype.ext hk⟩,
        fun ⟨k, hk⟩ => ⟨k, congrArg Subtype.val hk⟩⟩
    have hn' : (I.subtype (· ≠ i)).card = n := by
      rw [Finset.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem hi, hn]; rfl
    have hm : ∀ (s : Finset {j : μ // j ≠ i}) (t : Finset κ),
        (s ∪ t.map f'.toEmbedding).map (otherDirections i).toEmbedding =
          s.map (otherDirections i).toEmbedding ∪ t.map f.toEmbedding := fun s t => by
      rw [Finset.map_union, Finset.map_map]; rfl
    have hs : ∀ s ⊆ I.subtype (· ≠ i), s.map (otherDirections i).toEmbedding ⊆ I := by
      intro s hs j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hj
      exact Finset.mem_subtype.1 (hs hk)
    refine cubeComplex_acyclic_of_faces (range_otherDirections i) A
      (ih _ f' _ hI' hn' _ fun s hsI => ?_) (ih _ f' _ hI' hn' _ fun s hsI => ?_)
    · have : Cube.slice f' s (Cube.lowerFace (otherDirections i) A) =
          Cube.slice f (s.map (otherDirections i).toEmbedding) A :=
        Cube.comap_congr (fun _ _ h => Finset.map_subset_map.2 (Cube.monotone_union_map f' s h))
          _ (hm s) A
      rw [this]
      exact hA _ (hs s hsI)
    · have : Cube.slice f' s (Cube.upperFace (otherDirections i) i A) =
          Cube.slice f (insert i (s.map (otherDirections i).toEmbedding)) A :=
        Cube.comap_congr (fun _ _ h => Finset.insert_subset_insert i
          (Finset.map_subset_map.2 (Cube.monotone_union_map f' s h)))
          _ (fun t => (congrArg (insert i) (hm s t)).trans (Finset.insert_union _ _ _).symm) A
      rw [this]
      exact hA _ (Finset.insert_subset hi (hs s hsI))
variable {ι μ : Type} [LinearOrder ι] [LinearOrder μ] {e : ι ↪o μ} {f : κ ↪o μ}
theorem cubeComplex_acyclic_of_slices [Finite ι] (h : IsCompl (Set.range e) (Set.range f))
    (A : Cube.{v} μ R)
    (hA : ∀ s : Finset ι, (cubeComplex (Cube.slice f (s.map e.toEmbedding) A)).Acyclic) :
    (cubeComplex A).Acyclic := by
  have := Fintype.ofFinite ι
  refine cubeTotalComplex_acyclic_of_slices_induction_on_card _ μ f (Finset.univ.map e.toEmbedding) (fun j => ?_)
    rfl A fun s hs => ?_
  · rw [← Set.mem_compl_iff, ← h.eq_compl]
    simp
  · obtain ⟨s', -, rfl⟩ := Finset.subset_map_iff.1 hs
    exact hA s'
end Slices
namespace Cube
section Parts
variable {ι κ μ : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder μ] {e : ι ↪o μ} {f : κ ↪o μ}
theorem part_union_left (h : Disjoint (Set.range e) (Set.range f)) (s : Finset ι) (t : Finset κ) :
    part e (s.map e.toEmbedding ∪ t.map f.toEmbedding) = s := by
  ext i
  have : ∀ k, f k ≠ e i := fun k hk => Set.disjoint_left.1 h ⟨i, rfl⟩ ⟨k, hk⟩
  simp [this]
theorem part_union_right (h : Disjoint (Set.range e) (Set.range f)) (s : Finset ι) (t : Finset κ) :
    part f (s.map e.toEmbedding ∪ t.map f.toEmbedding) = t := by
  rw [Finset.union_comm, part_union_left h.symm]
theorem map_part_union_map_part (h : Codisjoint (Set.range e) (Set.range f)) (u : Finset μ) :
    (part e u).map e.toEmbedding ∪ (part f u).map f.toEmbedding = u := by
  ext j
  simp only [Finset.mem_union, Finset.mem_map, mem_part]
  refine ⟨by rintro (⟨_, h, rfl⟩ | ⟨_, h, rfl⟩) <;> exact h, fun hj => ?_⟩
  have : j ∈ Set.range e ∪ Set.range f := by
    exact (codisjoint_iff.1 h).ge (Set.mem_univ j)
  rcases this with ⟨i, rfl⟩ | ⟨k, rfl⟩
  · exact Or.inl ⟨i, hj, rfl⟩
  · exact Or.inr ⟨k, hj, rfl⟩
omit [LinearOrder ι] in

theorem isUpperSet_nonempty : IsUpperSet {s : Finset ι | s.Nonempty} :=
  fun _ _ h hs => Finset.Nonempty.mono h hs
omit [LinearOrder ι] in

theorem ordConnected_nonempty : Set.OrdConnected {s : Finset ι | s.Nonempty} :=
  isUpperSet_nonempty.ordConnected
variable (e f) in

def partsIn (Q : Set (Finset ι)) (T : Set (Finset κ)) : Set (Finset μ) :=
  part e ⁻¹' Q ∩ part f ⁻¹' T
@[simp]
theorem mem_partsIn {Q : Set (Finset ι)} {T : Set (Finset κ)} {u : Finset μ} :
    u ∈ partsIn e f Q T ↔ part e u ∈ Q ∧ part f u ∈ T := Iff.rfl
variable (e f) in

theorem ordConnected_partsIn {Q : Set (Finset ι)} {T : Set (Finset κ)} (hQ : Q.OrdConnected)
    (hT : T.OrdConnected) : (partsIn e f Q T).OrdConnected :=
  (hQ.preimage_mono (monotone_part e)).inter (hT.preimage_mono (monotone_part f))
variable {R : Type u} [Ring R]
theorem supp_partsIn_comm {Q : Set (Finset ι)} {T : Set (Finset κ)} (hQ : Q.OrdConnected)
    (hT : T.OrdConnected) (A : Cube.{v} μ R) :
    supp A (partsIn e f Q T) (ordConnected_partsIn e f hQ hT) =
      supp A (partsIn f e T Q) (ordConnected_partsIn f e hT hQ) :=
  supp_congr A fun _ => and_comm
noncomputable def trunc₁ (A : Cube.{v} ι R) : Cube.{v} ι R :=
  supp A {s | s.Nonempty} ordConnected_nonempty
variable (e f) in

noncomputable def truncOver (Q : Set (Finset ι)) (hQ : Q.OrdConnected) (A : Cube.{v} μ R) :
    Cube.{v} μ R :=
  supp A (partsIn e f Q {t | t.Nonempty}) (ordConnected_partsIn e f hQ ordConnected_nonempty)
variable (e f) in

noncomputable def truncBoth (A : Cube.{v} μ R) : Cube.{v} μ R :=
  truncOver e f {s | s.Nonempty} ordConnected_nonempty A
theorem truncBoth_comm (A : Cube.{v} μ R) : truncBoth e f A = truncBoth f e A :=
  supp_partsIn_comm ordConnected_nonempty ordConnected_nonempty A
theorem slice_supp_partsIn_of_mem (h : Disjoint (Set.range e) (Set.range f))
    {Q : Set (Finset ι)} {T : Set (Finset κ)} (hQ : Q.OrdConnected) (hT : T.OrdConnected)
    (A : Cube.{v} μ R) {s : Finset ι} (hs : s ∈ Q) :
    slice f (s.map e.toEmbedding) (supp A (partsIn e f Q T) (ordConnected_partsIn e f hQ hT)) =
      supp (slice f (s.map e.toEmbedding) A) T hT :=
  (comap_supp _ _ A).trans (supp_congr _ fun t => by
    simp [part_union_left h, part_union_right h, hs])
theorem subsingleton_slice_supp_partsIn (h : Disjoint (Set.range e) (Set.range f))
    {Q : Set (Finset ι)} {T : Set (Finset κ)} (hQ : Q.OrdConnected) (hT : T.OrdConnected)
    (A : Cube.{v} μ R) {s : Finset ι} (hs : s ∉ Q) (t : Finset κ) :
    Subsingleton ((slice f (s.map e.toEmbedding)
      (supp A (partsIn e f Q T) (ordConnected_partsIn e f hQ hT))).obj t) :=
  subsingleton_supp A (ordConnected_partsIn e f hQ hT) (by simp [part_union_left h, hs])
end Parts
end Cube
section Trunc
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
noncomputable def cechTruncIso (A : Cube.{v} ι R) : cechComplex (Cube.trunc₁ A) ≅ cechComplex A :=
  @asIso _ _ _ _
    (cechComplexMap (Cube.suppIncl A Cube.ordConnected_nonempty Cube.isUpperSet_nonempty))
    (isIso_cechComplexMap _ fun s hs => by
      have h := Cube.suppIncl_app A Cube.ordConnected_nonempty Cube.isUpperSet_nonempty hs
      exact h ▸ (Cube.suppEquiv A Cube.ordConnected_nonempty hs).bijective)
noncomputable def truncHomologyIso (A : Cube.{v} ι R) (n : ℕ) :
    (cubeComplex (Cube.trunc₁ A)).homology (n + 1) ≅ (cechComplex A).homology n :=
  cubeHomologySuccIsoCech _ (Cube.subsingleton_supp A _ (by simp)) n ≪≫
    homologyMapIso (cechTruncIso A) n
theorem cubeComplex_trunc₁_exactAt_zero (A : Cube.{v} ι R) :
    (cubeComplex (Cube.trunc₁ A)).ExactAt 0 :=
  ExactAt.of_isZero (isZero_cubeComplex_X_of_subsingleton _ 0 fun s hs =>
    Cube.subsingleton_supp A _ (by simp [Finset.card_eq_zero.1 hs]))
theorem cubeComplex_trunc₁_acyclic_iff (A : Cube.{v} ι R) :
    (cubeComplex (Cube.trunc₁ A)).Acyclic ↔ (cechComplex A).Acyclic := by
  refine ⟨fun h n => ?_, fun h n => ?_⟩
  · exact (exactAt_iff_isZero_homology _ _).2
      (((exactAt_iff_isZero_homology _ _).1 (h (n + 1))).of_iso (truncHomologyIso A n).symm)
  · cases n with
    | zero => exact cubeComplex_trunc₁_exactAt_zero A
    | succ n =>
      exact (exactAt_iff_isZero_homology _ _).2
        (((exactAt_iff_isZero_homology _ _).1 (h n)).of_iso (truncHomologyIso A n))
end Trunc
section Compare
open Cube
variable {ι κ μ : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder μ] {e : ι ↪o μ} {f : κ ↪o μ}
  {R : Type u} [Ring R]
theorem cubeComplex_supp_partsIn_acyclic [Finite ι] (h : IsCompl (Set.range e) (Set.range f))
    {Q : Set (Finset ι)} {T : Set (Finset κ)} (hQ : Q.OrdConnected) (hT : T.OrdConnected)
    (A : Cube.{v} μ R)
    (hA : ∀ s ∈ Q, (cubeComplex (supp (slice f (s.map e.toEmbedding) A) T hT)).Acyclic) :
    (cubeComplex (supp A (partsIn e f Q T) (ordConnected_partsIn e f hQ hT))).Acyclic := by
  refine cubeComplex_acyclic_of_slices h _ fun s => ?_
  by_cases hs : s ∈ Q
  · rw [slice_supp_partsIn_of_mem h.disjoint hQ hT A hs]
    exact hA s hs
  · exact cubeComplex_acyclic_of_subsingleton _
      (subsingleton_slice_supp_partsIn h.disjoint hQ hT A hs)
theorem mem_range_of_notMem_range (h : IsCompl (Set.range e) (Set.range f)) {j : μ}
    (hj : j ∉ Set.range e) : j ∈ Set.range f := by
  rwa [← h.compl_eq]
noncomputable def suppEmptyHomologyIso (h : IsCompl (Set.range e) (Set.range f))
    {Q : Set (Finset ι)} (hQ : Q.OrdConnected) (A : Cube.{v} μ R) (n : ℕ) :
    (cubeComplex (supp A (partsIn e f Q {∅})
      (ordConnected_partsIn e f hQ Set.ordConnected_singleton))).homology n ≅
      (cubeComplex (supp (lowerFace e A) Q hQ)).homology n :=
  homologyMapIso (@asIso _ _ _ _ (cubeLowerProj e _) (isIso_cubeLowerProj_of_subsingleton e _ (by
    rintro u ⟨j, hj, hje⟩
    obtain ⟨k, rfl⟩ := mem_range_of_notMem_range h hje
    refine subsingleton_supp A _ fun hu => ?_
    have hk : k ∈ part f u := (mem_part f u k).2 hj
    rw [Set.mem_singleton_iff.1 hu.2] at hk
    simp at hk))) n ≪≫
  cubeHomologyMapIso (eqToIso (by
    have := slice_supp_partsIn_of_mem (e := f) (f := e) h.disjoint.symm
      (Set.ordConnected_singleton (a := ∅)) hQ A rfl
    rw [Finset.map_empty, slice_empty, slice_empty] at this
    exact (congrArg (lowerFace e) (supp_partsIn_comm hQ Set.ordConnected_singleton A)).trans this)) n
noncomputable def suppSingletonHomologyIso (h : IsCompl (Set.range e) (Set.range f))
    {Q : Set (Finset ι)} (hQ : Q.OrdConnected) (k : κ) (A : Cube.{v} μ R) (n : ℕ) :
    (cubeComplex (supp A (partsIn e f Q {{k}})
      (ordConnected_partsIn e f hQ Set.ordConnected_singleton))).homology (n + 1) ≅
      (cubeComplex (supp (slice e (({k} : Finset κ).map f.toEmbedding) A) Q hQ)).homology n :=
  let D := supp A (partsIn e f Q {{k}}) (ordConnected_partsIn e f hQ Set.ordConnected_singleton)
  have hne : ∀ i, e i ≠ f k := fun i hi => Set.disjoint_left.1 h.disjoint ⟨i, rfl⟩ ⟨k, hi.symm⟩
  let e' : ι ↪o {j : μ // j ≠ f k} :=
    OrderEmbedding.ofMapLEIff (fun i => ⟨e i, hne i⟩) fun _ _ => e.le_iff_le
  (homologyMapIso (@asIso _ _ _ _ (cubeUpperIncl (range_otherDirections (f k)) D)
    (isIso_cubeUpperIncl_of_subsingleton _ D fun u hu => subsingleton_supp A _ fun hu' => by
      have hk : k ∈ part f u := by rw [Set.mem_singleton_iff.1 hu'.2]; simp
      exact hu ((mem_part f u k).1 hk))) (n + 1)).symm ≪≫
  shiftSuccHomologyIso _ n ≪≫
  homologyMapIso (@asIso _ _ _ _ (cubeLowerProj e' _) (isIso_cubeLowerProj_of_subsingleton e' _ (by
    rintro u ⟨j, hj, hje⟩
    obtain ⟨k', hk'⟩ := mem_range_of_notMem_range h (j := j.1)
      fun ⟨i, hi⟩ => hje ⟨i, Subtype.ext hi⟩
    refine subsingleton_supp A (ordConnected_partsIn e f hQ (Set.ordConnected_singleton (a := {k})))
      fun hu => ?_
    have hk : k' ∈ part f (insert (f k) (u.map (otherDirections (f k)).toEmbedding)) :=
      (mem_part f _ k').2 (Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨j, hj, hk'.symm⟩))
    rw [Set.mem_singleton_iff.1 hu.2, Finset.mem_singleton] at hk
    exact j.2 (by rw [← hk', hk])))) n ≪≫
  cubeHomologyMapIso (eqToIso (by
    have := slice_supp_partsIn_of_mem (e := f) (f := e) h.disjoint.symm
      (Set.ordConnected_singleton (a := {k})) hQ A rfl
    refine Eq.trans ?_ ((congrArg (slice e _) (supp_partsIn_comm hQ Set.ordConnected_singleton A)).trans this)
    refine comap_congr (fun _ _ h => Finset.insert_subset_insert _
      (Finset.map_subset_map.2 (Finset.map_subset_map.2 h))) _ (fun s => ?_) D
    rw [Finset.map_map, Finset.map_singleton, Finset.singleton_union]
    rfl)) n
noncomputable def truncOverHomologyIsoEmpty [Finite ι] (h : IsCompl (Set.range e) (Set.range f))
    {Q : Set (Finset ι)} (hQ : Q.OrdConnected) (A : Cube.{v} μ R)
    (hA : ∀ s ∈ Q, (cubeComplex (slice f (s.map e.toEmbedding) A)).Acyclic) (n : ℕ) :
    (cubeComplex (truncOver e f Q hQ A)).homology (n + 1) ≅
      (cubeComplex (supp (lowerFace e A) Q hQ)).homology n :=
  have hS := cubeFunctor_shortExact _ (suppSequence_shortExact A
    (ordConnected_partsIn e f hQ ordConnected_nonempty)
    (ordConnected_partsIn e f hQ Set.ordConnected_univ)
    (ordConnected_partsIn e f hQ (Set.ordConnected_singleton (a := ∅)))
    (fun u => by
      simp only [mem_partsIn, Set.mem_univ, and_true, Set.mem_setOf_eq, Set.mem_singleton_iff]
      have := (part f u).eq_empty_or_nonempty
      tauto)
    (fun u hu hu' => hu.2.ne_empty hu'.2)
    (fun _ _ hst hs ht => ⟨ht.1, Finset.Nonempty.mono (monotone_part f hst) hs.2⟩))
  have h₂ := cubeComplex_supp_partsIn_acyclic h hQ Set.ordConnected_univ A fun s hs =>
    cubeComplex_acyclic_of_iso (suppIsoSelf _ _ fun _ => trivial).symm (hA s hs)
  (hS.δIso n (n + 1) rfl ((exactAt_iff_isZero_homology _ _).1 (h₂ n))
    ((exactAt_iff_isZero_homology _ _).1 (h₂ (n + 1)))).symm ≪≫
  suppEmptyHomologyIso h hQ A n
omit [LinearOrder κ] in

theorem Cube.isUpperSet_nonempty_ne_singleton (k : κ) :
    IsUpperSet {t : Finset κ | t.Nonempty ∧ t ≠ {k}} := by
  rintro s t hst ⟨hs, hs'⟩
  refine ⟨hs.mono hst, fun ht => ?_⟩
  rw [ht] at hst
  exact (Finset.subset_singleton_iff.1 hst).elim hs.ne_empty hs'
noncomputable def truncOverHomologyIsoSingleton [Finite κ]
    (h : IsCompl (Set.range e) (Set.range f))
    {Q : Set (Finset ι)} (hQ : Q.OrdConnected) (k : κ) (A : Cube.{v} μ R)
    (hA : ∀ t : Finset κ, t.Nonempty → t ≠ {k} →
      (cubeComplex (supp (slice e (t.map f.toEmbedding) A) Q hQ)).Acyclic) (n : ℕ) :
    (cubeComplex (truncOver e f Q hQ A)).homology (n + 1) ≅
      (cubeComplex (supp (slice e (({k} : Finset κ).map f.toEmbedding) A) Q hQ)).homology n :=
  have hT := (Cube.isUpperSet_nonempty_ne_singleton k).ordConnected
  have hS := cubeFunctor_shortExact _ (suppSequence_shortExact A
    (ordConnected_partsIn e f hQ hT)
    (ordConnected_partsIn e f hQ ordConnected_nonempty)
    (ordConnected_partsIn e f hQ (Set.ordConnected_singleton (a := ({k} : Finset κ))))
    (fun u => by
      simp only [mem_partsIn, Set.mem_setOf_eq, Set.mem_singleton_iff]
      by_cases hu : part f u = {k} <;> simp [hu])
    (fun u hu hu' => hu.2.2 hu'.2)
    (fun _ _ hst hs ht =>
      ⟨ht.1, Cube.isUpperSet_nonempty_ne_singleton k (monotone_part f hst) hs.2⟩))
  have h₁ : (cubeComplex (supp A _ (ordConnected_partsIn e f hQ hT))).Acyclic := by
    rw [supp_partsIn_comm hQ hT A]
    exact cubeComplex_supp_partsIn_acyclic h.symm hT hQ A fun t ht => hA t ht.1 ht.2
  @asIso _ _ _ _ _ (isIso_homologyMap_g_of_acyclic hS h₁ (n + 1)) ≪≫
    suppSingletonHomologyIso h hQ k A n
noncomputable def truncBothHomologyIsoEmpty [Finite ι] (h : IsCompl (Set.range e) (Set.range f))
    (A : Cube.{v} μ R)
    (hA : ∀ s : Finset ι, s.Nonempty → (cubeComplex (slice f (s.map e.toEmbedding) A)).Acyclic)
    (n : ℕ) :
    (cubeComplex (truncBoth e f A)).homology (n + 2) ≅ (cechComplex (lowerFace e A)).homology n :=
  truncOverHomologyIsoEmpty h ordConnected_nonempty A hA (n + 1) ≪≫ truncHomologyIso _ n
noncomputable def truncBothHomologyIsoSingleton [Finite κ]
    (h : IsCompl (Set.range e) (Set.range f)) (k : κ) (A : Cube.{v} μ R)
    (hA : ∀ t : Finset κ, t.Nonempty → t ≠ {k} →
      (cechComplex (slice e (t.map f.toEmbedding) A)).Acyclic) (n : ℕ) :
    (cubeComplex (truncBoth e f A)).homology (n + 2) ≅
      (cechComplex (slice e (({k} : Finset κ).map f.toEmbedding) A)).homology n :=
  truncOverHomologyIsoSingleton h ordConnected_nonempty k A
    (fun t ht ht' => (cubeComplex_trunc₁_acyclic_iff _).2 (hA t ht ht')) (n + 1) ≪≫
  truncHomologyIso _ n
end Compare
namespace Cube
section Sum
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
variable (ι κ) in

def inlEmb : ι ↪o ι ⊕ₗ κ := OrderEmbedding.ofStrictMono _ Sum.Lex.inl_strictMono
variable (ι κ) in

def inrEmb : κ ↪o ι ⊕ₗ κ := OrderEmbedding.ofStrictMono _ Sum.Lex.inr_strictMono
@[simp]
theorem inlEmb_apply (i : ι) : inlEmb ι κ i = toLex (Sum.inl i) := rfl
@[simp]
theorem inrEmb_apply (k : κ) : inrEmb ι κ k = toLex (Sum.inr k) := rfl
variable (ι κ) in

theorem isCompl_range_inlEmb_inrEmb : IsCompl (Set.range (inlEmb ι κ)) (Set.range (inrEmb ι κ)) :=
  Set.isCompl_range_inl_range_inr
def sumVertex (s : Finset ι) (t : Finset κ) : Finset (ι ⊕ₗ κ) :=
  s.map (inlEmb ι κ).toEmbedding ∪ t.map (inrEmb ι κ).toEmbedding
@[simp]
theorem part_inlEmb_sumVertex (s : Finset ι) (t : Finset κ) :
    part (inlEmb ι κ) (sumVertex s t) = s :=
  part_union_left (isCompl_range_inlEmb_inrEmb ι κ).disjoint s t
@[simp]
theorem part_inrEmb_sumVertex (s : Finset ι) (t : Finset κ) :
    part (inrEmb ι κ) (sumVertex s t) = t :=
  part_union_right (isCompl_range_inlEmb_inrEmb ι κ).disjoint s t
@[simp]
theorem sumVertex_part (u : Finset (ι ⊕ₗ κ)) :
    sumVertex (part (inlEmb ι κ) u) (part (inrEmb ι κ) u) = u :=
  map_part_union_map_part (isCompl_range_inlEmb_inrEmb ι κ).codisjoint u
@[simp]
theorem inl_mem_sumVertex {s : Finset ι} {t : Finset κ} {i : ι} :
    toLex (Sum.inl i) ∈ sumVertex s t ↔ i ∈ s := by
  rw [← inlEmb_apply, ← mem_part, part_inlEmb_sumVertex]
@[simp]
theorem inr_mem_sumVertex {s : Finset ι} {t : Finset κ} {k : κ} :
    toLex (Sum.inr k) ∈ sumVertex s t ↔ k ∈ t := by
  rw [← inrEmb_apply, ← mem_part, part_inrEmb_sumVertex]
theorem sumVertex_mono {s s' : Finset ι} {t t' : Finset κ} (hs : s ⊆ s') (ht : t ⊆ t') :
    sumVertex s t ⊆ sumVertex s' t' :=
  Finset.union_subset_union (Finset.map_subset_map.2 hs) (Finset.map_subset_map.2 ht)
def sliceSnd (A : Cube.{v} (ι ⊕ₗ κ) R) (s : Finset ι) : Cube.{v} κ R :=
  comap (fun t => sumVertex s t) (fun _ _ h => sumVertex_mono (subset_refl s) h) A
def sliceFst (A : Cube.{v} (ι ⊕ₗ κ) R) (t : Finset κ) : Cube.{v} ι R :=
  comap (fun s => sumVertex s t) (fun _ _ h => sumVertex_mono h (subset_refl t)) A
theorem sliceSnd_eq_slice (A : Cube.{v} (ι ⊕ₗ κ) R) (s : Finset ι) :
    sliceSnd A s = slice (inrEmb ι κ) (s.map (inlEmb ι κ).toEmbedding) A := rfl
theorem sliceFst_eq_slice (A : Cube.{v} (ι ⊕ₗ κ) R) (t : Finset κ) :
    sliceFst A t = slice (inlEmb ι κ) (t.map (inrEmb ι κ).toEmbedding) A :=
  comap_congr _ _ (fun _ => Finset.union_comm _ _) A
theorem sliceSnd_empty (A : Cube.{v} (ι ⊕ₗ κ) R) : sliceSnd A ∅ = lowerFace (inrEmb ι κ) A := by
  rw [sliceSnd_eq_slice, Finset.map_empty, slice_empty]
theorem sliceFst_empty (A : Cube.{v} (ι ⊕ₗ κ) R) : sliceFst A ∅ = lowerFace (inlEmb ι κ) A := by
  rw [sliceFst_eq_slice, Finset.map_empty, slice_empty]
noncomputable def trunc₂ (A : Cube.{v} (ι ⊕ₗ κ) R) : Cube.{v} (ι ⊕ₗ κ) R :=
  truncBoth (inlEmb ι κ) (inrEmb ι κ) A
theorem isUpperSet_partsIn_nonempty {μ : Type} [LinearOrder μ] (e : ι ↪o μ) (f : κ ↪o μ) :
    IsUpperSet (partsIn e f {s | s.Nonempty} {t | t.Nonempty}) :=
  (isUpperSet_nonempty.preimage (monotone_part e)).inter
    (isUpperSet_nonempty.preimage (monotone_part f))
noncomputable def trunc₁Incl (A : Cube.{v} ι R) : trunc₁ A ⟶ A :=
  suppIncl A ordConnected_nonempty isUpperSet_nonempty
noncomputable def trunc₂Incl (A : Cube.{v} (ι ⊕ₗ κ) R) : trunc₂ A ⟶ A :=
  suppIncl A (ordConnected_partsIn _ _ ordConnected_nonempty ordConnected_nonempty)
    (isUpperSet_partsIn_nonempty _ _)
noncomputable def trunc₂Iso {A B : Cube.{v} (ι ⊕ₗ κ) R} (φ : A ⟶ B)
    (hφ : ∀ (s : Finset ι) (t : Finset κ), s.Nonempty → t.Nonempty →
      Function.Bijective (φ.app (sumVertex s t)).hom) : trunc₂ A ≅ trunc₂ B :=
  suppIso φ (ordConnected_partsIn _ _ ordConnected_nonempty ordConnected_nonempty) fun u hu => by
    have := hφ _ _ hu.1 hu.2
    rwa [sumVertex_part] at this
end Sum
end Cube
section Main
open Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
noncomputable def truncOverHomologyIsoSliceFst [Finite ι] {Q : Set (Finset ι)}
    (hQ : Q.OrdConnected) (A : Cube.{v} (ι ⊕ₗ κ) R)
    (hA : ∀ s ∈ Q, (cubeComplex (sliceSnd A s)).Acyclic) (n : ℕ) :
    (cubeComplex (truncOver (inlEmb ι κ) (inrEmb ι κ) Q hQ A)).homology (n + 1) ≅
      (cubeComplex (supp (sliceFst A ∅) Q hQ)).homology n :=
  truncOverHomologyIsoEmpty (isCompl_range_inlEmb_inrEmb ι κ) hQ A hA n ≪≫
    cubeHomologyMapIso (eqToIso (by rw [sliceFst_empty])) n
noncomputable def truncOverHomologyIsoSliceFstSingleton [Finite κ] {Q : Set (Finset ι)}
    (hQ : Q.OrdConnected) (k : κ) (A : Cube.{v} (ι ⊕ₗ κ) R)
    (hA : ∀ t : Finset κ, t.Nonempty → t ≠ {k} →
      (cubeComplex (supp (sliceFst A t) Q hQ)).Acyclic) (n : ℕ) :
    (cubeComplex (truncOver (inlEmb ι κ) (inrEmb ι κ) Q hQ A)).homology (n + 1) ≅
      (cubeComplex (supp (sliceFst A {k}) Q hQ)).homology n :=
  truncOverHomologyIsoSingleton (isCompl_range_inlEmb_inrEmb ι κ) hQ k A
      (fun t ht ht' => sliceFst_eq_slice A t ▸ hA t ht ht') n ≪≫
    cubeHomologyMapIso (eqToIso (by rw [sliceFst_eq_slice])) n
noncomputable def trunc₂HomologyIsoFst [Finite ι] (A : Cube.{v} (ι ⊕ₗ κ) R)
    (hA : ∀ s : Finset ι, s.Nonempty → (cubeComplex (sliceSnd A s)).Acyclic) (n : ℕ) :
    (cubeComplex (trunc₂ A)).homology (n + 2) ≅ (cechComplex (sliceFst A ∅)).homology n :=
  truncOverHomologyIsoSliceFst ordConnected_nonempty A hA (n + 1) ≪≫ truncHomologyIso _ n
noncomputable def trunc₂HomologyIsoSnd [Finite κ] (A : Cube.{v} (ι ⊕ₗ κ) R)
    (hA : ∀ t : Finset κ, t.Nonempty → (cubeComplex (sliceFst A t)).Acyclic) (n : ℕ) :
    (cubeComplex (trunc₂ A)).homology (n + 2) ≅ (cechComplex (sliceSnd A ∅)).homology n :=
  cubeHomologyMapIso (eqToIso (truncBoth_comm A)) (n + 2) ≪≫
    truncBothHomologyIsoEmpty (isCompl_range_inlEmb_inrEmb ι κ).symm A
      (fun t ht => sliceFst_eq_slice A t ▸ hA t ht) n ≪≫
    cechHomologyMapIso (eqToIso (sliceSnd_empty A).symm) n
noncomputable def trunc₂HomologyIsoFstSingleton [Finite κ] (k : κ) (A : Cube.{v} (ι ⊕ₗ κ) R)
    (hA : ∀ t : Finset κ, t.Nonempty → t ≠ {k} → (cechComplex (sliceFst A t)).Acyclic) (n : ℕ) :
    (cubeComplex (trunc₂ A)).homology (n + 2) ≅ (cechComplex (sliceFst A {k})).homology n :=
  truncOverHomologyIsoSliceFstSingleton ordConnected_nonempty k A
    (fun t ht ht' => (cubeComplex_trunc₁_acyclic_iff _).2 (hA t ht ht')) (n + 1) ≪≫
  truncHomologyIso _ n
noncomputable def trunc₂HomologyIsoSndSingleton [Finite ι] (i : ι) (A : Cube.{v} (ι ⊕ₗ κ) R)
    (hA : ∀ s : Finset ι, s.Nonempty → s ≠ {i} → (cechComplex (sliceSnd A s)).Acyclic) (n : ℕ) :
    (cubeComplex (trunc₂ A)).homology (n + 2) ≅ (cechComplex (sliceSnd A {i})).homology n :=
  cubeHomologyMapIso (eqToIso (truncBoth_comm A)) (n + 2) ≪≫
    truncBothHomologyIsoSingleton (isCompl_range_inlEmb_inrEmb ι κ).symm i A hA n
end Main
section Three
open Cube
variable {ι κ ν : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] {R : Type u} [Ring R]
omit [LinearOrder ι] [LinearOrder κ] in

instance finite_sumLex [Finite ι] [Finite κ] : Finite (ι ⊕ₗ κ) := inferInstanceAs (Finite (ι ⊕ κ))
noncomputable def Cube.trunc₃ (A : Cube.{v} ((ι ⊕ₗ κ) ⊕ₗ ν) R) : Cube.{v} ((ι ⊕ₗ κ) ⊕ₗ ν) R :=
  truncOver (inlEmb _ _) (inrEmb _ _)
    (partsIn (inlEmb ι κ) (inrEmb ι κ) {s | s.Nonempty} {t | t.Nonempty})
    (ordConnected_partsIn _ _ ordConnected_nonempty ordConnected_nonempty) A
variable (ι κ ν) in

def Cube.lastTwoEmb : κ ⊕ₗ ν ↪o (ι ⊕ₗ κ) ⊕ₗ ν :=
  (inrEmb ι (κ ⊕ₗ ν)).trans (OrderIso.sumLexAssoc ι κ ν).symm.toOrderEmbedding
variable (ι κ ν) in

def Cube.firstEmb : ι ↪o (ι ⊕ₗ κ) ⊕ₗ ν := (inlEmb ι κ).trans (inlEmb (ι ⊕ₗ κ) ν)
@[simp]
theorem Cube.lastTwoEmb_inl (k : κ) :
    lastTwoEmb ι κ ν (toLex (Sum.inl k)) = toLex (Sum.inl (toLex (Sum.inr k))) := rfl
@[simp]
theorem Cube.lastTwoEmb_inr (l : ν) :
    lastTwoEmb ι κ ν (toLex (Sum.inr l)) = toLex (Sum.inr l) := rfl
@[simp]
theorem Cube.firstEmb_apply (i : ι) :
    firstEmb ι κ ν i = toLex (Sum.inl (toLex (Sum.inl i))) := rfl
variable (ι κ ν) in

theorem Cube.isCompl_range_lastTwoEmb_firstEmb :
    IsCompl (Set.range (lastTwoEmb ι κ ν)) (Set.range (firstEmb ι κ ν)) := by
  constructor
  · rw [Set.disjoint_left]
    rintro _ ⟨j, rfl⟩ ⟨i, hi⟩
    rcases j with j | j <;> cases hi
  · rw [codisjoint_iff]
    refine Set.eq_univ_of_forall fun j => ?_
    rcases j with (i | k) | l
    · exact Or.inr ⟨i, rfl⟩
    · exact Or.inl ⟨toLex (Sum.inl k), rfl⟩
    · exact Or.inl ⟨toLex (Sum.inr l), rfl⟩
theorem Cube.map_lastTwoEmb_union (s : Finset ι) (t : Finset κ) (w : Finset ν) :
    (sumVertex t w).map (lastTwoEmb ι κ ν).toEmbedding ∪ s.map (firstEmb ι κ ν).toEmbedding =
      sumVertex (sumVertex s t) w := by
  simp only [sumVertex, Finset.map_union, Finset.map_map]
  rw [Finset.union_comm, ← Finset.union_assoc]
  rfl
noncomputable def trunc₃HomologyIsoDropLast [Finite ι] [Finite κ]
    (A : Cube.{v} ((ι ⊕ₗ κ) ⊕ₗ ν) R)
    (hA : ∀ (s : Finset ι) (t : Finset κ), s.Nonempty → t.Nonempty →
      (cubeComplex (sliceSnd A (sumVertex s t))).Acyclic) (n : ℕ) :
    (cubeComplex (trunc₃ A)).homology (n + 1) ≅
      (cubeComplex (trunc₂ (sliceFst A ∅))).homology n :=
  truncOverHomologyIsoSliceFst _ A (fun u hu => by
    have := hA _ _ hu.1 hu.2
    rwa [sumVertex_part] at this) n
noncomputable def trunc₃HomologyIsoDropFirst [Finite κ] [Finite ν]
    (A : Cube.{v} ((ι ⊕ₗ κ) ⊕ₗ ν) R)
    (hA : ∀ (t : Finset κ) (w : Finset ν), t.Nonempty → w.Nonempty →
      (cubeComplex (sliceFst (sliceFst A w) t)).Acyclic) (n : ℕ) :
    (cubeComplex (trunc₃ A)).homology (n + 1) ≅
      (cubeComplex (trunc₂ (lowerFace (lastTwoEmb ι κ ν) A))).homology n :=
  have hQ := ordConnected_partsIn (inlEmb κ ν) (inrEmb κ ν) ordConnected_nonempty
    ordConnected_nonempty
  cubeHomologyMapIso (eqToIso (show trunc₃ A =
      truncOver (lastTwoEmb ι κ ν) (firstEmb ι κ ν) _ hQ A from
    supp_congr (hP := ordConnected_partsIn _ _
        (ordConnected_partsIn _ _ ordConnected_nonempty ordConnected_nonempty)
        ordConnected_nonempty) (hP' := ordConnected_partsIn _ _ hQ ordConnected_nonempty) A
      fun u => by
        simp only [mem_partsIn, Set.mem_setOf_eq, Finset.Nonempty, mem_part, inlEmb_apply,
          inrEmb_apply, Cube.lastTwoEmb_inl, Cube.lastTwoEmb_inr, Cube.firstEmb_apply]
        tauto)) (n + 1) ≪≫
  truncOverHomologyIsoEmpty (Cube.isCompl_range_lastTwoEmb_firstEmb ι κ ν) hQ A (fun u hu => by
    have h : slice (firstEmb ι κ ν) (u.map (lastTwoEmb ι κ ν).toEmbedding) A =
        sliceFst (sliceFst A (part (inrEmb κ ν) u)) (part (inlEmb κ ν) u) :=
      comap_congr _ (fun _ _ h => sumVertex_mono (sumVertex_mono h (subset_refl _)) (subset_refl _))
        (fun s => by rw [← Cube.map_lastTwoEmb_union, sumVertex_part]; rfl) A
    rw [h]
    exact hA _ _ hu.1 hu.2) n
end Three
section Examples
example : ¬ IsZero ((cubeComplex (Cube.trunc₂
    (Cube.const (Fin 1 ⊕ₗ Fin 1) (ModuleCat.of ℤ ℤ)))).homology 2) := fun h => by
  have h' := h.of_iso (trunc₂HomologyIsoFst (Cube.const (Fin 1 ⊕ₗ Fin 1) (ModuleCat.of ℤ ℤ))
    (fun s _ => cubeComplex_acyclic_of_bijective _ 0 fun _ _ => Function.bijective_id) 0).symm
  rw [← exactAt_iff_isZero_homology, cochainComplex_exactAt_zero_iff, cechComplex_d _ 0] at h'
  have h0 : Cube.aug (Cube.sliceFst (Cube.const (Fin 1 ⊕ₗ Fin 1) (ModuleCat.of ℤ ℤ)) ∅)
      (1 : ℤ) = 0 := h' ((Cube.d_aug _ _).trans (map_zero _).symm)
  exact (one_ne_zero : (1 : ℤ) ≠ 0) (congrFun h0 ⟨{0}, rfl⟩)
end Examples
end GlobalTheory


