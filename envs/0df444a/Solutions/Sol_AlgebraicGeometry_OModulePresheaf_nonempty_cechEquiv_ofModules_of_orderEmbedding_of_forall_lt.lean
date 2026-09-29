-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/69dc8736-dc2b-5a0b-98a2-072d061d8aa8

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_of_isQuasicoherent
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import Theorems.Thm_LinearMap_exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped Classical

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace P2mAdjoinChart

section Restrict

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F : OModulePresheaf π) (U : V.Opens)

theorem appIso_inv_comp_algebraMap (W : (U : Scheme.{u}).Opens) :
    ((Scheme.ΓSpecIso (.of R)).inv ≫ (U.ι ≫ π).appLE ⊤ W le_top) ≫ (U.ι.appIso W).inv =
      (Scheme.ΓSpecIso (.of R)).inv ≫ π.appLE ⊤ (U.ι ''ᵁ W) le_top := by
  rw [Category.assoc, Scheme.Hom.comp_appLE, Category.assoc, Scheme.Hom.appLE_appIso_inv, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_map]

theorem appIso_inv_algebraMap (W : (U : Scheme.{u}).Opens) (r : R) :
    (U.ι.appIso W).inv.hom ((Scheme.TwoAffineOpenCover.algebraOfHom (U.ι ≫ π) W).algebraMap r) =
      (Scheme.TwoAffineOpenCover.algebraOfHom π (U.ι ''ᵁ W)).algebraMap r := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom, Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  have := congrArg (fun φ => φ.hom r) (appIso_inv_comp_algebraMap (π := π) U W)
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using this

theorem appIso_inv_map {W W' : (U : Scheme.{u}).Opens} (h : W ≤ W') (a : Γ(↑U, W')) :
    (U.ι.appIso W).inv.hom (((U : Scheme.{u}).presheaf.map (homOfLE h).op).hom a) =
      (V.presheaf.map (homOfLE (U.ι.image_mono h)).op).hom ((U.ι.appIso W').inv.hom a) := by
  have := congrArg (fun φ => φ.hom a) (U.ι.appIso_inv_naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  rw [this]
  rfl

def restrictOpen : OModulePresheaf (U.ι ≫ π) where
  obj W := F.obj (U.ι ''ᵁ W)
  addCommGroup W := inferInstance
  module W := inferInstance
  moduleSections W := Module.compHom (F.obj (U.ι ''ᵁ W)) (U.ι.appIso W).inv.hom
  isScalarTower W := by
    letI : Module Γ(↑U, W) (F.obj (U.ι ''ᵁ W)) := Module.compHom (F.obj (U.ι ''ᵁ W)) (U.ι.appIso W).inv.hom
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (U.ι ≫ π) W
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π (U.ι ''ᵁ W)
    refine IsScalarTower.of_algebraMap_smul fun r x => ?_
    show (U.ι.appIso W).inv.hom (algebraMap R Γ(↑U, W) r) • x = r • x
    rw [appIso_inv_algebraMap, algebraMap_smul]
  res h := F.res (U.ι.image_mono h)
  res_smul {W W'} h a x := by
    show F.res (U.ι.image_mono h) ((U.ι.appIso W').inv.hom a • x) =
      (U.ι.appIso W).inv.hom (((U : Scheme.{u}).presheaf.map (homOfLE h).op).hom a) • F.res (U.ι.image_mono h) x
    rw [F.res_smul, appIso_inv_map]
  res_refl W := F.res_refl _
  res_comp h h' := F.res_comp _ _

theorem restrictOpen_res {W W' : (U : Scheme.{u}).Opens} (h : W ≤ W') (x : F.obj (U.ι ''ᵁ W')) :
    (restrictOpen F U).res h (show (restrictOpen F U).obj W' from x) = F.res (U.ι.image_mono h) x := rfl

theorem restrictOpen_smul (W : (U : Scheme.{u}).Opens) (a : Γ(↑U, W)) (x : F.obj (U.ι ''ᵁ W)) :
    (a • (show (restrictOpen F U).obj W from x)) =
      (show (restrictOpen F U).obj W from (U.ι.appIso W).inv.hom a • x) :=
  rfl

theorem res_irrel {A B : V.Opens} (h h' : A ≤ B) (x : F.obj B) : F.res h x = F.res h' x := rfl

theorem res_res_eq {A B : V.Opens} (e : A = B) (x : F.obj A) : F.res (le_of_eq e) (F.res (le_of_eq e.symm) x) = x := by
  rw [F.res_res, F.res_refl_apply]

theorem isQuasicoherent_restrictOpen (hF : F.IsQuasicoherent) : (restrictOpen F U).IsQuasicoherent := by
  intro W g
  have hW : IsAffineOpen (U.ι ''ᵁ W.1) := W.2.image_of_isOpenImmersion U.ι
  set g' : Γ(V, U.ι ''ᵁ W.1) := (U.ι.appIso W.1).inv.hom g with hg'
  have himg : U.ι ''ᵁ ((U : Scheme.{u}).basicOpen g) = V.basicOpen g' := Scheme.image_basicOpen U.ι g
  have hle : U.ι ''ᵁ ((U : Scheme.{u}).basicOpen g) ≤ U.ι ''ᵁ W.1 :=
    U.ι.image_mono ((U : Scheme.{u}).basicOpen_le g)
  obtain ⟨h1, h2⟩ := hF ⟨U.ι ''ᵁ W.1, hW⟩ g'

  have factA : ∀ y : F.obj (U.ι ''ᵁ W.1),
      F.res hle y = F.res (le_of_eq himg) (F.res (V.basicOpen_le g') y) := fun y => by
    rw [F.res_res]
  have hpow : ∀ n : ℕ, (U.ι.appIso W.1).inv.hom (g ^ n) = g' ^ n := fun n => by rw [map_pow]
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := h1 (F.res (le_of_eq himg.symm) x)
    refine ⟨n, y, ?_⟩
    rw [restrictOpen_res, restrictOpen_smul, res_irrel F _ hle, factA, hy, F.res_smul, res_res_eq F himg,
      ← CommRingCat.comp_apply, ← V.presheaf.map_comp, appIso_inv_map, hpow]
    rfl
  · intro y hy
    have hy0 : F.res hle y = 0 := hy
    have hy' : F.res (V.basicOpen_le g') y = 0 := by
      have := congrArg (F.res (le_of_eq himg.symm)) (factA y)
      rw [F.res_res (le_of_eq himg.symm) (le_of_eq himg), F.res_refl_apply, hy0, map_zero] at this
      exact this.symm
    obtain ⟨n, hn⟩ := h2 y hy'
    refine ⟨n, ?_⟩
    rw [restrictOpen_smul, hpow]
    exact hn

end Restrict

section Cover

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
  (K : V.OrderedAffineCover) (U : V.Opens) (hUa : IsAffineOpen U)

theorem image_preimage (W : V.Opens) : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = U ⊓ W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

theorem mem_iInf_fin {X : Scheme.{u}} {n : ℕ} (W : Fin (n + 1) → X.Opens) (x : X) :
    x ∈ (⨅ j, W j) ↔ ∀ j, x ∈ W j := by
  constructor
  · exact fun hx j => (iInf_le W j) hx
  · intro hx
    have hopen : IsOpen (⋂ j, (W j : Set X)) := isOpen_iInter_of_finite fun j => (W j).isOpen
    have hle : (⟨⋂ j, (W j : Set X), hopen⟩ : X.Opens) ≤ ⨅ j, W j :=
      le_iInf fun j => fun y hy => Set.mem_iInter.mp hy j
    exact hle (Set.mem_iInter.mpr hx)

theorem preimage_iInf {n : ℕ} (W : Fin (n + 1) → V.Opens) : (⨅ j, U.ι ⁻¹ᵁ W j) = U.ι ⁻¹ᵁ (⨅ j, W j) := by
  ext x
  rw [SetLike.mem_coe, SetLike.mem_coe, mem_iInf_fin]
  show (∀ j, U.ι.base x ∈ W j) ↔ U.ι.base x ∈ (⨅ j, W j)
  rw [mem_iInf_fin]

include hUa in

def coverOn : (U : Scheme.{u}).OrderedAffineCover where
  ι := K.ι
  U i := U.ι ⁻¹ᵁ K.U i
  isAffineOpen i := by
    rw [← U.ι.isAffineOpen_iff_of_isOpenImmersion, image_preimage]
    exact Scheme.OrderedAffineCover.isAffineOpen_inf_of_isSeparated π hUa (K.isAffineOpen i)
  iSup_eq_top := by
    apply le_antisymm le_top
    intro x _
    have hx : (U.ι.base x) ∈ (⊤ : V.Opens) := trivial
    rw [← K.iSup_eq_top, Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    exact Opens.mem_iSup.mpr ⟨i, hi⟩

theorem coverOn_U (i : K.ι) : (coverOn π K U hUa).U i = U.ι ⁻¹ᵁ K.U i := rfl

theorem image_inter {n : ℕ} (s : (coverOn π K U hUa).Idx n) :
    U.ι ''ᵁ ((coverOn π K U hUa).inter s) = U ⊓ K.inter ⟨s.1, s.2⟩ := by
  show U.ι ''ᵁ (⨅ j, U.ι ⁻¹ᵁ K.U (s.1 j)) = U ⊓ ⨅ j, K.U (s.1 j)
  rw [preimage_iInf, image_preimage]

end Cover

section Acyclic

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
  (F : OModulePresheaf π) (K : V.OrderedAffineCover) (U : V.Opens) (hUa : IsAffineOpen U)

include hUa in
theorem subsingleton_HSucc_restrictOpen (hF : F.IsQuasicoherent) (n : ℕ) :
    Subsingleton ((restrictOpen F U).HSucc (coverOn π K U hUa) n) := by
  haveI : IsAffine (U : Scheme.{u}) := hUa
  haveI : IsSeparated (U.ι ≫ π) := inferInstance
  exact OModulePresheaf.subsingleton_HSucc_of_isQuasicoherent (restrictOpen F U)
    (isQuasicoherent_restrictOpen F U hF) (coverOn π K U hUa) n

theorem exists_d_eq_of_subsingleton_HSucc {W : Scheme.{u}} {ρ : W ⟶ Spec (.of R)} (G : OModulePresheaf ρ)
    (L : W.OrderedAffineCover) (n : ℕ) [Subsingleton (G.HSucc L n)] (x : G.cochain L (n + 1))
    (hx : G.d L (n + 1) x = 0) : ∃ y : G.cochain L n, G.d L n y = x := by
  have hmem : (⟨x, hx⟩ : LinearMap.ker (G.d L (n + 1))) ∈
      (LinearMap.range (G.d L n)).comap (LinearMap.ker (G.d L (n + 1))).subtype := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact Subsingleton.elim _ _
  simpa using hmem

end Acyclic

section Snoc

variable {α : Type u} {n : ℕ}

def snoc' (f : Fin (n + 1) → α) (a : α) : Fin (n + 2) → α := @Fin.snoc (n + 1) (fun _ => α) f a

theorem snoc'_castSucc (f : Fin (n + 1) → α) (a : α) (k : Fin (n + 1)) : snoc' f a (Fin.castSucc k) = f k :=
  Fin.snoc_castSucc (α := fun _ => α) a f k

theorem snoc'_last (f : Fin (n + 1) → α) (a : α) : snoc' f a (Fin.last _) = a :=
  Fin.snoc_last (α := fun _ => α) a f

theorem fin_one_eq (a b : Fin (0 + 1)) : a = b := by
  haveI : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
  exact Subsingleton.elim a b

end Snoc

section Chains

variable {V : Scheme.{u}} (K K' : V.OrderedAffineCover) (e : K.ι ↪o K'.ι) (j₀ : K'.ι)
  (hj₀ : ∀ j : K'.ι, j = j₀ ∨ j ∈ Set.range e) (hlt : ∀ i, e i < j₀)

def idxE (n : ℕ) (s : K.Idx n) : K'.Idx n := ⟨e ∘ s.1, e.strictMono.comp s.2⟩

theorem idxE_face {n : ℕ} (s : K.Idx (n + 1)) (j : Fin (n + 2)) :
    idxE K K' e n (K.face s j) = K'.face (idxE K K' e (n + 1) s) j := rfl

theorem idxE_injective (n : ℕ) : Function.Injective (idxE K K' e n) := fun _ _ h =>
  Subtype.ext (funext fun k => e.injective (congrFun (congrArg Subtype.val h) k))

include hlt in
theorem strictMono_snoc {n : ℕ} (s : K.Idx n) : StrictMono (snoc' (e ∘ s.1) j₀) := by
  intro a b hab
  induction b using Fin.lastCases with
  | last =>
    induction a using Fin.lastCases with
    | last => exact absurd hab (lt_irrefl _)
    | cast a => rw [snoc'_castSucc, snoc'_last]; exact hlt _
  | cast b =>
    induction a using Fin.lastCases with
    | last => exact absurd (Fin.castSucc_lt_last b) (not_lt.mpr hab.le)
    | cast a =>
      rw [snoc'_castSucc, snoc'_castSucc]
      exact e.strictMono (s.2 (Fin.castSucc_lt_castSucc_iff.mp hab))

def snocIdx (n : ℕ) (s : K.Idx n) : K'.Idx (n + 1) := ⟨snoc' (e ∘ s.1) j₀, strictMono_snoc K K' e j₀ hlt s⟩

theorem snocIdx_apply_castSucc {n : ℕ} (s : K.Idx n) (k : Fin (n + 1)) :
    (snocIdx K K' e j₀ hlt n s).1 (Fin.castSucc k) = e (s.1 k) := snoc'_castSucc _ _ k

theorem snocIdx_apply_last {n : ℕ} (s : K.Idx n) : (snocIdx K K' e j₀ hlt n s).1 (Fin.last _) = j₀ :=
  snoc'_last _ _

def vtx : K'.Idx 0 := ⟨fun _ => j₀, fun a b h => absurd h (by rw [fin_one_eq a b]; exact lt_irrefl _)⟩

theorem face_snocIdx_last {n : ℕ} (s : K.Idx (n + 1)) :
    K'.face (snocIdx K K' e j₀ hlt (n + 1) s) (Fin.last _) = idxE K K' e (n + 1) s := by
  apply Subtype.ext
  funext k
  show snoc' (e ∘ s.1) j₀ (Fin.succAbove (Fin.last _) k) = e (s.1 k)
  rw [Fin.succAbove_last, snoc'_castSucc]
  rfl

theorem face_snocIdx_castSucc {n : ℕ} (s : K.Idx (n + 1)) (j : Fin (n + 2)) :
    K'.face (snocIdx K K' e j₀ hlt (n + 1) s) (Fin.castSucc j) = snocIdx K K' e j₀ hlt n (K.face s j) := by
  apply Subtype.ext
  funext k
  show snoc' (e ∘ s.1) j₀ (Fin.succAbove (Fin.castSucc j) k) = snoc' (e ∘ (s.1 ∘ Fin.succAbove j)) j₀ k
  induction k using Fin.lastCases with
  | last => rw [Fin.succAbove_castSucc_of_le j (Fin.last _) (Fin.le_last j), Fin.succ_last, snoc'_last, snoc'_last]
  | cast k => rw [Fin.castSucc_succAbove_castSucc, snoc'_castSucc, snoc'_castSucc]; rfl

theorem face_snocIdx_zero (s : K.Idx 0) : K'.face (snocIdx K K' e j₀ hlt 0 s) 0 = vtx K' j₀ := by
  apply Subtype.ext
  funext k
  show snoc' (e ∘ s.1) j₀ (Fin.succAbove 0 k) = j₀
  rw [fin_one_eq k 0]
  exact snoc'_last (n := 0) _ _

theorem face_snocIdx_one (s : K.Idx 0) : K'.face (snocIdx K K' e j₀ hlt 0 s) 1 = idxE K K' e 0 s := by
  apply Subtype.ext
  funext k
  show snoc' (e ∘ s.1) j₀ (Fin.succAbove 1 k) = e (s.1 k)
  rw [fin_one_eq k 0]
  exact snoc'_castSucc (n := 0) _ _ 0

theorem snocIdx_injective (n : ℕ) : Function.Injective (snocIdx K K' e j₀ hlt n) := by
  intro s s' h
  apply Subtype.ext; funext k
  have := congrFun (congrArg Subtype.val h) (Fin.castSucc k)
  rw [snocIdx_apply_castSucc, snocIdx_apply_castSucc] at this
  exact e.injective this

include hlt in
theorem idxE_ne_snocIdx {n : ℕ} (s : K.Idx (n + 1)) (s' : K.Idx n) :
    idxE K K' e (n + 1) s ≠ snocIdx K K' e j₀ hlt n s' := by
  intro h
  have := congrFun (congrArg Subtype.val h) (Fin.last _)
  rw [snocIdx_apply_last] at this
  exact absurd this (ne_of_lt (hlt _))

include hlt in
theorem idxE_ne_vtx (s : K.Idx 0) : idxE K K' e 0 s ≠ vtx K' j₀ := by
  intro h
  have := congrFun (congrArg Subtype.val h) 0
  exact absurd this (ne_of_lt (hlt _))

include hj₀ hlt in

theorem idx_cases {n : ℕ} (t : K'.Idx (n + 1)) :
    (∃ s : K.Idx (n + 1), t = idxE K K' e (n + 1) s) ∨ (∃ s : K.Idx n, t = snocIdx K K' e j₀ hlt n s) := by
  have hbelow : ∀ k : Fin (n + 1), t.1 (Fin.castSucc k) ∈ Set.range e := by
    intro k
    rcases hj₀ (t.1 (Fin.castSucc k)) with h | h
    · exfalso
      have hlt' : t.1 (Fin.castSucc k) < t.1 (Fin.last _) := t.2 (Fin.castSucc_lt_last k)
      rcases hj₀ (t.1 (Fin.last _)) with h' | ⟨i, hi⟩
      · rw [h, h'] at hlt'; exact lt_irrefl _ hlt'
      · rw [h, ← hi] at hlt'; exact absurd (hlt i) (not_lt.mpr hlt'.le)
    · exact h
  choose g hg using hbelow
  have hgmono : StrictMono g := fun a b hab => by
    have : e (g a) < e (g b) := by rw [hg, hg]; exact t.2 (Fin.castSucc_lt_castSucc_iff.mpr hab)
    exact e.lt_iff_lt.mp this
  rcases hj₀ (t.1 (Fin.last _)) with htop | ⟨i, hi⟩
  · right
    refine ⟨⟨g, hgmono⟩, Subtype.ext (funext fun k => ?_)⟩
    induction k using Fin.lastCases with
    | last => rw [snocIdx_apply_last]; exact htop
    | cast k => rw [snocIdx_apply_castSucc]; exact (hg k).symm
  · left
    have key : ∀ k, e (snoc' g i k) = t.1 k := fun k => by
      induction k using Fin.lastCases with
      | last => rw [snoc'_last]; exact hi
      | cast k => rw [snoc'_castSucc]; exact hg k
    refine ⟨⟨snoc' g i, fun a b hab => ?_⟩, Subtype.ext (funext fun k => (key k).symm)⟩
    have : e (snoc' g i a) < e (snoc' g i b) := by rw [key, key]; exact t.2 hab
    exact e.lt_iff_lt.mp this

include hj₀ in
theorem idx_cases_zero (t : K'.Idx 0) : (∃ s : K.Idx 0, t = idxE K K' e 0 s) ∨ t = vtx K' j₀ := by
  rcases hj₀ (t.1 0) with h | ⟨i, hi⟩
  · right; apply Subtype.ext; funext k; rw [fin_one_eq k 0]; exact h
  · left
    refine ⟨⟨fun _ => i, fun a b hab => absurd hab (by rw [fin_one_eq a b]; exact lt_irrefl _)⟩,
      Subtype.ext (funext fun k => ?_)⟩
    rw [fin_one_eq k 0]; exact hi.symm

variable (hU : ∀ i, K'.U (e i) = K.U i)

include hU in
theorem inter_idxE {n : ℕ} (s : K.Idx n) : K'.inter (idxE K K' e n s) = K.inter s := by
  show (⨅ j, K'.U ((e ∘ s.1) j)) = ⨅ j, K.U (s.1 j)
  exact iInf_congr fun j => by rw [Function.comp_apply, hU]

include hU in
theorem inter_snocIdx {n : ℕ} (s : K.Idx n) : K'.inter (snocIdx K K' e j₀ hlt n s) = K'.U j₀ ⊓ K.inter s := by
  show (⨅ k, K'.U (snoc' (e ∘ s.1) j₀ k)) = K'.U j₀ ⊓ ⨅ j, K.U (s.1 j)
  apply le_antisymm
  · refine le_inf ?_ (le_iInf fun j => ?_)
    · exact (iInf_le _ (Fin.last _)).trans (by rw [snoc'_last])
    · exact (iInf_le _ (Fin.castSucc j)).trans (by rw [snoc'_castSucc, Function.comp_apply, hU])
  · refine le_iInf fun k => ?_
    induction k using Fin.lastCases with
    | last => rw [snoc'_last]; exact inf_le_left
    | cast j => rw [snoc'_castSucc, Function.comp_apply, hU]; exact inf_le_right.trans (iInf_le _ j)

theorem inter_vtx : K'.inter (vtx K' j₀) = K'.U j₀ :=
  le_antisymm (iInf_le _ 0) (le_iInf fun _ => le_rfl)

end Chains

section Main

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π] (M : V.Modules)
  (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
  (K K' : V.OrderedAffineCover) (e : K.ι ↪o K'.ι) (hU : ∀ i, K'.U (e i) = K.U i)
  (j₀ : K'.ι) (hj₀ : ∀ j : K'.ι, j = j₀ ∨ j ∈ Set.range e) (hlt : ∀ i, e i < j₀)

local notation "𝓕" => OModulePresheaf.ofModules π M

theorem cochain_congr' {W : Scheme.{u}} {ρ : W ⟶ Spec (.of R)} (G : OModulePresheaf ρ) {L : W.OrderedAffineCover}
    {n : ℕ} (c : G.cochain L n) {t t' : L.Idx n} (htt : t = t') {A : W.Opens} (h : A ≤ L.inter t)
    (h' : A ≤ L.inter t') : G.res h (c t) = G.res h' (c t') := by
  subst htt; rfl

theorem res_dcongr {α : Type u} (β : α → V.Opens) (c : ∀ a, (𝓕).obj (β a)) {a₁ a₂ : α} (h12 : a₁ = a₂)
    {A : V.Opens} (h₁ : A ≤ β a₁) (h₂ : A ≤ β a₂) : (𝓕).res h₁ (c a₁) = (𝓕).res h₂ (c a₂) := by
  subst h12; rfl

theorem res_zsmul_res {A B C : V.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C) (z : ℤ) (v : (𝓕).obj C) :
    (𝓕).res h₁ (z • (𝓕).res h₂ v) = z • (𝓕).res (h₁.trans h₂) v := by
  rw [LinearMap.map_smul_of_tower, (𝓕).res_res]

theorem cochain_congr {L : V.OrderedAffineCover} {n : ℕ} (c : (𝓕).cochain L n) {t t' : L.Idx n} (htt : t = t')
    {A : V.Opens} (h : A ≤ L.inter t) (h' : A ≤ L.inter t') : (𝓕).res h (c t) = (𝓕).res h' (c t') := by
  subst htt; rfl

def fMap (n : ℕ) : (𝓕).cochain K' n →ₗ[R] (𝓕).cochain K n :=
  LinearMap.pi fun s => ((𝓕).res (le_of_eq (inter_idxE K K' e hU s).symm)).comp (LinearMap.proj (idxE K K' e n s))

theorem fMap_apply (n : ℕ) (c : (𝓕).cochain K' n) (s : K.Idx n) :
    fMap π M K K' e hU n c s = (𝓕).res (le_of_eq (inter_idxE K K' e hU s).symm) (c (idxE K K' e n s)) := rfl

theorem d_fMap (n : ℕ) (c : (𝓕).cochain K' n) :
    (𝓕).d K n (fMap π M K K' e hU n c) = fMap π M K K' e hU (n + 1) ((𝓕).d K' n c) := by
  funext s
  rw [fMap_apply, OModulePresheaf.d_apply, OModulePresheaf.d_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul_of_tower, fMap_apply, (𝓕).res_res, (𝓕).res_res]
  rfl

theorem fMap_surjective (n : ℕ) : Function.Surjective (fMap π M K K' e hU n) := by
  intro c'
  let c : (𝓕).cochain K' n := fun t =>
    if h : ∃ s, t = idxE K K' e n s then
      (𝓕).res (le_of_eq ((congrArg K'.inter h.choose_spec).trans (inter_idxE K K' e hU _))) (c' h.choose)
    else 0
  refine ⟨c, funext fun s => ?_⟩
  rw [fMap_apply]
  have h : ∃ s', idxE K K' e n s = idxE K K' e n s' := ⟨s, rfl⟩
  have hc : c (idxE K K' e n s) =
      (𝓕).res (le_of_eq ((congrArg K'.inter h.choose_spec).trans (inter_idxE K K' e hU _))) (c' h.choose) :=
    dif_pos h
  rw [hc, (𝓕).res_res]
  have hs : h.choose = s := (idxE_injective K K' e n h.choose_spec).symm
  rw [cochain_congr π M c' hs _ le_rfl, (𝓕).res_refl_apply]

theorem apply_idxE_eq_zero_of_fMap_eq_zero (n : ℕ) (c : (𝓕).cochain K' n) (hc : fMap π M K K' e hU n c = 0)
    (s : K.Idx n) : c (idxE K K' e n s) = 0 := by
  have h := congrFun hc s
  rw [fMap_apply] at h
  have := congrArg ((𝓕).res (le_of_eq (inter_idxE K K' e hU s))) h
  rwa [(𝓕).res_res, (𝓕).res_refl_apply, Pi.zero_apply, map_zero] at this

def sing (i : K.ι) : K.Idx 0 := ⟨fun _ => i, fun a b h => absurd h (by rw [fin_one_eq a b]; exact lt_irrefl _)⟩

theorem eq_sing (s : K.Idx 0) : s = sing K (s.1 0) := Subtype.ext (funext fun k => by rw [fin_one_eq k 0]; rfl)

include hU in

theorem cov_le (i : K.ι) : K'.inter (snocIdx K K' e j₀ hlt 0 (sing K i)) ≤ K'.inter (vtx K' j₀) :=
  (le_of_eq (inter_snocIdx K K' e j₀ hlt hU (sing K i))).trans (inf_le_left.trans (le_of_eq (inter_vtx K' j₀).symm))

include hU in
theorem le_iSup_cov : K'.inter (vtx K' j₀) ≤ ⨆ i, K'.inter (snocIdx K K' e j₀ hlt 0 (sing K i)) := by
  intro x hx
  rw [inter_vtx] at hx
  have hx' : x ∈ (⊤ : V.Opens) := trivial
  rw [← K.iSup_eq_top, Opens.mem_iSup] at hx'
  obtain ⟨i, hi⟩ := hx'
  refine Opens.mem_iSup.mpr ⟨i, ?_⟩
  rw [inter_snocIdx K K' e j₀ hlt hU]
  refine ⟨hx, ?_⟩
  show x ∈ ((⨅ j, K.U ((sing K i).1 j) : V.Opens) : Set V)
  exact (mem_iInf_fin _ x).mpr fun _ => hi

def Msh : TopCat.Sheaf Ab V := ⟨M.presheaf, M.isSheaf⟩

include hj₀ hlt hU in

theorem hex0 (x : (𝓕).cochain K' 0) (hf : fMap π M K K' e hU 0 x = 0) (hd : (𝓕).d K' 0 x = 0) : x = 0 := by
  have hE : ∀ s : K.Idx 0, x (idxE K K' e 0 s) = 0 := apply_idxE_eq_zero_of_fMap_eq_zero π M K K' e hU 0 x hf
  funext t
  rcases idx_cases_zero K K' e j₀ hj₀ t with ⟨s, rfl⟩ | rfl
  · exact hE s
  ·
    refine TopCat.Sheaf.eq_of_locally_eq' (Msh M) (fun i => K'.inter (snocIdx K K' e j₀ hlt 0 (sing K i)))
      (K'.inter (vtx K' j₀)) (fun i => homOfLE (cov_le K K' e hU j₀ hlt i)) (le_iSup_cov K K' e hU j₀ hlt)
      (x (vtx K' j₀)) 0 fun i => ?_
    rw [map_zero]

    have h := congrFun hd (snocIdx K K' e j₀ hlt 0 (sing K i))
    rw [OModulePresheaf.d_apply, Pi.zero_apply, Fin.sum_univ_two] at h
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul] at h
    rw [cochain_congr π M x (face_snocIdx_one K K' e j₀ hlt (sing K i)) _
        ((K'.inter_le_inter_face _ 1).trans (le_of_eq (congrArg K'.inter (face_snocIdx_one K K' e j₀ hlt (sing K i))))),
      hE, map_zero, neg_zero, add_zero,
      cochain_congr π M x (face_snocIdx_zero K K' e j₀ hlt (sing K i)) _ (cov_le K K' e hU j₀ hlt i)] at h
    exact h

def pairIdx {i i' : K.ι} (h : i < i') : K.Idx 1 :=
  ⟨![i, i'], Fin.strictMono_iff_lt_succ.mpr fun k => by rw [fin_one_eq k 0]; exact h⟩

theorem face_pairIdx_zero {i i' : K.ι} (h : i < i') : K.face (pairIdx K h) 0 = sing K i' :=
  Subtype.ext (funext fun k => by rw [fin_one_eq k 0]; rfl)

theorem face_pairIdx_one {i i' : K.ι} (h : i < i') : K.face (pairIdx K h) 1 = sing K i := by
  apply Subtype.ext; funext k
  rw [fin_one_eq k 0]
  show (![i, i'] : Fin 2 → K.ι) (Fin.succAbove 1 0) = i
  rw [Fin.succAbove_ne_zero_zero (ne_of_gt Fin.zero_lt_one)]
  rfl

include hU in

theorem inf_cov_le_inter_pair {i i' : K.ι} (h : i < i') :
    K'.inter (snocIdx K K' e j₀ hlt 0 (sing K i)) ⊓ K'.inter (snocIdx K K' e j₀ hlt 0 (sing K i')) ≤
      K'.inter (snocIdx K K' e j₀ hlt 1 (pairIdx K h)) := by
  rw [inter_snocIdx K K' e j₀ hlt hU, inter_snocIdx K K' e j₀ hlt hU, inter_snocIdx K K' e j₀ hlt hU]
  refine le_inf (inf_le_left.trans inf_le_left) (le_iInf fun k => ?_)
  show _ ≤ K.U ((![i, i'] : Fin 2 → K.ι) k)
  fin_cases k
  · exact inf_le_left.trans (inf_le_right.trans (iInf_le _ 0))
  · exact inf_le_right.trans (inf_le_right.trans (iInf_le _ 0))

theorem face_pair_zero {i i' : K.ι} (h : i < i') :
    K'.face (snocIdx K K' e j₀ hlt 1 (pairIdx K h)) 0 = snocIdx K K' e j₀ hlt 0 (sing K i') :=
  (face_snocIdx_castSucc K K' e j₀ hlt (pairIdx K h) 0).trans (congrArg _ (face_pairIdx_zero K h))

theorem face_pair_one {i i' : K.ι} (h : i < i') :
    K'.face (snocIdx K K' e j₀ hlt 1 (pairIdx K h)) 1 = snocIdx K K' e j₀ hlt 0 (sing K i) :=
  (face_snocIdx_castSucc K K' e j₀ hlt (pairIdx K h) 1).trans (congrArg _ (face_pairIdx_one K h))

theorem face_pair_two {i i' : K.ι} (h : i < i') :
    K'.face (snocIdx K K' e j₀ hlt 1 (pairIdx K h)) 2 = idxE K K' e 1 (pairIdx K h) :=
  face_snocIdx_last K K' e j₀ hlt (pairIdx K h)

include hj₀ hlt hU in

theorem res_pair_eq (x : (𝓕).cochain K' 1) (hE : ∀ s : K.Idx 1, x (idxE K K' e 1 s) = 0)
    (hd : (𝓕).d K' 1 x = 0) {i i' : K.ι} (h : i < i') :
    (𝓕).res ((K'.inter_le_inter_face _ 0).trans (le_of_eq (congrArg K'.inter (face_pair_zero K K' e j₀ hlt h))))
      (x (snocIdx K K' e j₀ hlt 0 (sing K i'))) =
    (𝓕).res ((K'.inter_le_inter_face _ 1).trans (le_of_eq (congrArg K'.inter (face_pair_one K K' e j₀ hlt h))))
      (x (snocIdx K K' e j₀ hlt 0 (sing K i))) := by
  have hc := congrFun hd (snocIdx K K' e j₀ hlt 1 (pairIdx K h))
  rw [OModulePresheaf.d_apply, Pi.zero_apply, Fin.sum_univ_three] at hc
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, Fin.val_two, neg_one_sq] at hc
  rw [cochain_congr π M x (face_pair_two K K' e j₀ hlt h) _
      ((K'.inter_le_inter_face _ 2).trans (le_of_eq (congrArg K'.inter (face_pair_two K K' e j₀ hlt h)))),
    hE, map_zero, add_zero, ← sub_eq_add_neg, sub_eq_zero,
    cochain_congr π M x (face_pair_zero K K' e j₀ hlt h) _
      ((K'.inter_le_inter_face _ 0).trans (le_of_eq (congrArg K'.inter (face_pair_zero K K' e j₀ hlt h)))),
    cochain_congr π M x (face_pair_one K K' e j₀ hlt h) _
      ((K'.inter_le_inter_face _ 1).trans (le_of_eq (congrArg K'.inter (face_pair_one K K' e j₀ hlt h))))] at hc
  exact hc

include hj₀ hlt hU in

theorem hexS_zero (x : (𝓕).cochain K' 1) (hf : fMap π M K K' e hU 1 x = 0) (hd : (𝓕).d K' 1 x = 0) :
    ∃ y : (𝓕).cochain K' 0, fMap π M K K' e hU 0 y = 0 ∧ (𝓕).d K' 0 y = x := by
  have hE : ∀ s : K.Idx 1, x (idxE K K' e 1 s) = 0 := apply_idxE_eq_zero_of_fMap_eq_zero π M K K' e hU 1 x hf

  let Uc : K.ι → V.Opens := fun i => K'.inter (snocIdx K K' e j₀ hlt 0 (sing K i))
  let sf : ∀ i, Γ(M, Uc i) := fun i => x (snocIdx K K' e j₀ hlt 0 (sing K i))
  have hcompat : TopCat.Presheaf.IsCompatible (Msh M).1 Uc sf := by
    intro i i'
    rcases lt_trichotomy i i' with h | rfl | h
    · have key := congrArg ((𝓕).res (inf_cov_le_inter_pair K K' e hU j₀ hlt h)) (res_pair_eq π M K K' e hU j₀ hj₀ hlt x hE hd h)
      rw [(𝓕).res_res, (𝓕).res_res] at key
      exact key.symm
    · rfl
    · have key := congrArg ((𝓕).res ((le_of_eq (inf_comm _ _)).trans (inf_cov_le_inter_pair K K' e hU j₀ hlt h)))
        (res_pair_eq π M K K' e hU j₀ hj₀ hlt x hE hd h)
      rw [(𝓕).res_res, (𝓕).res_res] at key
      exact key
  obtain ⟨y₀, hy₀, -⟩ := (Msh M).existsUnique_gluing' Uc (K'.inter (vtx K' j₀))
    (fun i => homOfLE (cov_le K K' e hU j₀ hlt i)) (le_iSup_cov K K' e hU j₀ hlt) sf hcompat

  let y : (𝓕).cochain K' 0 := fun t =>
    if h : t = vtx K' j₀ then (𝓕).res (le_of_eq (congrArg K'.inter h)) y₀ else 0
  have hyE : ∀ s : K.Idx 0, y (idxE K K' e 0 s) = 0 := fun s => dif_neg (idxE_ne_vtx K K' e j₀ hlt s)
  refine ⟨y, funext fun s => ?_, funext fun t => ?_⟩
  · rw [fMap_apply, hyE, map_zero]; rfl
  · rcases idx_cases K K' e j₀ hj₀ hlt t with ⟨s, rfl⟩ | ⟨s, rfl⟩
    ·
      rw [hE, OModulePresheaf.d_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [show y (K'.face (idxE K K' e (0 + 1) s) j) = 0 from hyE (K.face s j), map_zero, smul_zero]
    · obtain ⟨i, rfl⟩ : ∃ i, s = sing K i := ⟨_, eq_sing K s⟩
      rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
      simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul]
      have h1 : y (K'.face (snocIdx K K' e j₀ hlt 0 (sing K i)) 1) = 0 := by
        rw [face_snocIdx_one]; exact hyE _
      have h0 : y (K'.face (snocIdx K K' e j₀ hlt 0 (sing K i)) 0) =
          (𝓕).res (le_of_eq (congrArg K'.inter (face_snocIdx_zero K K' e j₀ hlt (sing K i)))) y₀ :=
        dif_pos (face_snocIdx_zero K K' e j₀ hlt (sing K i))
      rw [h1, map_zero, neg_zero, add_zero, h0, (𝓕).res_res]
      exact hy₀ i

section Higher

variable (m : ℕ)

abbrev U₀ : V.Opens := K'.U j₀

abbrev KU : (U₀ K' j₀ : Scheme.{u}).OrderedAffineCover := coverOn π K (U₀ K' j₀) (K'.isAffineOpen j₀)

abbrev G : OModulePresheaf ((U₀ K' j₀).ι ≫ π) := restrictOpen (𝓕) (U₀ K' j₀)

include hU in

theorem eqA {n : ℕ} (s : K.Idx n) :
    (U₀ K' j₀).ι ''ᵁ ((KU π K K' j₀).inter s) = K'.inter (snocIdx K K' e j₀ hlt n s) :=
  (image_inter π K (U₀ K' j₀) (K'.isAffineOpen j₀) s).trans (inter_snocIdx K K' e j₀ hlt hU s).symm

include hj₀ hlt hU hq in

theorem hexS_succ (x : (𝓕).cochain K' (m + 2)) (hf : fMap π M K K' e hU (m + 2) x = 0)
    (hd : (𝓕).d K' (m + 2) x = 0) :
    ∃ y : (𝓕).cochain K' (m + 1), fMap π M K K' e hU (m + 1) y = 0 ∧ (𝓕).d K' (m + 1) y = x := by
  have hE : ∀ s : K.Idx (m + 2), x (idxE K K' e (m + 2) s) = 0 :=
    apply_idxE_eq_zero_of_fMap_eq_zero π M K K' e hU (m + 2) x hf

  let xt : (G π M K' j₀).cochain (KU π K K' j₀) (m + 1) := fun s =>
    (𝓕).res (le_of_eq (eqA π K K' e hU j₀ hlt s)) (x (snocIdx K K' e j₀ hlt (m + 1) s))

  have hxt : (G π M K' j₀).d (KU π K K' j₀) (m + 1) xt = 0 := by
    funext s'
    have hc := congrFun hd (snocIdx K K' e j₀ hlt (m + 2) s')
    rw [OModulePresheaf.d_apply, Pi.zero_apply, Fin.sum_univ_castSucc,
      cochain_congr π M x (face_snocIdx_last K K' e j₀ hlt s') _
        ((K'.inter_le_inter_face _ (Fin.last _)).trans (le_of_eq (congrArg K'.inter (face_snocIdx_last K K' e j₀ hlt s')))),
      hE, map_zero, smul_zero, add_zero] at hc
    have hc' := congrArg ((𝓕).res (le_of_eq (eqA π K K' e hU j₀ hlt s'))) hc
    rw [map_zero, map_sum] at hc'
    rw [OModulePresheaf.d_apply]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hc'
    rw [LinearMap.map_smul_of_tower, Fin.val_castSucc,
      cochain_congr π M x (face_snocIdx_castSucc K K' e j₀ hlt s' j) _
        ((K'.inter_le_inter_face _ (Fin.castSucc j)).trans
          (le_of_eq (congrArg K'.inter (face_snocIdx_castSucc K K' e j₀ hlt s' j)))),
      (𝓕).res_res]
    show _ • (𝓕).res _ ((𝓕).res _ (x (snocIdx K K' e j₀ hlt (m + 1) (K.face s' j)))) = _
    rw [(𝓕).res_res]
    rfl

  haveI := subsingleton_HSucc_restrictOpen π (𝓕) K (U₀ K' j₀) (K'.isAffineOpen j₀) hq m
  obtain ⟨yt, hyt⟩ := exists_d_eq_of_subsingleton_HSucc (G π M K' j₀) (KU π K K' j₀) m xt hxt

  let y : (𝓕).cochain K' (m + 1) := fun t =>
    if h : ∃ s, t = snocIdx K K' e j₀ hlt m s then
      (𝓕).res (le_of_eq ((congrArg K'.inter h.choose_spec).trans (eqA π K K' e hU j₀ hlt h.choose).symm))
        (yt h.choose)
    else 0
  have hyE : ∀ s : K.Idx (m + 1), y (idxE K K' e (m + 1) s) = 0 := fun s =>
    dif_neg fun ⟨s', hs'⟩ => idxE_ne_snocIdx K K' e j₀ hlt s s' hs'
  have hyS : ∀ (s : K.Idx m) (A : V.Opens) (h : A ≤ K'.inter (snocIdx K K' e j₀ hlt m s))
      (h' : A ≤ (U₀ K' j₀).ι ''ᵁ ((KU π K K' j₀).inter s)),
      (𝓕).res h (y (snocIdx K K' e j₀ hlt m s)) = (𝓕).res h' (yt s) := by
    intro s A h h'
    have hex : ∃ s', snocIdx K K' e j₀ hlt m s = snocIdx K K' e j₀ hlt m s' := ⟨s, rfl⟩
    have hs : hex.choose = s := (snocIdx_injective K K' e j₀ hlt m hex.choose_spec).symm
    have hy : y (snocIdx K K' e j₀ hlt m s) =
        (𝓕).res (le_of_eq ((congrArg K'.inter hex.choose_spec).trans (eqA π K K' e hU j₀ hlt hex.choose).symm))
          (yt hex.choose) := dif_pos hex
    rw [hy, (𝓕).res_res]
    exact res_dcongr π M (fun s => (U₀ K' j₀).ι ''ᵁ ((KU π K K' j₀).inter s)) yt hs _ _
  refine ⟨y, funext fun s => ?_, funext fun t => ?_⟩
  · rw [fMap_apply, hyE, map_zero]; rfl
  · rcases idx_cases K K' e j₀ hj₀ hlt t with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · rw [hE, OModulePresheaf.d_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [show y (K'.face (idxE K K' e (m + 2) s) j) = 0 from hyE (K.face s j), map_zero, smul_zero]
    ·
      have hx : x (snocIdx K K' e j₀ hlt (m + 1) s) = (𝓕).res (le_of_eq (eqA π K K' e hU j₀ hlt s).symm) (xt s) := by
        show _ = (𝓕).res _ ((𝓕).res _ _)
        rw [(𝓕).res_res, (𝓕).res_refl_apply]
      rw [hx, ← hyt, OModulePresheaf.d_apply, OModulePresheaf.d_apply]
      refine Eq.trans ?_ (map_sum ((𝓕).res (le_of_eq (eqA π K K' e hU j₀ hlt s).symm)) _ _).symm
      rw [Fin.sum_univ_castSucc,
        show y (K'.face (snocIdx K K' e j₀ hlt (m + 1) s) (Fin.last _)) = 0 by
          rw [face_snocIdx_last]; exact hyE s,
        map_zero, smul_zero, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Fin.val_castSucc,
        cochain_congr π M y (face_snocIdx_castSucc K K' e j₀ hlt s j) _
          ((K'.inter_le_inter_face _ (Fin.castSucc j)).trans
            (le_of_eq (congrArg K'.inter (face_snocIdx_castSucc K K' e j₀ hlt s j)))),
        hyS (K.face s j) _ _ (((K'.inter_le_inter_face _ (Fin.castSucc j)).trans
            (le_of_eq (congrArg K'.inter (face_snocIdx_castSucc K K' e j₀ hlt s j)))).trans
          (le_of_eq (eqA π K K' e hU j₀ hlt (K.face s j)).symm))]
      exact (res_zsmul_res π M _ _ ((-1 : ℤ) ^ (j : ℕ)) (yt (K.face s j))).symm

end Higher

include hj₀ hlt hU hq in
theorem main :
    Nonempty ((𝓕).H0 K' ≃ₗ[R] (𝓕).H0 K) ∧ ∀ i : ℕ, Nonempty ((𝓕).HSucc K' i ≃ₗ[R] (𝓕).HSucc K i) := by
  have key := LinearMap.exists_ker_linearEquiv_and_quotient_linearEquiv_of_surjective_of_forall_exact
    (R := R) (C := fun n => (𝓕).cochain K' n) (D := fun n => (𝓕).cochain K n)
    (fun n => (𝓕).d K' n) (fun n => (𝓕).d K n) (fun n => fMap π M K K' e hU n)
    (fun n x => (d_fMap π M K K' e hU n x).symm)
    (fun n x => by
      have := LinearMap.congr_fun ((𝓕).d_comp_d K' n) x
      exact this)
    (fun n => fMap_surjective π M K K' e hU n)
    (fun x hfx hdx => hex0 π M K K' e hU j₀ hj₀ hlt x hfx hdx)
    (fun n => by
      cases n with
      | zero => exact fun x hfx hdx => hexS_zero π M K K' e hU j₀ hj₀ hlt x hfx hdx
      | succ m => exact fun x hfx hdx => hexS_succ π M hq K K' e hU j₀ hj₀ hlt m x hfx hdx)
  obtain ⟨⟨e0, -⟩, hS⟩ := key
  exact ⟨⟨e0⟩, fun i => by obtain ⟨eS, -⟩ := hS i; exact ⟨eS⟩⟩

end Main

end P2mAdjoinChart

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
    (M : V.Modules) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (K K' : V.OrderedAffineCover) (e : K.ι ↪o K'.ι) (hU : ∀ i, K'.U (e i) = K.U i)
    (j₀ : K'.ι) (hj₀ : ∀ j : K'.ι, j = j₀ ∨ j ∈ Set.range e) (hlt : ∀ i, e i < j₀) :
    Nonempty ((OModulePresheaf.ofModules π M).H0 K' ≃ₗ[R] (OModulePresheaf.ofModules π M).H0 K) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules π M).HSucc K' i ≃ₗ[R]
        (OModulePresheaf.ofModules π M).HSucc K i) :=
  P2mAdjoinChart.main π M hq K K' e hU j₀ hj₀ hlt

end

end S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_orderEmbedding_of_forall_lt (solution)
