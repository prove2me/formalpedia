-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
-- name    : Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:18.126829+00:00
-- url     : https://prove2.me/theorems/59ef7459-4428-4b9e-94a6-2b13115f5d05
-- title:
--   Is Iso Term Comparison Restrict Scalars
-- statement:
--   Definitions and structural lemmas for Is Iso Term Comparison Restrict Scalars, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
namespace GlobalTheory
abbrev Cube (ι : Type) (R : Type u) [Ring R] : Type _ := Finset ι ⥤ ModuleCat.{v} R
section Sign
variable {ι : Type} [LinearOrder ι]
def cubeSign (t : Finset ι) (i : ι) : ℤ := (-1) ^ (t.filter (· < i)).card
@[simp]
theorem cubeSign_mul_self (t : Finset ι) (i : ι) : cubeSign t i * cubeSign t i = 1 := by
  rw [cubeSign, ← mul_pow]; simp
@[simp]
theorem cubeSign_smul_smul {M : Type*} [AddCommGroup M] (t : Finset ι) (i : ι) (x : M) :
    cubeSign t i • cubeSign t i • x = x := by
  rw [smul_smul, cubeSign_mul_self, one_smul]
@[simp]
theorem cubeSign_smul_eq_zero {M : Type*} [AddCommGroup M] (t : Finset ι) (i : ι) (x : M) :
    cubeSign t i • x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← cubeSign_smul_smul t i x, h, smul_zero], fun h => by rw [h, smul_zero]⟩
theorem cubeSign_eq_one_of_forall_le {t : Finset ι} {i : ι} (h : ∀ j ∈ t, i ≤ j) :
    cubeSign t i = 1 := by
  rw [cubeSign, Finset.filter_eq_empty_iff.2 (fun j hj => not_lt.2 (h j hj))]; simp
@[simp]
theorem cubeSign_singleton (i : ι) : cubeSign {i} i = 1 :=
  cubeSign_eq_one_of_forall_le (by simp)
theorem cubeSign_erase_of_le (t : Finset ι) {i j : ι} (h : i ≤ j) :
    cubeSign (t.erase j) i = cubeSign t i := by
  unfold cubeSign
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp [h]
theorem cubeSign_erase_of_lt {t : Finset ι} {i j : ι} (hj : j ∈ t) (h : j < i) :
    cubeSign (t.erase j) i = - cubeSign t i := by
  unfold cubeSign
  rw [Finset.filter_erase,
    ← Finset.card_erase_add_one (s := t.filter (· < i)) (a := j) (by simp [hj, h]), pow_succ]
  ring
theorem cubeSign_mul_erase {t : Finset ι} {i j : ι} (hi : i ∈ t) (hj : j ∈ t) (h : i ≠ j) :
    cubeSign t i * cubeSign (t.erase i) j = - (cubeSign t j * cubeSign (t.erase j) i) := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [cubeSign_erase_of_lt hi h, cubeSign_erase_of_le t h.le]; ring
  · rw [cubeSign_erase_of_lt hj h, cubeSign_erase_of_le t h.le]; ring
end Sign
namespace Cube
section Basic
variable {ι : Type} {R : Type u} [Ring R]
def res (A : Cube.{v} ι R) {s t : Finset ι} (h : s ⊆ t) : A.obj s →ₗ[R] A.obj t :=
  (A.map (homOfLE h)).hom
@[simp]
theorem res_self (A : Cube.{v} ι R) {s : Finset ι} (h : s ⊆ s) (x : A.obj s) :
    res A h x = x := by
  have : (homOfLE h : s ⟶ s) = 𝟙 s := rfl
  simp [res, this]
@[simp]
theorem res_res (A : Cube.{v} ι R) {s t w : Finset ι} (h : s ⊆ t) (h' : t ⊆ w) (x : A.obj s) :
    res A h' (res A h x) = res A (h.trans h') x := by
  have : (homOfLE (h.trans h') : s ⟶ w) = homOfLE h ≫ homOfLE h' := rfl
  simp only [res, this, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
theorem res_congr (A : Cube.{v} ι R) (x : ∀ s, A.obj s) {s s' t : Finset ι} (e : s = s')
    (h : s ⊆ t) (h' : s' ⊆ t) : res A h (x s) = res A h' (x s') := by
  subst e; rfl
theorem app_res {A B : Cube.{v} ι R} (φ : A ⟶ B) {s t : Finset ι} (h : s ⊆ t) (x : A.obj s) :
    (φ.app t).hom (res A h x) = res B h ((φ.app s).hom x) :=
  congr(($(φ.naturality (homOfLE h))).hom x)
@[simps obj]
def mk (X : Finset ι → ModuleCat.{v} R) (ρ : ∀ {s t : Finset ι}, s ⊆ t → X s →ₗ[R] X t)
    (ρ_self : ∀ (s : Finset ι) (x : X s), ρ (subset_refl s) x = x)
    (ρ_comp : ∀ {s t w : Finset ι} (h : s ⊆ t) (h' : t ⊆ w) (x : X s),
      ρ h' (ρ h x) = ρ (h.trans h') x) : Cube.{v} ι R where
  obj := X
  map f := ModuleCat.ofHom (ρ (leOfHom f))
  map_id s := ModuleCat.hom_ext (LinearMap.ext (ρ_self s))
  map_comp f g := ModuleCat.hom_ext (LinearMap.ext fun x => (ρ_comp (leOfHom f) (leOfHom g) x).symm)
@[simp]
theorem res_mk (X : Finset ι → ModuleCat.{v} R) (ρ : ∀ {s t : Finset ι}, s ⊆ t → X s →ₗ[R] X t)
    (ρ_self ρ_comp) {s t : Finset ι} (h : s ⊆ t) :
    res (mk X ρ ρ_self ρ_comp) h = ρ h := rfl
@[simps]
def homMk {A B : Cube.{v} ι R} (φ : ∀ s, A.obj s →ₗ[R] B.obj s)
    (hφ : ∀ {s t : Finset ι} (h : s ⊆ t) (x : A.obj s), φ t (res A h x) = res B h (φ s x)) :
    A ⟶ B where
  app s := ModuleCat.ofHom (φ s)
  naturality _ _ f := ModuleCat.hom_ext (LinearMap.ext (hφ (leOfHom f)))
def isoMk {A B : Cube.{v} ι R} (φ : ∀ s, A.obj s ≃ₗ[R] B.obj s)
    (hφ : ∀ {s t : Finset ι} (h : s ⊆ t) (x : A.obj s), φ t (res A h x) = res B h (φ s x)) :
    A ≅ B :=
  NatIso.ofComponents (fun s => (φ s).toModuleIso)
    (fun f => ModuleCat.hom_ext (LinearMap.ext (hφ (leOfHom f))))
abbrev const (ι : Type) (M : ModuleCat.{v} R) : Cube.{v} ι R := (Functor.const _).obj M
@[simp]
theorem res_const (M : ModuleCat.{v} R) {s t : Finset ι} (h : s ⊆ t) (x : M) :
    res (const ι M) h x = x := rfl
abbrev Term (A : Cube.{v} ι R) (p : ℕ) : Type v :=
  ∀ s : {s : Finset ι // s.card = p}, A.obj s.1
def extend (A : Cube.{v} ι R) (p : ℕ) : Term A p →ₗ[R] ∀ s, A.obj s where
  toFun x s := if h : s.card = p then x ⟨s, h⟩ else 0
  map_add' x y := by ext s; by_cases h : s.card = p <;> simp [h]
  map_smul' r x := by ext s; by_cases h : s.card = p <;> simp [h]
theorem extend_apply_of_eq (A : Cube.{v} ι R) {p : ℕ} (x : Term A p) {s : Finset ι}
    (h : s.card = p) : extend A p x s = x ⟨s, h⟩ := dif_pos h
def termMap {A B : Cube.{v} ι R} (φ : A ⟶ B) (p : ℕ) : Term A p →ₗ[R] Term B p where
  toFun x s := (φ.app s.1).hom (x s)
  map_add' x y := by ext s; simp
  map_smul' r x := by ext s; simp
@[simp]
theorem termMap_apply {A B : Cube.{v} ι R} (φ : A ⟶ B) (p : ℕ) (x : Term A p)
    (s : {s : Finset ι // s.card = p}) : termMap φ p x s = (φ.app s.1).hom (x s) := rfl
def termZeroEquiv (A : Cube.{v} ι R) : Term A 0 ≃ₗ[R] A.obj ∅ where
  toFun x := x ⟨∅, rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a s := res A (Finset.empty_subset s.1) a
  left_inv x := by
    ext ⟨s, hs⟩
    obtain rfl := Finset.card_eq_zero.1 hs
    simp
  right_inv a := by simp
@[simp]
theorem termZeroEquiv_apply (A : Cube.{v} ι R) (x : Term A 0) :
    termZeroEquiv A x = x ⟨∅, rfl⟩ := rfl
@[simp]
theorem termZeroEquiv_symm_apply (A : Cube.{v} ι R) (a : A.obj ∅)
    (s : {s : Finset ι // s.card = 0}) :
    (termZeroEquiv A).symm a s = res A (Finset.empty_subset s.1) a := rfl
noncomputable def termOneEquiv (A : Cube.{v} ι R) : (∀ i : ι, A.obj {i}) ≃ₗ[R] Term A 1 :=
  LinearEquiv.piCongrLeft R (fun s : {s : Finset ι // s.card = 1} => A.obj s.1)
    (Equiv.ofBijective (fun i : ι => (⟨{i}, Finset.card_singleton i⟩ :
        {s : Finset ι // s.card = 1}))
      ⟨fun i j h => Finset.singleton_injective (congrArg Subtype.val h), fun s => by
        obtain ⟨i, hi⟩ := Finset.card_eq_one.1 s.2
        exact ⟨i, Subtype.ext hi.symm⟩⟩)
@[simp]
theorem termOneEquiv_symm_apply (A : Cube.{v} ι R) (x : Term A 1) (i : ι) :
    (termOneEquiv A).symm x i = x ⟨{i}, Finset.card_singleton i⟩ := rfl
@[simp]
theorem termOneEquiv_apply (A : Cube.{v} ι R) (y : ∀ i : ι, A.obj {i}) (i : ι) :
    termOneEquiv A y ⟨{i}, Finset.card_singleton i⟩ = y i := by
  rw [← termOneEquiv_symm_apply A (termOneEquiv A y), LinearEquiv.symm_apply_apply]
theorem subsingleton_term [Fintype ι] (A : Cube.{v} ι R) {p : ℕ} (h : Fintype.card ι < p) :
    Subsingleton (Term A p) :=
  ⟨fun _ _ => funext fun s => absurd (s.2 ▸ Finset.card_le_univ s.1) (not_le.2 h)⟩
def aug (A : Cube.{v} ι R) : A.obj ∅ →ₗ[R] Term A 1 :=
  LinearMap.pi fun s => res A (Finset.empty_subset s.1)
@[simp]
theorem aug_apply (A : Cube.{v} ι R) (a : A.obj ∅) (s : {s : Finset ι // s.card = 1}) :
    aug A a s = res A (Finset.empty_subset s.1) a := rfl
theorem termMap_aug {A B : Cube.{v} ι R} (φ : A ⟶ B) (a : A.obj ∅) :
    termMap φ 1 (aug A a) = aug B ((φ.app ∅).hom a) := by
  ext s; simp [app_res]
end Basic
section Differential
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
abbrev eraseIdx {p : ℕ} (t : {s : Finset ι // s.card = p + 1}) (i : t.1) :
    {s : Finset ι // s.card = p} :=
  ⟨t.1.erase i.1, by rw [Finset.card_erase_of_mem i.2, t.2]; rfl⟩
def d (A : Cube.{v} ι R) (p : ℕ) : Term A p →ₗ[R] Term A (p + 1) :=
  LinearMap.pi fun t => ∑ i : t.1, cubeSign t.1 i.1 •
    (res A (Finset.erase_subset i.1 t.1) ∘ₗ LinearMap.proj (eraseIdx t i))
theorem d_apply (A : Cube.{v} ι R) (p : ℕ) (x : Term A p) (t : {s : Finset ι // s.card = p + 1}) :
    d A p x t = ∑ i : t.1, cubeSign t.1 i.1 •
      res A (Finset.erase_subset i.1 t.1) (x (eraseIdx t i)) := by
  simp [d, LinearMap.sum_apply]
def totalD (A : Cube.{v} ι R) : (∀ s, A.obj s) →ₗ[R] ∀ s, A.obj s :=
  LinearMap.pi fun t => ∑ i ∈ t, cubeSign t i •
    (res A (Finset.erase_subset i t) ∘ₗ LinearMap.proj (t.erase i))
theorem totalD_apply (A : Cube.{v} ι R) (x : ∀ s, A.obj s) (t : Finset ι) :
    totalD A x t = ∑ i ∈ t, cubeSign t i • res A (Finset.erase_subset i t) (x (t.erase i)) := by
  simp [totalD, LinearMap.sum_apply]
theorem d_apply_eq_totalD (A : Cube.{v} ι R) {p : ℕ} (x : Term A p) (y : ∀ s, A.obj s)
    (h : ∀ s : {s : Finset ι // s.card = p}, x s = y s.1) (t : {s : Finset ι // s.card = p + 1}) :
    d A p x t = totalD A y t.1 := by
  rw [d_apply, totalD_apply, ← Finset.sum_coe_sort t.1]
  exact Finset.sum_congr rfl fun i _ => by rw [h]
theorem d_apply_extend (A : Cube.{v} ι R) {p : ℕ} (x : Term A p)
    (t : {s : Finset ι // s.card = p + 1}) :
    d A p x t = ∑ i ∈ t.1, cubeSign t.1 i •
      res A (Finset.erase_subset i t.1) (extend A p x (t.1.erase i)) := by
  rw [d_apply_eq_totalD A x (extend A p x) (fun s => (extend_apply_of_eq A x s.2).symm),
    totalD_apply]
theorem totalD_totalD (A : Cube.{v} ι R) (x : ∀ s, A.obj s) : totalD A (totalD A x) = 0 := by
  funext t
  let f : ι × ι → A.obj t := fun q => (cubeSign t q.1 * cubeSign (t.erase q.1) q.2) •
    res A ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)) (x ((t.erase q.1).erase q.2))
  have h1 : totalD A (totalD A x) t = ∑ q ∈ t.offDiag, f q := by
    rw [totalD_apply, Finset.sum_finset_product t.offDiag t (fun i => t.erase i)
      (fun q => by simp only [Finset.mem_offDiag, Finset.mem_erase]; tauto)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [totalD_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [f, map_zsmul, res_res, smul_smul]
  rw [h1]
  refine Finset.sum_involution (fun q _ => q.swap) (fun q hq => ?_) (fun q hq _ h => ?_)
    (fun q hq => ?_) (fun q _ => rfl)
  · rw [Finset.mem_offDiag] at hq
    simp only [f, Prod.fst_swap, Prod.snd_swap]
    rw [cubeSign_mul_erase hq.1 hq.2.1 hq.2.2,
      res_congr A x (Finset.erase_right_comm (a := q.1) (b := q.2)) _
        ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)), neg_smul, neg_add_cancel]
  · rw [Finset.mem_offDiag] at hq
    exact hq.2.2 (congrArg Prod.snd h)
  · rw [Finset.mem_offDiag] at hq ⊢
    exact ⟨hq.2.1, hq.1, hq.2.2.symm⟩
@[simp]
theorem d_d (A : Cube.{v} ι R) (p : ℕ) (x : Term A p) : d A (p + 1) (d A p x) = 0 := by
  funext t
  rw [d_apply_eq_totalD A (d A p x) (totalD A (extend A p x)) (fun s =>
    d_apply_eq_totalD A x _ (fun s => (extend_apply_of_eq A x s.2).symm) s), totalD_totalD]
  rfl
theorem d_comp_d (A : Cube.{v} ι R) (p : ℕ) : d A (p + 1) ∘ₗ d A p = 0 :=
  LinearMap.ext (d_d A p)
theorem termMap_d {A B : Cube.{v} ι R} (φ : A ⟶ B) (p : ℕ) (x : Term A p) :
    termMap φ (p + 1) (d A p x) = d B p (termMap φ p x) := by
  funext t
  simp only [termMap_apply, d_apply, map_sum, map_zsmul, app_res]
theorem d_zero_apply (A : Cube.{v} ι R) (x : Term A 0) :
    d A 0 x = aug A (termZeroEquiv A x) := by
  obtain ⟨a, rfl⟩ := (termZeroEquiv A).symm.surjective x
  ext ⟨t, ht⟩
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 ht
  rw [d_apply_eq_totalD A ((termZeroEquiv A).symm a) (fun s => res A (Finset.empty_subset s) a)
    (fun _ => rfl), totalD_apply]
  simp
@[simp]
theorem d_aug (A : Cube.{v} ι R) (a : A.obj ∅) : d A 1 (aug A a) = 0 := by
  have := d_zero_apply A ((termZeroEquiv A).symm a)
  rw [LinearEquiv.apply_symm_apply] at this
  rw [← this]
  exact d_d A 0 _
theorem d_one_apply_pair (A : Cube.{v} ι R) (x : Term A 1) {i j : ι} (h : i < j) :
    d A 1 x ⟨{i, j}, Finset.card_pair h.ne⟩ =
      res A (by simp) (x ⟨{j}, Finset.card_singleton j⟩) -
        res A (by simp) (x ⟨{i}, Finset.card_singleton i⟩) := by
  rw [d_apply_extend, Finset.sum_pair h.ne,
    ← extend_apply_of_eq A x (Finset.card_singleton j),
    ← extend_apply_of_eq A x (Finset.card_singleton i)]
  have e1 : ({i, j} : Finset ι).erase i = {j} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun hk => hk.2.resolve_left hk.1, fun hk => ⟨hk ▸ h.ne', Or.inr hk⟩⟩
  have e2 : ({i, j} : Finset ι).erase j = {i} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨fun hk => hk.2.resolve_right hk.1, fun hk => ⟨hk ▸ h.ne, Or.inl hk⟩⟩
  have s1 : cubeSign ({i, j} : Finset ι) i = 1 :=
    cubeSign_eq_one_of_forall_le (by simp [h.le])
  have s2 : cubeSign ({i, j} : Finset ι) j = -1 := by
    have := cubeSign_erase_of_lt (t := {i, j}) (by simp) h
    rw [e1, cubeSign_singleton] at this
    omega
  rw [res_congr A _ e1 _ (by simp), res_congr A _ e2 _ (by simp)]
  simp only [s1, s2, one_smul, neg_smul, sub_eq_add_neg]
end Differential
end Cube
section Complex
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
def cubeComplex (A : Cube.{v} ι R) : CochainComplex (ModuleCat.{v} R) ℕ :=
  CochainComplex.of (fun p => ModuleCat.of R (Cube.Term A p)) (fun p => ModuleCat.ofHom (Cube.d A p))
    (fun p => ModuleCat.hom_ext (Cube.d_comp_d A p))
theorem cubeComplex_d (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComplex A).d p (p + 1) = ModuleCat.ofHom (Cube.d A p) :=
  CochainComplex.of_d (fun p => ModuleCat.of R (Cube.Term A p))
    (fun p => ModuleCat.ofHom (Cube.d A p)) p
def cubeComplexMap {A B : Cube.{v} ι R} (φ : A ⟶ B) : cubeComplex A ⟶ cubeComplex B :=
  CochainComplex.ofHom (fun p => ModuleCat.ofHom (Cube.termMap φ p)) fun p => by
    rw [cubeComplex_d, cubeComplex_d]
    exact ModuleCat.hom_ext (LinearMap.ext fun x => (Cube.termMap_d φ p x).symm)
variable (ι R) in

@[simps]
def cubeFunctor : Cube.{v} ι R ⥤ CochainComplex (ModuleCat.{v} R) ℕ where
  obj := cubeComplex
  map := cubeComplexMap
  map_id _ := rfl
  map_comp _ _ := rfl
instance cubeFunctor_additive : (cubeFunctor.{v} ι R).Additive where
  map_add := rfl
def cechComplex (A : Cube.{v} ι R) : CochainComplex (ModuleCat.{v} R) ℕ :=
  CochainComplex.truncate.obj (cubeComplex A)
theorem cechComplex_d (A : Cube.{v} ι R) (p : ℕ) :
    (cechComplex A).d p (p + 1) = ModuleCat.ofHom (Cube.d A (p + 1)) :=
  cubeComplex_d A (p + 1)
def cechComplexMap {A B : Cube.{v} ι R} (φ : A ⟶ B) : cechComplex A ⟶ cechComplex B :=
  CochainComplex.truncate.map (cubeComplexMap φ)
variable (ι R) in

@[simps]
def cechFunctor : Cube.{v} ι R ⥤ CochainComplex (ModuleCat.{v} R) ℕ where
  obj := cechComplex
  map := cechComplexMap
  map_id _ := rfl
  map_comp _ _ := rfl
instance cechFunctor_additive : (cechFunctor.{v} ι R).Additive where
  map_add := rfl
noncomputable def cechAug (A : Cube.{v} ι R) :
    (CochainComplex.single₀ (ModuleCat.{v} R)).obj (A.obj ∅) ⟶ cechComplex A :=
  (CochainComplex.fromSingle₀Equiv (cechComplex A) (A.obj ∅)).symm
    ⟨ModuleCat.ofHom (Cube.aug A), by
      rw [cechComplex_d A 0]
      exact ModuleCat.hom_ext (LinearMap.ext (Cube.d_aug A))⟩
theorem cechAug_f_zero (A : Cube.{v} ι R) : (cechAug A).f 0 = ModuleCat.ofHom (Cube.aug A) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
@[reassoc]
theorem cechAug_naturality {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    (CochainComplex.single₀ (ModuleCat.{v} R)).map (φ.app ∅) ≫ cechAug B =
      cechAug A ≫ cechComplexMap φ := by
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, cechAug_f_zero, cechAug_f_zero,
    CochainComplex.single₀_map_f_zero]
  exact ModuleCat.hom_ext (LinearMap.ext fun a => (Cube.termMap_aug φ a).symm)
variable (ι R) in

@[simps]
noncomputable def cechAugNatTrans :
    (evaluation _ _).obj (∅ : Finset ι) ⋙ CochainComplex.single₀ (ModuleCat.{v} R) ⟶
      cechFunctor.{v} ι R where
  app := cechAug
  naturality _ _ φ := cechAug_naturality φ
theorem cochainComplex_exactAt_zero_iff (K : CochainComplex (ModuleCat.{v} R) ℕ) :
    K.ExactAt 0 ↔ Function.Injective (K.d 0 1).hom := by
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp),
    ShortComplex.exact_iff_mono _ (K.shape 0 0 (by simp)), ModuleCat.mono_iff_injective]
  rfl
theorem cubeComplex_exactAt_zero_iff' (A : Cube.{v} ι R) :
    (cubeComplex A).ExactAt 0 ↔ Function.Injective (Cube.d A 0) := by
  rw [cochainComplex_exactAt_zero_iff, cubeComplex_d A 0]
  rfl
theorem cubeComplex_exactAt_zero_iff (A : Cube.{v} ι R) :
    (cubeComplex A).ExactAt 0 ↔ Function.Injective (Cube.aug A) := by
  rw [cubeComplex_exactAt_zero_iff', ← Function.Injective.of_comp_iff' _ (Cube.termZeroEquiv A).bijective]
  exact Iff.of_eq (congrArg _ (funext (Cube.d_zero_apply A)))
noncomputable def cochainCyclesIsoKer (K : CochainComplex (ModuleCat.{v} R) ℕ) (p : ℕ)
    (f : K.X p →ₗ[R] K.X (p + 1)) (hf : K.d p (p + 1) = ModuleCat.ofHom f) :
    K.cycles p ≅ ModuleCat.of R (LinearMap.ker f) :=
  IsLimit.conePointUniqueUpToIso (K.cyclesIsKernel p (p + 1) (by simp))
      (ModuleCat.kernelIsLimit _) ≪≫
    (LinearEquiv.ofEq _ _ (congrArg (fun f => LinearMap.ker f.hom) hf)).toModuleIso
noncomputable def cubeCyclesIso (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComplex A).cycles p ≅ ModuleCat.of R (LinearMap.ker (Cube.d A p)) :=
  cochainCyclesIsoKer (cubeComplex A) p (Cube.d A p) (cubeComplex_d A p)
noncomputable def cechCyclesIso (A : Cube.{v} ι R) (p : ℕ) :
    (cechComplex A).cycles p ≅ ModuleCat.of R (LinearMap.ker (Cube.d A (p + 1))) :=
  cochainCyclesIsoKer (cechComplex A) p (Cube.d A (p + 1)) (cechComplex_d A p)
noncomputable def cechHomologyZeroIso (A : Cube.{v} ι R) :
    (cechComplex A).homology 0 ≅ ModuleCat.of R (LinearMap.ker (Cube.d A 1)) :=
  (CochainComplex.isoHomologyπ₀ _).symm ≪≫ cechCyclesIso A 0
@[reassoc]
theorem homologyπ_cechHomologyZeroIso_hom (A : Cube.{v} ι R) :
    (cechComplex A).homologyπ 0 ≫ (cechHomologyZeroIso A).hom = (cechCyclesIso A 0).hom :=
  (CochainComplex.isoHomologyπ₀ (cechComplex A)).hom_inv_id_assoc _
end Complex
section Linear
variable {ι : Type} [LinearOrder ι] {R : Type u} [CommRing R]
instance cubeFunctor_linear : (cubeFunctor.{v} ι R).Linear R where
  map_smul _ _ := rfl
instance cechFunctor_linear : (cechFunctor.{v} ι R).Linear R where
  map_smul _ _ := rfl
end Linear
section ChangeOfRings
variable {ι : Type} {R : Type u} [Ring R] {S : Type u'} [Ring S]
  (F : ModuleCat.{v} R ⥤ ModuleCat.{v'} S)
abbrev Cube.termProj (A : Cube.{v} ι R) {p : ℕ} (s : {s : Finset ι // s.card = p}) :
    ModuleCat.of R (Cube.Term A p) ⟶ A.obj s.1 :=
  ModuleCat.ofHom (LinearMap.proj s)
def Cube.termComparison (A : Cube.{v} ι R) (p : ℕ) :
    F.obj (ModuleCat.of R (Cube.Term A p)) ⟶ ModuleCat.of S (Cube.Term (A ⋙ F) p) :=
  ModuleCat.ofHom (LinearMap.pi fun s => (F.map (Cube.termProj A s)).hom)
theorem Cube.termComparison_apply (A : Cube.{v} ι R) (p : ℕ)
    (x : F.obj (ModuleCat.of R (Cube.Term A p))) (s : {s : Finset ι // s.card = p}) :
    (Cube.termComparison F A p).hom x s = (F.map (Cube.termProj A s)).hom x := rfl
instance Cube.isIso_termComparison [Finite ι] [F.Additive] (A : Cube.{v} ι R) (p : ℕ) :
    IsIso (Cube.termComparison F A p) := by
  classical
  have := Fintype.ofFinite {s : Finset ι // s.card = p}
  let e (s : {s : Finset ι // s.card = p}) : A.obj s.1 ⟶ ModuleCat.of R (Cube.Term A p) :=
    ModuleCat.ofHom (LinearMap.single R (fun s : {s : Finset ι // s.card = p} => A.obj s.1) s)
  have h1 : ∑ s, Cube.termProj A s ≫ e s = 𝟙 _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    rw [ModuleCat.hom_sum, LinearMap.sum_apply]
    exact Finset.univ_sum_single x
  have h2 (s) : e s ≫ Cube.termProj A s = 𝟙 _ :=
    ModuleCat.hom_ext (LinearMap.ext fun x => Pi.single_eq_same
      (M := fun s : {s : Finset ι // s.card = p} => A.obj s.1) s x)
  have h3 (s t) (h : t ≠ s) : e s ≫ Cube.termProj A t = 0 :=
    ModuleCat.hom_ext (LinearMap.ext fun x => Pi.single_eq_of_ne
      (M := fun s : {s : Finset ι // s.card = p} => A.obj s.1) h x)
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (Cube.termComparison F A p).hom
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h : (F.map (∑ s, Cube.termProj A s ≫ e s)).hom x = x := by rw [h1, F.map_id]; rfl
    rw [← h, F.map_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hs : (F.map (Cube.termProj A s)).hom x = 0 := congrFun hx s
    rw [F.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hs, map_zero]
  · intro y
    refine ⟨∑ s, (F.map (e s)).hom (y s), funext fun t => ?_⟩
    rw [Cube.termComparison_apply, map_sum, Finset.sum_eq_single t]
    · rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← F.map_comp, h2, F.map_id]; rfl
    · intro s _ hs
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← F.map_comp, h3 _ _ hs.symm, F.map_zero]
      rfl
    · simp
@[reassoc]
theorem Cube.termComparison_naturality {A B : Cube.{v} ι R} (φ : A ⟶ B) (p : ℕ) :
    F.map (ModuleCat.ofHom (Cube.termMap φ p)) ≫ Cube.termComparison F B p =
      Cube.termComparison F A p ≫
        ModuleCat.ofHom (Cube.termMap (Functor.whiskerRight φ F) p) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun s => ?_)
  have h : ModuleCat.ofHom (Cube.termMap φ p) ≫ Cube.termProj B s =
    Cube.termProj A s ≫ φ.app s.1 := rfl
  have h' := congrArg F.map h
  rw [F.map_comp, F.map_comp] at h'
  exact congr(($h').hom x)
@[reassoc]
theorem Cube.map_aug_termComparison (A : Cube.{v} ι R) :
    F.map (ModuleCat.ofHom (Cube.aug A)) ≫ Cube.termComparison F A 1 =
      ModuleCat.ofHom (Cube.aug (A ⋙ F)) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun s => ?_)
  have h := (F.map_comp (ModuleCat.ofHom (Cube.aug A)) (Cube.termProj A s)).symm
  exact congr(($h).hom x)
variable [LinearOrder ι] [F.Additive]
theorem Cube.d_termProj (A : Cube.{v} ι R) (p : ℕ) (t : {s : Finset ι // s.card = p + 1}) :
    ModuleCat.ofHom (Cube.d A p) ≫ Cube.termProj A t = ∑ i : t.1, cubeSign t.1 i.1 •
      (Cube.termProj A (Cube.eraseIdx t i) ≫ A.map (homOfLE (Finset.erase_subset i.1 t.1))) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  exact Cube.d_apply A p x t
@[reassoc]
theorem Cube.map_d_termComparison (A : Cube.{v} ι R) (p : ℕ) :
    F.map (ModuleCat.ofHom (Cube.d A p)) ≫ Cube.termComparison F A (p + 1) =
      Cube.termComparison F A p ≫ ModuleCat.ofHom (Cube.d (A ⋙ F) p) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun t => ?_)
  have h := congrArg F.map (Cube.d_termProj A p t)
  rw [F.map_comp, F.map_sum] at h
  refine Eq.trans congr(($h).hom x) (Eq.trans ?_ (Cube.d_apply (A ⋙ F) p _ t).symm)
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [F.map_zsmul, F.map_comp]
  rfl
def cubeComparison (A : Cube.{v} ι R) :
    (F.mapHomologicalComplex _).obj (cubeComplex A) ⟶ cubeComplex (A ⋙ F) :=
  CochainComplex.ofHom (fun p => Cube.termComparison F A p) fun p => by
    rw [Functor.mapHomologicalComplex_obj_d, cubeComplex_d, cubeComplex_d]
    exact (Cube.map_d_termComparison F A p).symm
def cechComparison (A : Cube.{v} ι R) :
    (F.mapHomologicalComplex _).obj (cechComplex A) ⟶ cechComplex (A ⋙ F) :=
  CochainComplex.truncate.map (cubeComparison F A)
instance isIso_cubeComparison [Finite ι] (A : Cube.{v} ι R) : IsIso (cubeComparison F A) :=
  haveI : ∀ p, IsIso ((cubeComparison F A).f p) := Cube.isIso_termComparison F A
  HomologicalComplex.Hom.isIso_of_components _
instance isIso_cechComparison [Finite ι] (A : Cube.{v} ι R) : IsIso (cechComparison F A) :=
  haveI : ∀ p, IsIso ((cechComparison F A).f p) := fun p => Cube.isIso_termComparison F A (p + 1)
  HomologicalComplex.Hom.isIso_of_components _
variable (ι) in

noncomputable def cubeFunctorCompIso [Finite ι] :
    cubeFunctor.{v} ι R ⋙ F.mapHomologicalComplex _ ≅
      (Functor.whiskeringRight _ _ _).obj F ⋙ cubeFunctor.{v'} ι S :=
  NatIso.ofComponents (fun A => @asIso _ _ _ _ (cubeComparison F A) (isIso_cubeComparison F A))
    fun φ =>
    HomologicalComplex.hom_ext _ _ fun p => Cube.termComparison_naturality F φ p
variable (ι) in

noncomputable def cechFunctorCompIso [Finite ι] :
    cechFunctor.{v} ι R ⋙ F.mapHomologicalComplex _ ≅
      (Functor.whiskeringRight _ _ _).obj F ⋙ cechFunctor.{v'} ι S :=
  NatIso.ofComponents (fun A => @asIso _ _ _ _ (cechComparison F A) (isIso_cechComparison F A))
    fun φ =>
    HomologicalComplex.hom_ext _ _ fun p => Cube.termComparison_naturality F φ (p + 1)
end ChangeOfRings
section RestrictScalars
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S] (f : R →+* S)
omit [LinearOrder ι] in

theorem Cube.isIso_termComparison_restrictScalars (A : Cube.{v} ι S) (p : ℕ) :
    IsIso (Cube.termComparison (ModuleCat.restrictScalars f) A p) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact Function.bijective_id
noncomputable def cubeRestrictScalarsIso (A : Cube.{v} ι S) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj (cubeComplex A) ≅
      cubeComplex (A ⋙ ModuleCat.restrictScalars f) :=
  haveI : ∀ p, IsIso ((cubeComparison (ModuleCat.restrictScalars f) A).f p) :=
    Cube.isIso_termComparison_restrictScalars f A
  haveI := HomologicalComplex.Hom.isIso_of_components
    (cubeComparison (ModuleCat.restrictScalars f) A)
  asIso (cubeComparison _ A)
noncomputable def cechRestrictScalarsIso (A : Cube.{v} ι S) :
    ((ModuleCat.restrictScalars f).mapHomologicalComplex _).obj (cechComplex A) ≅
      cechComplex (A ⋙ ModuleCat.restrictScalars f) :=
  CochainComplex.truncate.mapIso (cubeRestrictScalarsIso f A)
end RestrictScalars
section BaseChange
open TensorProduct
variable {ι : Type} {R : Type u} [CommRing R]
instance Cube.extendScalars_additive {S : Type u'} [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, u', v} f).Additive where
  map_add {M N g h} := by
    letI := ((algebraMap S S).comp f).toAlgebra
    exact ModuleCat.hom_ext (LinearMap.baseChange_add g.hom h.hom)
noncomputable def cubeExtendScalarsIso [LinearOrder ι] [Finite ι] {S : Type u'} [CommRing S]
    (f : R →+* S) (A : Cube.{v} ι R) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex _).obj (cubeComplex A) ≅
      cubeComplex (A ⋙ ModuleCat.extendScalars f) :=
  asIso (cubeComparison _ A)
noncomputable def cechExtendScalarsIso [LinearOrder ι] [Finite ι] {S : Type u'} [CommRing S]
    (f : R →+* S) (A : Cube.{v} ι R) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex _).obj (cechComplex A) ≅
      cechComplex (A ⋙ ModuleCat.extendScalars f) :=
  asIso (cechComparison _ A)
variable (S : Type u') [CommRing S] [Algebra R S]
noncomputable def Cube.baseChange (A : Cube.{v} ι R) : Cube.{max u' v} ι S :=
  Cube.mk (fun s => ModuleCat.of S (S ⊗[R] A.obj s)) (fun h => (Cube.res A h).baseChange S)
    (fun s x => by
      have : Cube.res A (subset_refl s) = LinearMap.id := LinearMap.ext (Cube.res_self A _)
      simp [this])
    (fun h h' x => by
      have : Cube.res A (h.trans h') = Cube.res A h' ∘ₗ Cube.res A h :=
        LinearMap.ext fun y => (Cube.res_res A h h' y).symm
      simp [this, LinearMap.baseChange_comp])
noncomputable def Cube.termBaseChange (A : Cube.{v} ι R) (p : ℕ) :
    S ⊗[R] Cube.Term A p →ₗ[S] Cube.Term (Cube.baseChange S A) p :=
  TensorProduct.piRightHom R S S _
theorem Cube.termBaseChange_bijective [Finite ι] (A : Cube.{v} ι R) (p : ℕ) :
    Function.Bijective (Cube.termBaseChange S A p) := by
  classical
  have := Fintype.ofFinite {s : Finset ι // s.card = p}
  exact (TensorProduct.piRight R S S fun s : {s : Finset ι // s.card = p} => A.obj s.1).bijective
noncomputable def Cube.termBaseChangeEquiv [Finite ι] (A : Cube.{v} ι R) (p : ℕ) :
    S ⊗[R] Cube.Term A p ≃ₗ[S] Cube.Term (Cube.baseChange S A) p :=
  LinearEquiv.ofBijective _ (Cube.termBaseChange_bijective S A p)
end BaseChange
section DirectSum
open DirectSum
variable {R : Type u} [Ring R] {κ : Type} [DecidableEq κ]
theorem homology_directSum_bijective {K : κ → CochainComplex (ModuleCat.{v} R) ℕ}
    {L : CochainComplex (ModuleCat.{v} R) ℕ} (i : ∀ k, K k ⟶ L) (π : ∀ k, L ⟶ K k)
    (h₁ : ∀ k, i k ≫ π k = 𝟙 _) (h₂ : ∀ k j, k ≠ j → i k ≫ π j = 0) (p : ℕ)
    (h₃ : ∀ z : L.X p, ∃ T : Finset κ, ∑ k ∈ T, ((π k ≫ i k).f p).hom z = z) :
    Function.Bijective (DirectSum.toModule R κ (L.homology p)
      fun k => (HomologicalComplex.homologyMap (i k) p).hom) := by
  constructor
  · have key (j : κ) : (HomologicalComplex.homologyMap (π j) p).hom ∘ₗ
        (DirectSum.toModule R κ (L.homology p)
          fun k => (HomologicalComplex.homologyMap (i k) p).hom) =
        DirectSum.component R κ (fun k => (K k).homology p) j := by
      refine DirectSum.linearMap_ext _ fun k => LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, DirectSum.toModule_lof]
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← HomologicalComplex.homologyMap_comp]
      by_cases h : k = j
      · subst h
        simp [h₁]
      · simp [h₂ k j h, DirectSum.component.of, h]
    intro x y hxy
    refine DirectSum.ext_component R fun j => ?_
    rw [← key j, LinearMap.comp_apply, LinearMap.comp_apply, hxy]
  · intro x
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (L.homologyπ p)).1 inferInstance x
    obtain ⟨T, hT⟩ := h₃ ((L.iCycles p).hom c)
    have hc : (HomologicalComplex.cyclesMap (∑ k ∈ T, π k ≫ i k) p).hom c = c := by
      apply (ModuleCat.mono_iff_injective (L.iCycles p)).1 inferInstance
      have h := congr(($(HomologicalComplex.cyclesMap_i (∑ k ∈ T, π k ≫ i k) p)).hom c)
      refine h.trans (Eq.trans ?_ hT)
      have h' := (HomologicalComplex.eval _ _ p).map_sum (fun k => π k ≫ i k) T
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ← LinearMap.sum_apply, ← ModuleCat.hom_sum]
      exact congr(($h').hom _)
    refine ⟨∑ k ∈ T, DirectSum.lof R κ (fun k => (K k).homology p) k
      ((HomologicalComplex.homologyMap (π k) p).hom ((L.homologyπ p).hom c)), ?_⟩
    have h := congr(($(HomologicalComplex.homologyπ_naturality (∑ k ∈ T, π k ≫ i k) p)).hom c)
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, hc] at h
    refine Eq.trans ?_ h
    have h' := (HomologicalComplex.homologyFunctor _ _ p).map_sum (fun k => π k ≫ i k) T
    refine Eq.trans ?_ congr(($h').hom ((L.homologyπ p).hom c)).symm
    rw [map_sum, ModuleCat.hom_sum]
    refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) (LinearMap.sum_apply _ _ _).symm
    rw [DirectSum.toModule_lof, Functor.map_comp]
    rfl
variable {ι : Type}
omit [DecidableEq κ] in

noncomputable def Cube.directSum (A : κ → Cube.{v} ι R) : Cube.{v} ι R :=
  Cube.mk (fun s => ModuleCat.of R (⨁ k, (A k).obj s))
    (fun h => DirectSum.lmap fun k => Cube.res (A k) h)
    (fun s x => by ext k; simp)
    (fun h h' x => by ext k; simp)
noncomputable def Cube.directSumIncl (A : κ → Cube.{v} ι R) (k : κ) : A k ⟶ Cube.directSum A :=
  Cube.homMk (fun s => DirectSum.lof R κ (fun k => (A k).obj s) k)
    fun h x => (DirectSum.lmap_lof (fun k => Cube.res (A k) h) k x).symm
omit [DecidableEq κ] in

noncomputable def Cube.directSumProj (A : κ → Cube.{v} ι R) (k : κ) : Cube.directSum A ⟶ A k :=
  Cube.homMk (fun s => DirectSum.component R κ (fun k => (A k).obj s) k) fun _ _ => rfl
@[reassoc (attr := simp)]
theorem Cube.directSumIncl_proj (A : κ → Cube.{v} ι R) (k : κ) :
    Cube.directSumIncl A k ≫ Cube.directSumProj A k = 𝟙 _ := by
  ext s x
  exact DirectSum.component.lof_self (M := fun k => (A k).obj s) R k x
theorem Cube.directSumIncl_proj_of_ne (A : κ → Cube.{v} ι R) {k j : κ} (h : k ≠ j) :
    Cube.directSumIncl A k ≫ Cube.directSumProj A j = 0 := by
  ext s x
  exact (DirectSum.component.of (M := fun k => (A k).obj s) R j k x).trans (dif_neg h)
theorem Cube.exists_sum_directSum [Finite ι] (A : κ → Cube.{v} ι R) (p : ℕ)
    (z : Cube.Term (Cube.directSum A) p) : ∃ T : Finset κ,
      ∑ k ∈ T, Cube.termMap (Cube.directSumProj A k ≫ Cube.directSumIncl A k) p z = z := by
  classical
  have := Fintype.ofFinite {s : Finset ι // s.card = p}
  let z' : ∀ s : {s : Finset ι // s.card = p}, ⨁ k, (A k).obj s.1 := z
  refine ⟨Finset.univ.biUnion fun s => (z' s).support, funext fun s => ?_⟩
  rw [Finset.sum_apply]
  change ∑ k ∈ _, DirectSum.of (fun k => (A k).obj s.1) k (z' s k) = z' s
  refine Eq.trans (Finset.sum_subset (Finset.subset_biUnion_of_mem _ (Finset.mem_univ s))
    fun k _ hk => ?_).symm (DirectSum.sum_support_of (z' s))
  rw [DFinsupp.notMem_support_iff.1 hk, map_zero]
noncomputable def Cube.termDirectSum (A : κ → Cube.{v} ι R) (p : ℕ) :
    (⨁ k, Cube.Term (A k) p) →ₗ[R] Cube.Term (Cube.directSum A) p :=
  DirectSum.toModule R κ _ fun k => Cube.termMap (Cube.directSumIncl A k) p
theorem Cube.termDirectSum_lof (A : κ → Cube.{v} ι R) (p : ℕ) (k : κ) (x : Cube.Term (A k) p) :
    Cube.termDirectSum A p (DirectSum.lof R κ (fun k => Cube.Term (A k) p) k x) =
      Cube.termMap (Cube.directSumIncl A k) p x :=
  DirectSum.toModule_lof (M := fun k => Cube.Term (A k) p) R k x
theorem Cube.termMap_proj_termDirectSum (A : κ → Cube.{v} ι R) (p : ℕ) (j : κ)
    (x : ⨁ k, Cube.Term (A k) p) :
    Cube.termMap (Cube.directSumProj A j) p (Cube.termDirectSum A p x) = x j := by
  have : Cube.termMap (Cube.directSumProj A j) p ∘ₗ Cube.termDirectSum A p =
      DirectSum.component R κ (fun k => Cube.Term (A k) p) j := by
    refine DirectSum.linearMap_ext _ fun k => LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, Cube.termDirectSum_lof]
    change Cube.termMap (Cube.directSumIncl A k ≫ Cube.directSumProj A j) p x = _
    by_cases h : k = j
    · subst h
      rw [Cube.directSumIncl_proj, DirectSum.component.lof_self]
      rfl
    · rw [Cube.directSumIncl_proj_of_ne A h, DirectSum.component.of, dif_neg h]
      rfl
  exact congr($this x)
theorem Cube.termDirectSum_bijective [Finite ι] (A : κ → Cube.{v} ι R) (p : ℕ) :
    Function.Bijective (Cube.termDirectSum A p) := by
  constructor
  · intro x y h
    refine DFinsupp.ext fun j => ?_
    rw [← Cube.termMap_proj_termDirectSum, h, Cube.termMap_proj_termDirectSum]
  · intro z
    obtain ⟨T, hT⟩ := Cube.exists_sum_directSum A p z
    refine ⟨∑ k ∈ T, DirectSum.lof R κ (fun k => Cube.Term (A k) p) k
      (Cube.termMap (Cube.directSumProj A k) p z), Eq.trans ?_ hT⟩
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => Cube.termDirectSum_lof A p k _
noncomputable def Cube.termDirectSumEquiv [Finite ι] (A : κ → Cube.{v} ι R) (p : ℕ) :
    (⨁ k, Cube.Term (A k) p) ≃ₗ[R] Cube.Term (Cube.directSum A) p :=
  LinearEquiv.ofBijective _ (Cube.termDirectSum_bijective A p)
variable [LinearOrder ι]
variable [Finite ι]
noncomputable def cubeDirectSumIsColimit (A : κ → Cube.{v} ι R) :
    IsColimit (Cofan.mk (cubeComplex (Cube.directSum A))
      fun k => cubeComplexMap (Cube.directSumIncl A k)) :=
  HomologicalComplex.isColimitOfEval _ _ fun p =>
    (isColimitMapCoconeCofanMkEquiv (HomologicalComplex.eval _ _ p) _ _).symm
      (IsColimit.ofIsoColimit
        (ModuleCat.coproductCoconeIsColimit fun k => ModuleCat.of R (Cube.Term (A k) p))
        (Cofan.ext (Cube.termDirectSumEquiv A p).toModuleIso fun k =>
          ModuleCat.hom_ext (LinearMap.ext (Cube.termDirectSum_lof A p k))))
noncomputable def cechDirectSumIsColimit (A : κ → Cube.{v} ι R) :
    IsColimit (Cofan.mk (cechComplex (Cube.directSum A))
      fun k => cechComplexMap (Cube.directSumIncl A k)) :=
  HomologicalComplex.isColimitOfEval _ _ fun p =>
    (isColimitMapCoconeCofanMkEquiv (HomologicalComplex.eval _ _ p) _ _).symm
      (IsColimit.ofIsoColimit
        (ModuleCat.coproductCoconeIsColimit fun k => ModuleCat.of R (Cube.Term (A k) (p + 1)))
        (Cofan.ext (Cube.termDirectSumEquiv A (p + 1)).toModuleIso fun k =>
          ModuleCat.hom_ext (LinearMap.ext (Cube.termDirectSum_lof A (p + 1) k))))
noncomputable def cubeHomologyDirectSumEquiv (A : κ → Cube.{v} ι R) (p : ℕ) :
    (⨁ k, (cubeComplex (A k)).homology p) ≃ₗ[R] (cubeComplex (Cube.directSum A)).homology p :=
  LinearEquiv.ofBijective _ (homology_directSum_bijective
    (fun k => cubeComplexMap (Cube.directSumIncl A k))
    (fun k => cubeComplexMap (Cube.directSumProj A k))
    (fun k => congrArg cubeComplexMap (Cube.directSumIncl_proj A k))
    (fun _ _ h => congrArg cubeComplexMap (Cube.directSumIncl_proj_of_ne A h)) p
    (Cube.exists_sum_directSum A p))
noncomputable def cechHomologyDirectSumEquiv (A : κ → Cube.{v} ι R) (p : ℕ) :
    (⨁ k, (cechComplex (A k)).homology p) ≃ₗ[R] (cechComplex (Cube.directSum A)).homology p :=
  LinearEquiv.ofBijective _ (homology_directSum_bijective
    (fun k => cechComplexMap (Cube.directSumIncl A k))
    (fun k => cechComplexMap (Cube.directSumProj A k))
    (fun k => congrArg cechComplexMap (Cube.directSumIncl_proj A k))
    (fun _ _ h => congrArg cechComplexMap (Cube.directSumIncl_proj_of_ne A h)) p
    (Cube.exists_sum_directSum A (p + 1)))
end DirectSum
section TwoDirections
variable {R : Type u} [Ring R]
noncomputable def Cube.termOneFinTwo (A : Cube.{v} (Fin 2) R) :
    Cube.Term A 1 ≃ₗ[R] A.obj {0} × A.obj {1} :=
  (Cube.termOneEquiv A).symm ≪≫ₗ LinearEquiv.piFinTwo R fun i : Fin 2 => A.obj {i}
theorem Cube.termOneFinTwo_apply (A : Cube.{v} (Fin 2) R) (x : Cube.Term A 1) :
    Cube.termOneFinTwo A x = (x ⟨{0}, rfl⟩, x ⟨{1}, rfl⟩) := rfl
def Cube.termTwoFinTwo (A : Cube.{v} (Fin 2) R) : Cube.Term A 2 ≃ₗ[R] A.obj {0, 1} where
  toFun x := x ⟨{0, 1}, rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun a s := Cube.res A (by obtain ⟨s, hs⟩ := s; revert s; decide) a
  left_inv x := by
    ext ⟨s, hs⟩
    obtain rfl : s = {0, 1} := by revert s; decide
    simp
  right_inv a := by simp
theorem Cube.termTwoFinTwo_apply (A : Cube.{v} (Fin 2) R) (x : Cube.Term A 2) :
    Cube.termTwoFinTwo A x = x ⟨{0, 1}, rfl⟩ := rfl
theorem Cube.d_one_finTwo (A : Cube.{v} (Fin 2) R) (x : Cube.Term A 1) :
    Cube.termTwoFinTwo A (Cube.d A 1 x) =
      Cube.res A (by decide) (Cube.termOneFinTwo A x).2 -
        Cube.res A (by decide) (Cube.termOneFinTwo A x).1 := by
  have h := Cube.d_one_apply_pair A x (i := 0) (j := 1) (by decide)
  rw [Cube.termOneFinTwo_apply]
  exact (Cube.termTwoFinTwo_apply A _).trans h
end TwoDirections
section Examples
example : cubeSign ({0, 1, 2} : Finset (Fin 3)) 0 = 1 ∧ cubeSign ({0, 1, 2} : Finset (Fin 3)) 1 = -1 ∧
    cubeSign ({0, 1, 2} : Finset (Fin 3)) 2 = 1 := by decide
example : Cube.termTwoFinTwo (Cube.const (Fin 2) (ModuleCat.of ℤ ℤ))
    (Cube.d _ 1 ((Cube.termOneFinTwo (Cube.const (Fin 2) (ModuleCat.of ℤ ℤ))).symm
      ((3 : ℤ), (10 : ℤ)))) = (7 : ℤ) := by
  rw [Cube.d_one_finTwo, LinearEquiv.apply_symm_apply]
  rfl
example : ¬ (cubeComplex (Cube.const (Fin 0) (ModuleCat.of ℤ ℤ))).ExactAt 0 := by
  rw [cubeComplex_exactAt_zero_iff]
  intro h
  haveI := Cube.subsingleton_term (Cube.const (Fin 0) (ModuleCat.of ℤ ℤ)) (p := 1) (by simp)
  exact (one_ne_zero : (1 : ℤ) ≠ 0) (h (Subsingleton.elim _ _))
example : ¬ (cechComplex (Cube.const (Fin 2) (ModuleCat.of ℤ ℤ))).ExactAt 0 := by
  rw [cochainComplex_exactAt_zero_iff, cechComplex_d _ 0]
  intro h
  have h0 : Cube.aug (Cube.const (Fin 2) (ModuleCat.of ℤ ℤ)) (1 : ℤ) = 0 :=
    h ((Cube.d_aug _ _).trans (map_zero _).symm)
  exact (one_ne_zero : (1 : ℤ) ≠ 0) (congrFun h0 ⟨{0}, rfl⟩)
end Examples
end GlobalTheory


