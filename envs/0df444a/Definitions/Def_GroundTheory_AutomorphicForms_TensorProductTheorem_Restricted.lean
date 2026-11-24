-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:54.746657+00:00
-- url     : https://prove2.me/theorems/778686fa-03f1-40c6-920f-e7e9ba109955
-- title:
--   Restricted
-- statement:
--   Definitions and structural lemmas for Restricted, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Restricted.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace RestrictedTensor
open PiTensorProduct Filter Function Module Set
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
def IsRestricted (ξ x : ∀ v, V v) : Prop :=
  ∀ᶠ v in cofinite, x v = ξ v
theorem isRestricted_iff_finite {ξ x : ∀ v, V v} :
    IsRestricted ξ x ↔ {v | x v ≠ ξ v}.Finite :=
  Filter.eventually_cofinite
theorem IsRestricted.update [DecidableEq ι] {ξ x : ∀ v, V v} (h : IsRestricted ξ x) (i : ι)
    (a : V i) : IsRestricted ξ (Function.update x i a) := by
  rw [isRestricted_iff_finite] at h ⊢
  refine (h.union (Set.finite_singleton i)).subset fun v hv => ?_
  by_cases hvi : v = i
  · exact Or.inr hvi
  · left
    simpa [Function.update_of_ne hvi] using hv
def restrictedTensor (ξ : ∀ v, V v) : Submodule ℂ (⨂[ℂ] v, V v) :=
  Submodule.span ℂ (tprod ℂ '' {x | IsRestricted ξ x})
theorem tprod_mem_restrictedTensor {ξ x : ∀ v, V v} (h : IsRestricted ξ x) :
    tprod ℂ x ∈ restrictedTensor ξ :=
  Submodule.subset_span ⟨x, h, rfl⟩
section Lift
def weight (T : Finset ι) (l : ∀ v, Dual ℂ (V v)) (x : ∀ v, V v) (v : ι) : ℂ := by
  classical
  exact if v ∈ T then 1 else l v (x v)
theorem weight_of_mem {T : Finset ι} (l : ∀ v, Dual ℂ (V v)) (x : ∀ v, V v) {v : ι}
    (hv : v ∈ T) : weight T l x v = 1 := by
  simp [weight, hv]
theorem weight_of_notMem {T : Finset ι} (l : ∀ v, Dual ℂ (V v)) (x : ∀ v, V v) {v : ι}
    (hv : v ∉ T) : weight T l x v = l v (x v) := by
  simp [weight, hv]
theorem mulSupport_weight_subset (ξ : ∀ v, V v) (T : Finset ι) (l : ∀ v, Dual ℂ (V v))
    (x : ∀ v, V v) :
    mulSupport (weight T l x) ⊆ {v | x v ≠ ξ v} ∪ {v | l v (ξ v) ≠ 1} := by
  intro v hv
  rw [mem_mulSupport] at hv
  by_cases hvT : v ∈ T
  · exact absurd (weight_of_mem l x hvT) hv
  · rw [weight_of_notMem l x hvT] at hv
    by_cases hx : x v = ξ v
    · right
      show l v (ξ v) ≠ 1
      rw [← hx]
      exact hv
    · exact Or.inl hx
theorem finite_mulSupport_weight {ξ x : ∀ v, V v} (hx : IsRestricted ξ x) (T : Finset ι)
    {l : ∀ v, Dual ℂ (V v)} (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1) :
    (mulSupport (weight T l x)).Finite :=
  ((isRestricted_iff_finite.1 hx).union (Filter.eventually_cofinite.1 hl)).subset
    (mulSupport_weight_subset ξ T l x)
theorem finprod_update_eq_mul [DecidableEq ι] (w : ι → ℂ) (hw : (mulSupport w).Finite) (i : ι) (c : ℂ) :
    ∏ᶠ v, Function.update w i c v = c * ∏ᶠ v, Function.update w i 1 v := by
  classical
  set s : Finset ι := insert i hw.toFinset
  have hs : ∀ c, mulSupport (Function.update w i c) ⊆ (s : Set ι) := by
    intro c v hv
    by_cases hvi : v = i
    · simp [s, hvi]
    · rw [mem_mulSupport, Function.update_of_ne hvi] at hv
      simp [s, hv]
  rw [finprod_eq_prod_of_mulSupport_subset _ (hs c),
    finprod_eq_prod_of_mulSupport_subset _ (hs 1),
    Finset.prod_update_of_mem (Finset.mem_insert_self i _),
    Finset.prod_update_of_mem (Finset.mem_insert_self i _), one_mul]
theorem weight_update_of_mem {T : Finset ι} (l : ∀ v, Dual ℂ (V v)) (x : ∀ v, V v) {i : ι}
    (hi : i ∈ T) (a : V i) {inst : DecidableEq ι} :
    weight T l (@Function.update _ _ inst x i a) = weight T l x := by
  funext v
  by_cases hv : v ∈ T
  · rw [weight_of_mem l _ hv, weight_of_mem l _ hv]
  · rw [weight_of_notMem l _ hv, weight_of_notMem l _ hv,
      Function.update_of_ne (fun h => hv (by rw [h]; exact hi))]
theorem weight_update_of_notMem {T : Finset ι} (l : ∀ v, Dual ℂ (V v)) (x : ∀ v, V v) {i : ι}
    (hi : i ∉ T) (a : V i) {inst : DecidableEq ι} :
    weight T l (@Function.update _ _ inst x i a) =
      @Function.update _ _ inst (weight T l x) i (l i a) := by
  funext v
  by_cases hvi : v = i
  · subst hvi
    rw [Function.update_self, weight_of_notMem l _ hi, Function.update_self]
  · rw [Function.update_of_ne hvi]
    by_cases hv : v ∈ T
    · rw [weight_of_mem l _ hv, weight_of_mem l _ hv]
    · rw [weight_of_notMem l _ hv, weight_of_notMem l _ hv, Function.update_of_ne hvi]
theorem restrict_update_of_mem {T : Finset ι} (x : ∀ v, V v) {i : ι} (hi : i ∈ T) (a : V i)
    {inst : DecidableEq ι} :
    (fun v : T => @Function.update _ _ inst x i a v) =
      Function.update (fun v : T => x v) ⟨i, hi⟩ a := by
  funext ⟨v, hv⟩
  by_cases hvi : v = i
  · subst hvi
    simp
  · rw [Function.update_of_ne hvi, Function.update_of_ne (fun h => hvi (congrArg Subtype.val h))]
theorem restrict_update_of_notMem {T : Finset ι} (x : ∀ v, V v) {i : ι} (hi : i ∉ T) (a : V i)
    {inst : DecidableEq ι} :
    (fun v : T => @Function.update _ _ inst x i a v) = fun v : T => x v := by
  funext ⟨v, hv⟩
  rw [Function.update_of_ne (fun h => hi (by rw [← h]; exact hv))]
variable {N : Type*} [AddCommGroup N] [Module ℂ N]
def restrictedIndicator (ξ x : ∀ v, V v) : ℂ := by
  classical
  exact if IsRestricted ξ x then 1 else 0
theorem restrictedIndicator_of {ξ x : ∀ v, V v} (h : IsRestricted ξ x) :
    restrictedIndicator ξ x = 1 := by
  simp [restrictedIndicator, h]
theorem restrictedIndicator_of_not {ξ x : ∀ v, V v} (h : ¬ IsRestricted ξ x) :
    restrictedIndicator ξ x = 0 := by
  simp [restrictedIndicator, h]
def restrictedLift (ξ : ∀ v, V v) (T : Finset ι) (l : ∀ v, Dual ℂ (V v))
    (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1) (f : MultilinearMap ℂ (fun v : T => V v) N) :
    MultilinearMap ℂ V N where
  toFun x := restrictedIndicator ξ x • (∏ᶠ v, weight T l x v) • f (fun v => x v)
  map_update_add' := by
    intro inst x i a b
    by_cases hx : IsRestricted ξ x
    · have h1 : ∀ c : V i, IsRestricted ξ (@Function.update _ _ inst x i c) := fun c => by
        have := @IsRestricted.update _ _ _ _ inst ξ x hx i c
        exact this
      simp only [restrictedIndicator_of (h1 _), one_smul]
      by_cases hi : i ∈ T
      · simp only [weight_update_of_mem l x hi, restrict_update_of_mem x hi]
        rw [f.map_update_add, smul_add]
      · simp only [weight_update_of_notMem l x hi, restrict_update_of_notMem x hi]
        have hw := finite_mulSupport_weight hx T hl
        rw [finprod_update_eq_mul _ hw, finprod_update_eq_mul _ hw (c := l i a),
          finprod_update_eq_mul _ hw (c := l i b), map_add, add_mul, add_smul]
    · have h1 : ∀ c : V i, ¬ IsRestricted ξ (@Function.update _ _ inst x i c) := fun c h => by
        apply hx
        have := @IsRestricted.update _ _ _ _ inst ξ _ h i (x i)
        rwa [Function.update_idem, Function.update_eq_self] at this
      simp [restrictedIndicator_of_not (h1 _)]
  map_update_smul' := by
    intro inst x i c a
    by_cases hx : IsRestricted ξ x
    · have h1 : ∀ c : V i, IsRestricted ξ (@Function.update _ _ inst x i c) := fun c => by
        have := @IsRestricted.update _ _ _ _ inst ξ x hx i c
        exact this
      simp only [restrictedIndicator_of (h1 _), one_smul]
      by_cases hi : i ∈ T
      · simp only [weight_update_of_mem l x hi, restrict_update_of_mem x hi]
        rw [f.map_update_smul, smul_comm]
      · simp only [weight_update_of_notMem l x hi, restrict_update_of_notMem x hi]
        have hw := finite_mulSupport_weight hx T hl
        rw [finprod_update_eq_mul _ hw (c := l i (c • a)), finprod_update_eq_mul _ hw (c := l i a),
          map_smul, smul_eq_mul, mul_assoc, mul_smul]
    · have h1 : ∀ c : V i, ¬ IsRestricted ξ (@Function.update _ _ inst x i c) := fun c h => by
        apply hx
        have := @IsRestricted.update _ _ _ _ inst ξ _ h i (x i)
        rwa [Function.update_idem, Function.update_eq_self] at this
      simp [restrictedIndicator_of_not (h1 _)]
def evalForm (ξ : ∀ v, V v) (l : ∀ v, Dual ℂ (V v)) (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1) :
    (⨂[ℂ] v, V v) →ₗ[ℂ] ℂ :=
  lift (restrictedLift ξ ∅ l hl (MultilinearMap.constOfIsEmpty ℂ _ 1))
def projSingleton (v : ι) : MultilinearMap ℂ (fun w : ({v} : Finset ι) => V w) (V v) where
  toFun y := y ⟨v, Finset.mem_singleton_self v⟩
  map_update_add' := by
    intro inst y j a b
    obtain rfl : j = ⟨v, Finset.mem_singleton_self v⟩ := Subsingleton.elim _ _
    simp
  map_update_smul' := by
    intro inst y j c a
    obtain rfl : j = ⟨v, Finset.mem_singleton_self v⟩ := Subsingleton.elim _ _
    simp
def contract (ξ : ∀ v, V v) (l : ∀ v, Dual ℂ (V v)) (hl : ∀ᶠ v in cofinite, l v (ξ v) = 1)
    (v : ι) : (⨂[ℂ] w, V w) →ₗ[ℂ] V v :=
  lift (restrictedLift ξ {v} l hl (projSingleton v))
end Lift
section Finite
variable [DecidableEq ι]
def extend (ξ : ∀ v, V v) (T : Finset ι) (y : ∀ v : T, V v) : ∀ v, V v :=
  fun v => if h : v ∈ T then y ⟨v, h⟩ else ξ v
def finiteEmbed (ξ : ∀ v, V v) (T : Finset ι) : (⨂[ℂ] v : T, V v) →ₗ[ℂ] ⨂[ℂ] v, V v :=
  lift ((PiTensorProduct.tprod ℂ).domDomRestrict (· ∈ T) fun w => ξ w)
end Finite
section Rep
variable {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}
variable (K) in

def tensorRep (π : ∀ v, Representation ℂ (G v) (V v)) :
    Representation ℂ (Πʳ v, [G v, K v]) (⨂[ℂ] v, V v) where
  toFun g := PiTensorProduct.map fun v => π v (g v)
  map_one' := by
    simp only [RestrictedProduct.one_apply, map_one]
    exact PiTensorProduct.map_id
  map_mul' g h := by
    simp only [RestrictedProduct.mul_apply, map_mul]
    exact PiTensorProduct.map_mul _ _
theorem tensorRep_tprod (π : ∀ v, Representation ℂ (G v) (V v)) (g : Πʳ v, [G v, K v])
    (x : ∀ v, V v) :
    tensorRep K π g (tprod ℂ x) = tprod ℂ fun v => π v (g v) (x v) :=
  PiTensorProduct.map_tprod _ _
def restrictedSubrep (π : ∀ v, Representation ℂ (G v) (V v)) (ξ : ∀ v, V v)
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)) :
    Subrepresentation (tensorRep K π) where
  toSubmodule := restrictedTensor ξ
  apply_mem_toSubmodule g t ht := by
    have : restrictedTensor ξ ≤ (restrictedTensor ξ).comap (tensorRep K π g) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, tensorRep_tprod]
      refine tprod_mem_restrictedTensor ?_
      filter_upwards [(hx : ∀ᶠ v in cofinite, x v = ξ v), hξ, g.2] with v h1 h2 h3
      rw [h1]
      exact h2 _ h3
    exact this ht
def restrictedTensorRep (π : ∀ v, Representation ℂ (G v) (V v)) (ξ : ∀ v, V v)
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)) :
    Representation ℂ (Πʳ v, [G v, K v]) (restrictedTensor ξ) :=
  (restrictedSubrep π ξ hξ).toRepresentation
end Rep
end RestrictedTensor
end GroundTheory.Automorphic


