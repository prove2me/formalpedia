-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_Smooth
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:12:55.684117+00:00
-- url     : https://prove2.me/theorems/7901f2eb-55ac-4816-85ac-c72fc8bfc30c
-- title:
--   Smooth
-- statement:
--   Definitions and structural lemmas for Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/Smooth.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Restricted
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_TotallyDisconnectedSpaceRestrictedProduct
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isCompact_boxSubgroup
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_isOpen_boxSubgroup
import Theorems.Thm_GroundTheory_Automorphic_exists_openSubgroup_isCompact_subset

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
open PiTensorProduct Filter Function Module Set Topology
open scoped TensorProduct RestrictedProduct
variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
  {π : ∀ v, Representation ℂ (G v) (V v)} {ξ : ∀ v, V v}
theorem exists_boxSubgroup_fixing (hπ : ∀ v, IsSmooth (π v))
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)) {t : ⨂[ℂ] v, V v}
    (ht : t ∈ restrictedTensor ξ) :
    ∃ K' : ∀ v, Subgroup (G v), (∀ v, IsCompact (K' v : Set (G v))) ∧
      (∀ v, IsOpen (K' v : Set (G v))) ∧ (∀ v, K' v ≤ K v) ∧ (∀ᶠ v in cofinite, K' v = K v) ∧
        ∀ g ∈ boxSubgroup K K', tensorRep K π g t = t := by
  classical
  have hKcs : ∀ v, IsCompact (K v : Set (G v)) := fun v => isCompact_iff_compactSpace.2 (hKc v)
  induction ht using Submodule.span_induction with
  | mem t ht =>
    obtain ⟨x, hx, rfl⟩ := ht
    have hL : ∀ v, ∃ L : Subgroup (G v), IsCompact (L : Set (G v)) ∧ IsOpen (L : Set (G v)) ∧
        L ≤ K v ∧ ∀ g ∈ L, π v g (x v) = x v := by
      intro v
      obtain ⟨L, hLc, hLU⟩ := exists_openSubgroup_isCompact_subset
        (((hπ v) (x v)).inter (hKo.out v) |>.mem_nhds ⟨(stabilizerOf (π v) (x v)).one_mem,
          (K v).one_mem⟩)
      exact ⟨L, hLc, L.isOpen, fun g hg => (hLU hg).2, fun g hg => (hLU hg).1⟩
    choose L hLc hLo hLK hLfix using hL
    set K' : ∀ v, Subgroup (G v) :=
      fun v => if x v = ξ v ∧ ξ v ∈ fixedVectors (π v) (K v) then K v else L v
    refine ⟨K', fun v => ?_, fun v => ?_, fun v => ?_, ?_, fun g hg => ?_⟩
    · by_cases h : x v = ξ v ∧ ξ v ∈ fixedVectors (π v) (K v) <;> simp [K', h, hLc v, hKcs v]
    · by_cases h : x v = ξ v ∧ ξ v ∈ fixedVectors (π v) (K v) <;> simp [K', h, hLo v, hKo.out v]
    · by_cases h : x v = ξ v ∧ ξ v ∈ fixedVectors (π v) (K v) <;> simp [K', h, hLK v]
    · filter_upwards [show ∀ᶠ v in cofinite, x v = ξ v from hx, hξ] with v h1 h2
      simp [K', h1, h2]
    · rw [tensorRep_tprod]
      congr 1
      funext v
      have hgv := hg v
      by_cases h : x v = ξ v ∧ ξ v ∈ fixedVectors (π v) (K v)
      · simp only [K', h, and_self, if_true] at hgv
        rw [h.1]
        exact h.2 _ hgv
      · simp only [K', h, if_false] at hgv
        exact hLfix v _ hgv
  | zero =>
    exact ⟨K, hKcs, fun v => hKo.out v, fun v => le_rfl, Eventually.of_forall fun v => rfl,
      fun g _ => map_zero _⟩
  | add a b _ _ ha hb =>
    obtain ⟨A, hAc, hAo, hAK, hAe, hAfix⟩ := ha
    obtain ⟨B, hBc, hBo, hBK, hBe, hBfix⟩ := hb
    refine ⟨fun v => A v ⊓ B v, fun v => (hAc v).inter_right (Subgroup.isClosed_of_isOpen _
      (hBo v)), fun v => (hAo v).inter (hBo v), fun v => inf_le_left.trans (hAK v), ?_,
      fun g hg => ?_⟩
    · filter_upwards [hAe, hBe] with v h1 h2
      rw [h1, h2, inf_idem]
    · rw [map_add, hAfix g fun v => (hg v).1, hBfix g fun v => (hg v).2]
  | smul c a _ ha =>
    obtain ⟨A, hAc, hAo, hAK, hAe, hAfix⟩ := ha
    exact ⟨A, hAc, hAo, hAK, hAe, fun g hg => by rw [map_smul, hAfix g hg]⟩
theorem isSmooth_restrictedTensorRep (hπ : ∀ v, IsSmooth (π v))
    (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v)) :
    IsSmooth (restrictedTensorRep π ξ hξ) := by
  intro t
  obtain ⟨K', hK'c, hK'o, -, hK'e, hfix⟩ := exists_boxSubgroup_fixing hπ hξ t.2
  refine Subgroup.isOpen_mono (H₁ := boxSubgroup K K') (fun g hg => ?_)
    (isOpen_boxSubgroup hK'o hK'e)
  exact Subtype.ext (hfix g hg)
section Window
variable (hπ : ∀ v, IsSmooth (π v)) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
  {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)
include hK'c hK'e in
omit hKc in
theorem isCompact_boxSubgroup_of_eq :
    IsCompact (boxSubgroup K K' : Set (Πʳ v, [G v, K v])) :=
  isCompact_boxSubgroup hK'c (hK'e.mono fun v h => h.le)
end Window
section Admissible
variable (hπ : ∀ v, IsAdmissible (π v)) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
  {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v)))
omit [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)] hKo hKc in

def windowEmbed [DecidableEq ι] (ξ : ∀ v, V v) (S : Finset ι) :
    (⨂[ℂ] v : S, fixedVectors (π v) (K' v)) →ₗ[ℂ] ⨂[ℂ] v, V v :=
  finiteEmbed ξ S ∘ₗ PiTensorProduct.map fun v => (fixedVectors (π v) (K' v)).subtype
end Admissible
end RestrictedTensor
end GroundTheory.Automorphic


