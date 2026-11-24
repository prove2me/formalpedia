-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TopologicalKrullDimAffinePoints
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TopologicalKrullDimAffinePoints
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:11:42.501374+00:00
-- url     : https://prove2.me/theorems/76ac9a94-d879-44d4-8317-06d6980f2d66
-- title:
--   Topological Krull Dim Affine Points
-- statement:
--   Definitions and structural lemmas for Topological Krull Dim Affine Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/TopologicalKrullDimAffinePoints.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Theorems.Thm_GlobalTheory_FlagPts_isOpen_affPts_ne_zero
import Theorems.Thm_GlobalTheory_FullFlag_map_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FullFlag.map_sub


set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlagPts
open MvPolynomial
variable {k : Type} [Field k] {J : Type}
def affPtsVanIdeal (x : AffPts k J) : PrimeSpectrum (MvPolynomial J k) :=
  ⟨RingHom.ker (MvPolynomial.eval (show J → k from x)), RingHom.ker_isPrime _⟩
theorem mem_affPtsVanIdeal_preimage_basicOpen (p : MvPolynomial J k) (x : AffPts k J) :
    x ∈ affPtsVanIdeal ⁻¹' (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum (MvPolynomial J k))) ↔
      MvPolynomial.eval x p ≠ 0 := by
  simp [affPtsVanIdeal, PrimeSpectrum.mem_basicOpen]
theorem isInducing_affPtsVanIdeal : Topology.IsInducing (affPtsVanIdeal (k := k) (J := J)) := by
  rw [Topology.isInducing_iff, PrimeSpectrum.isTopologicalBasis_basic_opens.eq_generateFrom,
    induced_generateFrom_eq]
  show TopologicalSpace.generateFrom _ = _
  congr 1
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨_, ⟨p, rfl⟩, by ext x; exact mem_affPtsVanIdeal_preimage_basicOpen p x⟩
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, by ext x; exact mem_affPtsVanIdeal_preimage_basicOpen p x⟩
theorem isTopologicalBasis_affPts :
    IsTopologicalBasis (Set.preimage (affPtsVanIdeal (k := k) (J := J)) ''
      Set.range fun p : MvPolynomial J k ↦ (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum (MvPolynomial J k)))) :=
  PrimeSpectrum.isTopologicalBasis_basic_opens.isInducing isInducing_affPtsVanIdeal
theorem isIrreducible_univ_affPts [Infinite k] : IsIrreducible (Set.univ : Set (AffPts k J)) := by
  refine ⟨⟨fun _ ↦ 0, trivial⟩, ?_⟩
  rintro u v hu hv ⟨x, -, hx⟩ ⟨y, -, hy⟩
  obtain ⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, hxp, hpu⟩ := isTopologicalBasis_affPts.exists_subset_of_mem_open hx hu
  obtain ⟨_, ⟨_, ⟨q, rfl⟩, rfl⟩, hyq, hqv⟩ := isTopologicalBasis_affPts.exists_subset_of_mem_open hy hv
  rw [mem_affPtsVanIdeal_preimage_basicOpen] at hxp hyq
  have hp : p ≠ 0 := by rintro rfl; simp at hxp
  have hq : q ≠ 0 := by rintro rfl; simp at hyq
  have hpq : p * q ≠ 0 := mul_ne_zero hp hq
  obtain ⟨z, hz⟩ : ∃ z : AffPts k J, MvPolynomial.eval z (p * q) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hpq (MvPolynomial.funext fun z ↦ by simpa using h z)
  rw [map_mul] at hz
  refine ⟨z, trivial, hpu ?_, hqv ?_⟩
  · exact (mem_affPtsVanIdeal_preimage_basicOpen p z).2 (left_ne_zero_of_mul hz)
  · exact (mem_affPtsVanIdeal_preimage_basicOpen q z).2 (right_ne_zero_of_mul hz)
open Classical in

def affPtsProj (S : Set J) (x : AffPts k J) : AffPts k J := fun j ↦ if j ∈ S then x j else 0
open Classical in
theorem eval_affPtsProj (S : Set J) (x : AffPts k J) (p : MvPolynomial J k) :
    MvPolynomial.eval (affPtsProj S x) p =
      MvPolynomial.eval x (MvPolynomial.bind₁ (fun j ↦ if j ∈ S then (X j : MvPolynomial J k) else 0) p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.bind₁_C_right]
    exact (MvPolynomial.eval_C (f := affPtsProj S x) a).trans (MvPolynomial.eval_C (f := x) a).symm
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, map_mul, hp, MvPolynomial.bind₁_X_right]
    congr 1
    rw [MvPolynomial.eval_X (f := affPtsProj S x)]
    by_cases hj : j ∈ S
    · rw [if_pos hj, MvPolynomial.eval_X (f := x)]
      show (if j ∈ S then x j else 0) = x j
      rw [if_pos hj]
    · rw [if_neg hj, map_zero]
      show (if j ∈ S then x j else 0) = 0
      rw [if_neg hj]
theorem continuous_affPtsProj (S : Set J) : Continuous (affPtsProj (k := k) S) := by
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨p, rfl⟩
  classical
  convert isOpen_affPts_ne_zero (k := k)
    (MvPolynomial.bind₁ (fun j ↦ if j ∈ S then (X j : MvPolynomial J k) else 0) p) using 1
  ext x
  show MvPolynomial.eval (affPtsProj S x) p ≠ 0 ↔ _
  rw [eval_affPtsProj]
  rfl
theorem range_affPtsProj (S : Set J) :
    Set.range (affPtsProj (k := k) S) = {x : AffPts k J | ∀ j, j ∉ S → x j = 0} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ j hj
    simp [affPtsProj, hj]
  · intro hx
    refine ⟨x, funext fun j ↦ ?_⟩
    by_cases hj : j ∈ S
    · simp [affPtsProj, hj]
    · simp [affPtsProj, hj, hx j hj]
theorem isClosed_coordSubspace (S : Set J) : IsClosed {x : AffPts k J | ∀ j, j ∉ S → x j = 0} := by
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦ ?_
  rw [← isOpen_compl_iff]
  have : ({x : AffPts k J | x j = 0}ᶜ : Set (AffPts k J)) =
      {x : AffPts k J | MvPolynomial.eval x (X j : MvPolynomial J k) ≠ 0} := by
    ext x
    exact Iff.not (Eq.to_iff (congrArg (· = (0 : k)) (MvPolynomial.eval_X (f := x) j).symm))
  rw [this]
  exact isOpen_affPts_ne_zero _
def coordSubspace [Infinite k] (S : Set J) : IrreducibleCloseds (AffPts k J) :=
  ⟨{x : AffPts k J | ∀ j, j ∉ S → x j = 0},
    by
      rw [← range_affPtsProj, ← Set.image_univ]
      exact isIrreducible_univ_affPts.image _ (continuous_affPtsProj S).continuousOn,
    isClosed_coordSubspace S⟩
end GlobalTheory.FlagPts


