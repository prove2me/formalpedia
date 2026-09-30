-- Prove2me | Definitions.Def_capacityBlockIncidence
-- name    : capacityBlockIncidence
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-07T18:03:31.130557+00:00
-- url     : https://prove2.me/theorems/dc0be9ff-029f-45f7-9d7c-b9f5b39c5d66
-- title:
--   Nonempty-block incidence and singleton potentials
-- statement:
--   Let $X$ be a finite label set, $\mathcal B(X)$ its nonempty subsets, and $\Pi(X)$ its set of partitions. Rational block coefficients are evaluated by the linear map
--
--   $$T:\mathbb Q^{\mathcal B(X)}\longrightarrow\mathbb Q^{\Pi(X)},\qquad (Tc)(P)=\sum_{B\in P}c_B.$$
--
--   The bundle also defines the coordinate-sum functional $L(a)=\sum_{i\in X}a_i$ and the modular potential $M(a)_B=\sum_{i\in B}a_i$. Restriction of $M$ gives an actual linear equivalence from $\ker L$ to $\ker T$, with its proved constructor dependencies included. This describes the row relations needed for the rank calculation; the rank theorem itself is separate. Empty label sets are allowed in these definitions, and the equivalence does not assume that the sum functional is nonzero.
-- source:
--   The four-label correlation threshold, Theorem 2.1 and equations (2.1)–(2.5). Unpublished research note (2026), N4_BLOCK_CORRELATION_NOTE.md, SHA-256 a9b67c132ca0e0af807fb917ca2322833b84e162c45a4da7329ee88fbe4f1c83. Exact formal source: formal_capacity/FormalCapacity/Finite/BlockRank.lean, source-file SHA-256 0adb1c853d3a750450a8b0f6899884f5e03206466fc1f165f86e21e0849a29bc. Local source archive; no public repository URL or commit is asserted. Upload checked with Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Definitions.Def_capacityFinitePartitions

set_option autoImplicit false

/-!
# Rank of first-order block incidence

This file upgrades the row-relation characterization in `Partition.lean` to
the finite-dimensional rank formula `2^n - n`.
-/

namespace FormalCapacity.Finite

open scoped BigOperators
open Finset Module

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A nonempty block of labels. -/
abbrev NonemptyBlock (α : Type*) [Fintype α] [DecidableEq α] :=
  {B : Finset α // B.Nonempty}

instance : Fintype (NonemptyBlock α) := by
  unfold NonemptyBlock
  infer_instance

/-- Extend coefficients on nonempty blocks by zero at the empty block. -/
def extendBlockCoeff (c : NonemptyBlock α → ℚ) (B : Finset α) : ℚ :=
  if hB : B.Nonempty then c ⟨B, hB⟩ else 0

lemma extendBlockCoeff_add (c d : NonemptyBlock α → ℚ) (B : Finset α) :
    extendBlockCoeff (c + d) B = extendBlockCoeff c B + extendBlockCoeff d B := by
  by_cases hB : B.Nonempty <;> simp [extendBlockCoeff, hB]

lemma extendBlockCoeff_smul (r : ℚ) (c : NonemptyBlock α → ℚ)
    (B : Finset α) :
    extendBlockCoeff (r • c) B = r * extendBlockCoeff c B := by
  by_cases hB : B.Nonempty <;> simp [extendBlockCoeff, hB]

/-- The transpose of the block-incidence projection: a coefficient on each
nonempty block is evaluated additively on every partition. -/
def blockIncidenceTranspose :
    (NonemptyBlock α → ℚ) →ₗ[ℚ]
      (Finpartition (univ : Finset α) → ℚ) where
  toFun c P := blockRowSum (extendBlockCoeff c) P
  map_add' c d := by
    funext P
    simp [blockRowSum, extendBlockCoeff_add, Finset.sum_add_distrib]
  map_smul' r c := by
    funext P
    simp [blockRowSum, extendBlockCoeff_smul, Finset.mul_sum]

/-- The kernel consists exactly of zero-sum modular singleton potentials. -/
theorem mem_ker_blockIncidenceTranspose_iff (c : NonemptyBlock α → ℚ) :
    c ∈ (blockIncidenceTranspose (α := α)).ker ↔
      (∀ B : NonemptyBlock α,
        c B = ∑ i ∈ B.1, c ⟨{i}, singleton_nonempty i⟩) ∧
      (∑ i : α, c ⟨{i}, singleton_nonempty i⟩) = 0 := by
  constructor
  · intro hc
    have hrel : ∀ P : Finpartition (univ : Finset α),
        blockRowSum (extendBlockCoeff c) P = 0 := by
      intro P
      have hfun : blockIncidenceTranspose (α := α) c = 0 := hc
      exact congrFun hfun P
    constructor
    · intro B
      have h := rowRelation_eq_sum_singletons (extendBlockCoeff c) hrel B.2
      simpa [extendBlockCoeff, B.2] using h
    · have h := rowRelation_singletons_sum_zero (extendBlockCoeff c) hrel
      simpa [extendBlockCoeff] using h
  · rintro ⟨hmod, hsum⟩
    rw [LinearMap.mem_ker]
    funext P
    change blockRowSum (extendBlockCoeff c) P = 0
    have hpoint : ∀ B : Finset α,
        extendBlockCoeff c B =
          ∑ i ∈ B, c ⟨{i}, singleton_nonempty i⟩ := by
      intro B
      by_cases hB : B.Nonempty
      · simpa [extendBlockCoeff, hB] using hmod ⟨B, hB⟩
      · have hBe : B = ∅ := not_nonempty_iff_eq_empty.mp hB
        subst B
        simp [extendBlockCoeff]
    simp only [blockRowSum]
    simp_rw [hpoint]
    exact sum_singletons_rowRelation
      (fun i ↦ c ⟨{i}, singleton_nonempty i⟩) hsum P

/-- Sum of label coordinates as a linear functional. -/
def labelSum : (α → ℚ) →ₗ[ℚ] ℚ where
  toFun a := ∑ i, a i
  map_add' a b := Finset.sum_add_distrib
  map_smul' r a := by simp [Finset.mul_sum]

/-- Turn a label potential into its modular nonempty-block coefficients. -/
def modularPotential : (α → ℚ) →ₗ[ℚ] (NonemptyBlock α → ℚ) where
  toFun a B := ∑ i ∈ B.1, a i
  map_add' a b := by ext B; simp [Finset.sum_add_distrib]
  map_smul' r a := by ext B; simp [Finset.mul_sum]

/-- A zero-sum label potential lands in the incidence kernel. -/
def modularPotentialToKernel :
    (labelSum (α := α)).ker →ₗ[ℚ]
      (blockIncidenceTranspose (α := α)).ker where
  toFun a := ⟨modularPotential a.1, by
    apply (mem_ker_blockIncidenceTranspose_iff _).2
    constructor
    · intro B
      simp [modularPotential]
    · simpa [modularPotential, labelSum] using a.2⟩
  map_add' a b := by
    ext B
    exact Finset.sum_add_distrib
  map_smul' r a := by ext B; simp [modularPotential]

theorem modularPotentialToKernel_bijective :
    Function.Bijective (modularPotentialToKernel (α := α)) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    funext i
    have hi := congrFun (congrArg Subtype.val hab) ⟨{i}, singleton_nonempty i⟩
    simpa [modularPotentialToKernel, modularPotential] using hi
  · intro c
    let a : α → ℚ := fun i ↦ c.1 ⟨{i}, singleton_nonempty i⟩
    have hc := (mem_ker_blockIncidenceTranspose_iff c.1).1 c.2
    have ha : a ∈ (labelSum (α := α)).ker := by
      simpa [LinearMap.mem_ker, labelSum, a] using hc.2
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    funext B
    simpa [modularPotentialToKernel, modularPotential, a] using (hc.1 B).symm

/-- The incidence kernel and the zero-sum-potential space are linearly
equivalent. -/
noncomputable def incidenceKernelEquivZeroSum :
    (labelSum (α := α)).ker ≃ₗ[ℚ]
      (blockIncidenceTranspose (α := α)).ker :=
  LinearEquiv.ofBijective (modularPotentialToKernel (α := α))
    modularPotentialToKernel_bijective

/-- Nonempty finite subsets are the complements of the unique empty subset. -/
def nonemptyBlockEquivNeEmpty : NonemptyBlock α ≃
    {B : Finset α // B ≠ ∅} :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun _ ↦ Finset.nonempty_iff_ne_empty)













end FormalCapacity.Finite


