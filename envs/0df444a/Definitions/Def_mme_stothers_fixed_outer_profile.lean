-- Prove2me | Definitions.Def_mme_stothers_fixed_outer_profile
-- name    : mme_stothers_fixed_outer_profile
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T18:46:37.708295+00:00
-- url     : https://prove2.me/theorems/32a085bc-e86b-4101-9744-611b6b5cff99
-- title:
--   Exact fixed outer profile for the Davie–Stothers fourth-power construction
-- statement:
--   Fix a positive integer repetition parameter m, and put N = 97,942,072m. This package gives an exact integral specialization of the ten symmetric constituent classes used in the fourth-power Davie–Stothers laser construction. Its one-period class counts are (98, 1862, 73075, 1023050, 3626000, 98000, 2156000, 13720000, 21560000, 38710000). It records the resulting nine marginal counts from Equation (5.2), exact joint-profile addresses of length 3N, coordinatewise support, marginal regularity, inducedness, mode disjointness, and the explicit target/ambient collision relation needed for Salem–Spencer pruning.
--
--   The rational distribution obtained by dividing these counts by 97,942,072 is a nearby exact stationary certificate, used on both sides of Theorem 5.3; it is not claimed to reproduce the rounded decimal optimizer printed in Table 2. The package contains only finite data and predicates, not the hashing estimate or any constituent-value lower bound.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh Section A 143(2), 2013, Section 5, Table 1, Equation (5.2), Lemma 5.2 and Theorem 5.3, printed pp. 366–368; exact rational stationary specialization independently certified from those equations. https://www.maths.ed.ac.uk/~sandy/a11164.pdf; DOI 10.1017/S0308210511001646.

import Definitions.Def_mme_stothers_fourth_data
import Mathlib.Data.Finset.Prod

open MME BigOperators

namespace MME.StothersFourth

set_option autoImplicit false

/-!
# Exact outer-profile data for the `omega < 2.3737` witness

These definitions expose the finite type-1 hypergraph used by the fixed
Davie--Stothers witness.  They contain no extraction or cardinality claim.
-/

/-- Common denominator of the exact stationary witness. -/
def fixedProfileScale : ℕ := 97942072

/-- One period of exact Table-1 class counts. -/
def fixedProfileBaseCount : Fin 10 → ℕ :=
  ![98, 1862, 73075, 1023050, 3626000,
    98000, 2156000, 13720000, 21560000, 38710000]

def fixedProfileCount (m : ℕ) (i : Fin 10) : ℕ :=
  m * fixedProfileBaseCount i

/-- Exact rational stationary witness used on both sides of Theorem 5.3. -/
noncomputable def fixedProfileB : Fin 10 → ℝ :=
  fun i ↦ (fixedProfileBaseCount i : ℝ) / fixedProfileScale

/-- A decidable presentation of the six permutations of three coordinates. -/
def fixedSameOrbitExplicit (σ ρ : Fin 3 → Fin 9) : Prop :=
  (σ 0 = ρ 0 ∧ σ 1 = ρ 1 ∧ σ 2 = ρ 2) ∨
  (σ 0 = ρ 0 ∧ σ 1 = ρ 2 ∧ σ 2 = ρ 1) ∨
  (σ 0 = ρ 1 ∧ σ 1 = ρ 0 ∧ σ 2 = ρ 2) ∨
  (σ 0 = ρ 1 ∧ σ 1 = ρ 2 ∧ σ 2 = ρ 0) ∨
  (σ 0 = ρ 2 ∧ σ 1 = ρ 0 ∧ σ 2 = ρ 1) ∨
  (σ 0 = ρ 2 ∧ σ 1 = ρ 1 ∧ σ 2 = ρ 0)

instance fixedDecidableSameOrbitExplicit (σ ρ : Fin 3 → Fin 9) :
    Decidable (fixedSameOrbitExplicit σ ρ) := by
  unfold fixedSameOrbitExplicit
  infer_instance

/-- The `3N` positions at exact scale `N = fixedProfileScale * m`. -/
def fixedOuterLength (m : ℕ) : ℕ :=
  3 * (fixedProfileScale * m)

def FixedOuterAddress (m : ℕ) : Type :=
  Fin 3 → Fin (fixedOuterLength m) → Fin 9

def fixedAddressType {m : ℕ} (a : FixedOuterAddress m)
    (k : Fin (fixedOuterLength m)) : Fin 3 → Fin 9 :=
  fun s ↦ a s k

def fixedClassOrbit (r : Fin 10) : Finset (Fin 3 → Fin 9) :=
  Finset.univ.filter (fun σ ↦ fixedSameOrbitExplicit σ (classRep r))

/-- Transpose of the integer coefficient matrix in Equation (5.2). -/
def fixedClassMarginalMultiplicity : Fin 10 → Fin 9 → ℕ :=
  ![![2, 0, 0, 0, 0, 0, 0, 0, 1],
    ![2, 2, 0, 0, 0, 0, 0, 2, 0],
    ![2, 0, 2, 0, 0, 0, 2, 0, 0],
    ![2, 0, 0, 2, 0, 2, 0, 0, 0],
    ![1, 0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 1, 0, 0],
    ![0, 2, 2, 0, 0, 2, 0, 0, 0],
    ![0, 2, 0, 2, 2, 0, 0, 0, 0],
    ![0, 0, 2, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 2, 0, 0, 0, 0, 0]]

/-- Every member of class `r` occurs this many times; unsupported joint
types have multiplicity zero. -/
def fixedJointMultiplicity (m : ℕ) (σ : Fin 3 → Fin 9) : ℕ :=
  ∑ r : Fin 10,
    if fixedSameOrbitExplicit σ (classRep r) then
      fixedProfileCount m r
    else 0

def FixedExactOuterAddress (m : ℕ) : Type :=
  {a : FixedOuterAddress m //
    ∀ σ : Fin 3 → Fin 9,
      (Finset.univ.filter (fun k ↦ fixedAddressType a k = σ)).card =
        fixedJointMultiplicity m σ}

/-- Numerators of the exact nine-grade marginal in Equation (5.2). -/
def fixedMarginalBaseCount : Fin 9 → ℕ :=
  ![5822170, 31951724, 86288150, 106906100, 56252000,
    6358100, 244150, 3724, 98]

def fixedMarginalCount (m : ℕ) (j : Fin 9) : ℕ :=
  m * fixedMarginalBaseCount j

def FixedMarginallyRegular {m : ℕ} (a : FixedOuterAddress m) : Prop :=
  ∀ s : Fin 3, ∀ j : Fin 9,
    (Finset.univ.filter (fun k ↦ a s k = j)).card =
      fixedMarginalCount m j

def FixedCoordinatewiseSupported {m : ℕ}
    (a : FixedOuterAddress m) : Prop :=
  ∀ k, (∑ s, ((a s k).val : ℕ)) = 8

/-- Full marginal-supported ambient hypergraph for the outer hash. -/
def FixedMarginalSupportedAddress (m : ℕ) : Type :=
  {a : FixedOuterAddress m //
    FixedCoordinatewiseSupported a ∧ FixedMarginallyRegular a}

def FixedHasExactJointProfile {m : ℕ}
    (a : FixedMarginalSupportedAddress m) : Prop :=
  ∀ σ : Fin 3 → Fin 9,
    (Finset.univ.filter (fun k ↦ fixedAddressType a.1 k = σ)).card =
      fixedJointMultiplicity m σ

def fixedMixedAddress {m : ℕ}
    (x y z : FixedOuterAddress m) : FixedOuterAddress m
  | ⟨0, _⟩ => x 0
  | ⟨1, _⟩ => y 1
  | ⟨2, _⟩ => z 2
  | ⟨_ + 3, h⟩ => absurd h (by omega)

def FixedModeDisjoint {m : ℕ}
    (F : Finset (FixedExactOuterAddress m)) : Prop :=
  ∀ x : F, ∀ y : F, x ≠ y → ∀ s : Fin 3, x.1.1 s ≠ y.1.1 s

def FixedInduced {m : ℕ}
    (F : Finset (FixedExactOuterAddress m)) : Prop :=
  ∀ x : F, ∀ y : F, ∀ z : F,
    FixedCoordinatewiseSupported
      (fixedMixedAddress x.1.1 y.1.1 z.1.1) →
      x = y ∧ y = z

def FixedInducedModeDisjoint {m : ℕ}
    (F : Finset (FixedExactOuterAddress m)) : Prop :=
  FixedModeDisjoint F ∧ FixedInduced F

/-- Closure condition needed by deterministic collision pruning: every
supported mixed edge assembled from retained vertices is itself retained. -/
def FixedMarginalVertexClosed {m : ℕ}
    (E : Finset (FixedMarginalSupportedAddress m)) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, ∀ z ∈ E,
    FixedCoordinatewiseSupported
      (fixedMixedAddress x.1 y.1 z.1) →
      ∃ e ∈ E, e.1 = fixedMixedAddress x.1 y.1 z.1

/-- Exact-profile target edges inside a marginal-supported ambient family. -/
noncomputable def fixedExactTargetEdges {m : ℕ}
    (E : Finset (FixedMarginalSupportedAddress m)) :
    Finset (FixedMarginalSupportedAddress m) := by
  classical
  exact E.filter FixedHasExactJointProfile

/-- Ordered target--ambient pairs sharing at least one mode word. -/
noncomputable def fixedTargetAmbientCollisions {m : ℕ}
    (E : Finset (FixedMarginalSupportedAddress m)) :
    Finset (FixedMarginalSupportedAddress m ×
      FixedMarginalSupportedAddress m) := by
  classical
  exact (fixedExactTargetEdges E ×ˢ E).filter (fun p ↦
    p.1 ≠ p.2 ∧ ∃ s : Fin 3, p.1.1 s = p.2.1 s)

end MME.StothersFourth


