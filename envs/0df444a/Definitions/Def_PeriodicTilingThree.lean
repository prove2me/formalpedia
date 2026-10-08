-- Prove2me | Definitions.Def_PeriodicTilingThree
-- name    : PeriodicTilingThree
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:02.492336+00:00
-- url     : https://prove2.me/theorems/c01f1372-1527-4576-bbff-6aa9d98138b6
-- statement:
--   Working in an arbitrary additive commutative group G, a finite set F tiles a set A when the addition map from pairs (f,a) with f in F and a in A to G is a bijection, so every element of G is written uniquely as f+a. A vector v is a period of A when x+v lies in A exactly when x lies in A, for every x; A is FullyPeriodic when some finite-index subgroup P of G consists entirely of periods of A. Lattice(d) is the integer lattice of functions Fin d to ℤ, and Space(d) is real d-space Fin d → ℝ, with castLattice the additive embedding of integer vectors into real vectors and unitCube(d) the closed cube [0,1]^d. Thickening(F), for a finite F of lattice points, is the union of the unit cubes translated by the points of F. AETiles(Ω,A) says that for Lebesgue-almost every x there is exactly one a in A with x−a in Ω. For a real basis b of Space(d), latticeOfBasis(b) is the additive subgroup of integer linear combinations of the basis vectors, and EuclideanFullyPeriodic(A) says that for some basis b every vector of latticeOfBasis(b) is a period of A. Finally, HasTileWithoutPeriodicComplement(d) is a defined proposition, not an established theorem: it asserts that there is a nonempty finite set T of integer lattice points in dimension d such that T tiles some subset A of the lattice, yet every subset A of the lattice that T tiles fails to be FullyPeriodic.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PeriodicTilingThree.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PeriodicTilingThree.lean; bytes 16..1498
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

universe u

namespace PeriodicTilingThree

abbrev Lattice (d : ℕ) := Fin d → ℤ

variable {G : Type u} [AddCommGroup G]

def Tiles (F : Finset G) (A : Set G) : Prop :=
  Function.Bijective (fun p : ↥F × A => (p.1 : G) + (p.2 : G))

def Period (A : Set G) (v : G) : Prop :=
  ∀ x : G, x + v ∈ A ↔ x ∈ A

def FullyPeriodic (A : Set G) : Prop :=
  ∃ P : AddSubgroup G, P.FiniteIndex ∧ ∀ v ∈ P, Period A v

open MeasureTheory

abbrev Space (d : ℕ) := Fin d → ℝ

def castLattice {d : ℕ} : Lattice d →+ Space d where
  toFun z i := (z i : ℝ)
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp

def unitCube (d : ℕ) : Set (Space d) := Set.Icc 0 1

def Thickening {d : ℕ} (F : Finset (Lattice d)) : Set (Space d) :=
  {x | ∃ z ∈ F, x - castLattice z ∈ unitCube d}

def AETiles {d : ℕ} (Ω A : Set (Space d)) : Prop :=
  ∀ᵐ x ∂volume, ∃! a : A, x - (a : Space d) ∈ Ω

def latticeOfBasis {d : ℕ} (b : Module.Basis (Fin d) ℝ (Space d)) :
    AddSubgroup (Space d) := (Submodule.span ℤ (Set.range b)).toAddSubgroup

def EuclideanFullyPeriodic {d : ℕ} (A : Set (Space d)) : Prop :=
  ∃ b : Module.Basis (Fin d) ℝ (Space d), ∀ v ∈ latticeOfBasis b, Period A v

def HasTileWithoutPeriodicComplement (d : ℕ) : Prop :=
  ∃ T : Finset (Lattice d), T.Nonempty ∧
    (∃ A : Set (Lattice d), Tiles T A) ∧
    ∀ A : Set (Lattice d), Tiles T A → ¬ FullyPeriodic A



end PeriodicTilingThree
end
end OAI


