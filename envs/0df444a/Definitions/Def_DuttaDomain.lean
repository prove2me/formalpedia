-- Prove2me | Definitions.Def_DuttaDomain
-- name    : DuttaDomain
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:08.634349+00:00
-- url     : https://prove2.me/theorems/744532a7-acb5-4b7b-a7aa-7a67030139b3
-- statement:
--   For a commutative ring A, d(A) is its Krull dimension converted to a natural number, with zero used for the bottom value. For a local ring with maximal ideal m, the colength at N is the module length of A/mᴺ converted to a natural number; the normalized colength is d(A)! times this colength divided by Nᵈ⁽ᴬ⁾. Its multiplicity e(A) is the chosen limit value of these real numbers as N tends to infinity. For a Noetherian local ring R, a short complex means an integer-indexed cochain complex of finite free R-modules that vanishes outside degrees −d(R) through 0, has finite-length homology in every degree, and has nonzero zeroth homology. In prime characteristic p, the nth Frobenius complex is obtained by extending scalars along r ↦ r^(pⁿ). The short Euler characteristic of a complex is the alternating sum, for 0 ≤ i ≤ d(R), of the natural-number conversions of the lengths of its homology in degree −i. The Dutta sequence multiplies the short Euler characteristic of the nth Frobenius complex by p^(−nd(R)), and Dutta multiplicity is its chosen limit value. These definitions alone do not assert convergence. DuttaDomainClaim is the defined proposition that, for every Noetherian local domain D complete with respect to its maximal ideal, every prime characteristic p, and every short complex F over D, all homology modules of every Frobenius complex have finite length, the Dutta sequence converges to the Dutta multiplicity, and e(D) is at most that Dutta multiplicity.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DuttaDomain.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DuttaDomain.lean; bytes 16..2560
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
namespace Lech
noncomputable def dimension (A : Type*) [CommRing A] : ℕ :=
  (WithBot.unbotD 0 (ringKrullDim A)).toNat

noncomputable def colength (A : Type*) [CommRing A] [IsLocalRing A]
    (N : ℕ) : ℕ :=
  (Module.length A (A ⧸ (IsLocalRing.maximalIdeal A) ^ N)).toNat

noncomputable def normalizedColength (A : Type*) [CommRing A] [IsLocalRing A]
    (N : ℕ) : ℝ :=
  (Nat.factorial (dimension A) : ℝ) * (colength A N : ℝ) /
    (N : ℝ) ^ dimension A

noncomputable def multiplicity (A : Type*) [CommRing A] [IsLocalRing A] : ℝ :=
  Filter.limUnder Filter.atTop (normalizedColength A)
end Lech


 

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

 
structure IsShortComplex (F : CochainComplex (ModuleCat.{u} R) ℤ) : Prop where
  term_free : ∀ i, Module.Free R (F.X i)
  term_finite : ∀ i, Module.Finite R (F.X i)
  bounded : ∀ i, i < -(dimension R : ℤ) ∨ 0 < i → IsZero (F.X i)
  homology_finite_length : ∀ i, IsFiniteLength R (F.homology i)
  homology_zero_nonzero : ¬ IsZero (F.homology 0)

 

def frobeniusComplex (p : ℕ) [Fact p.Prime] [CharP R p] (n : ℕ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  ((ModuleCat.extendScalars (iterateFrobenius R p n)).mapHomologicalComplex (.up ℤ)).obj F

 
def shortEuler (F : CochainComplex (ModuleCat.{u} R) ℤ) : ℝ :=
  ∑ i∈Finset.range (dimension R+1),(-1:ℝ)^i*
    ((Module.length R (F.homology (-(i:ℤ)))).toNat : ℝ)

def duttaSequence (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) : ℝ :=
  (p:ℝ)^(-(n*dimension R : ℤ)) * shortEuler R (frobeniusComplex R p n F)

def duttaMultiplicity (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) : ℝ :=
  limUnder atTop (duttaSequence R p F)

 

def DuttaDomainClaim : Prop :=
  ∀ (D : Type u) [CommRing D] [IsNoetherianRing D] [IsLocalRing D] [IsDomain D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    (F : CochainComplex (ModuleCat.{u} D) ℤ), IsShortComplex D F →
      (∀ n i,IsFiniteLength D ((frobeniusComplex D p n F).homology i)) ∧
      Tendsto (duttaSequence D p F) atTop (𝓝 (duttaMultiplicity D p F)) ∧
      multiplicity D ≤ duttaMultiplicity D p F
end Lech

namespace Lech
universe u


end Lech
end
end
end OAI


