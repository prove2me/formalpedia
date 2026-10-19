-- Prove2me | Definitions.Def_OAIE3v2B127
-- name    : OAIE3v2B127
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:55:02.240985+00:00
-- url     : https://prove2.me/theorems/b69d56fa-2999-42dc-8fb1-c086ba37d456
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 129 of 311
-- statement:
--   Definitions bundle 129 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B100`, `OAIE3v2B101`, `OAIE3v2B103`, `OAIE3v2B104`, `OAIE3v2B105`, `OAIE3v2B111` of this split.
--
--   Modules: `Estimates/PinnedSectionMeans.lean`, `Estimates/RealOrderedSlots.lean`, `Geometry/ControlledIntegralCoordinates.lean`, `Lattices/AllocatedSupportedSlicedResidue.lean`, `Lattices/PrincipalResidueMixture.lean`, `Lattices/SmoothResidueWindowMass.lean`, `Linear/KernelPrincipalFiberSliceLaw.lean`, `Probability/ObservedDensityTesting.lean`, `Sampling/RationalForecastGridTail.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B103
import Definitions.Def_OAIE3v2B104
import Definitions.Def_OAIE3v2B105
import Definitions.Def_OAIE3v2B111

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

def refinedColumnExtraResidue {K I : Type*} (modulus : I → ℕ) (q : ℕ)
    (r : ColumnResiduePattern K I (fun i => modulus i * q)) : K × I → ZMod q :=
  columnResidueReduction (fun _ => q) (fun i => modulus i * q)
    (fun i => dvd_mul_left q (modulus i)) r

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PinnedSectionMeans
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productNormalizedSection (T A : Finset I) (z : ∀ i, X i)
    (K : ℝ) (f : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (K ^ A.card)⁻¹ * productSectionAverage μ T A z f x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledIntegralCoordinates
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def realIntegralOrderedBasisProduct (B : ℕ) (z : Fin d → ℤ) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) :=
  realOrderedBasisProduct (e.baseChange ℝ) (realification_lowerCentralSeries_eq_bot hnil)
    (fun j => (B : ℝ) * (z j : ℝ))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealOrderedSlots
namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] {d s : ℕ}
  (e : Basis (Fin d) ℝ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def realOrderedSlots (B : ℝ) (a : NilpotentLieBCHGroup L s hnil) :
    TriangularSlots d where
  center x j := -e.repr (a * realOrderedBasisPrefixProduct e hnil j.val
    (fun k => B * x k)).coord j / B
  lower j x y h := by
    have hp : realOrderedBasisPrefixProduct e hnil j.val (fun k => B * x k) =
        realOrderedBasisPrefixProduct e hnil j.val (fun k => B * y k) := by
      apply realOrderedBasisPrefixProduct_congr
      intro k hk
      rw [h k hk]
    rw [hp]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem principalResidueCell_mass_pos {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) (hm : 0 < m)
    (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) :
    0 < (principalTupleWeights (α := α) B h L hL).mass
      (Finset.univ.filter (fun y => principalResidueLabel m y = r)) := by
  rw [principalResidueCell_eq]
  exact FiniteProbabilityWeights.piRestriction_mass_pos _ _
    (fun j => scalarCubeResidue_mass_pos α (L j) m (hL j) (fun _ => m) (r j)
      (fun _ => hm) (fun _ => le_rfl) (hsize j))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalForecastGridTail
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {Ω O : Type*} [Fintype Ω] [Fintype O] [DecidableEq O]

noncomputable def rationalOutputOrderTail
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    (T : ℕ) (b : O → ZMod N) : ℂ :=
  (rationalOutputDensity p Y N b : ℂ) -
    ∑ χ ∈ Finset.univ.filter (fun χ : AddChar (O → ZMod N) ℂ => orderOf χ ≤ T),
      finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ * star (χ b)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

variable {D : Type*} [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (H : PrincipalTupleIndex B h → ℕ) (hH : ∀ j, 0 < H j)

def principalFinTuplePoint (t : ∀ j, Fin (H j)) : PrincipalIntegerTuples B h Empty H :=
  fun j => zeroScalarFinPoint (H j) (t j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelPrincipalFiberSliceLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G D : Type*} [Fintype G] [DecidableEq G] [Fintype D] [DecidableEq D]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (LG : G → ℕ) (L : PrincipalTupleIndex B h → ℕ)

def kernelZeroTupleFromSumIntegerBox
    (z : integerBox (Sum.elim LG L)) : ∀ g, IntegerScalarCubeBox Empty (LG g) :=
  fun g _ => ⟨z.val (Sum.inl g), Finset.mem_Ico.mpr
    ⟨(neg_nonpos.mpr (Int.natCast_nonneg _)).trans
      ((mem_integerBox (Sum.elim LG L) z.val).mp z.property (Sum.inl g)).1,
      ((mem_integerBox (Sum.elim LG L) z.val).mp z.property (Sum.inl g)).2⟩⟩

def principalZeroTupleFromSumIntegerBox
    (z : integerBox (Sum.elim LG L)) : PrincipalIntegerTuples B h Empty L :=
  fun j _ => ⟨z.val (Sum.inr j), Finset.mem_Ico.mpr
    ⟨(neg_nonpos.mpr (Int.natCast_nonneg _)).trans
      ((mem_integerBox (Sum.elim LG L) z.val).mp z.property (Sum.inr j)).1,
      ((mem_integerBox (Sum.elim LG L) z.val).mp z.property (Sum.inr j)).2⟩⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ObservedDensityTesting
namespace OAI

section

namespace Erdos3

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

noncomputable def productSectionDensityWeight (T A : Finset I) (z : ∀ i, X i)
    (rho F : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  productSectionAverage μ T A z (fun y => rho y * F y) x /
    productSectionAverage μ T A z rho x

noncomputable def productNormalizedSectionWeight (T A : Finset I) (z : ∀ i, X i)
    (K : ℝ) (rho F : (∀ i, X i) → ℝ) (x : ∀ i, X i) : ℝ :=
  (K ^ A.card)⁻¹ * productSectionDensityWeight μ T A z rho F x

end Erdos3

end

end OAI
end


