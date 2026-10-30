-- Prove2me | Definitions.Def_OAIQ095D000
-- name    : OAIQ095D000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:56:54.494052+00:00
-- url     : https://prove2.me/theorems/08287582-85fb-4f43-ba5b-a3ec5250560c
-- title:
--   Definitions bundle OAIQ095D000 of the split of OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 329 declarations of OpenAI's Lean: 86 definitions, 5 inductive types or structures, 2 instances and 236 theorems. The definitions and types are `BernoulliRegular.characterIndexEquiv`, `BernoulliRegular.complexCharacterMulEquivUnits`, `BernoulliRegular.constOneDirichletCharacterFamily`, `BernoulliRegular.deltaZeroConstOneDirichletCharacterBasis`, `BernoulliRegular.deltaZeroConstOneDirichletCharacterFamily`, `BernoulliRegular.deltaZeroFunction`, `BernoulliRegular.dirichletCharacterUnitMonoidHom`, `BernoulliRegular.evalAtZeroLinear`, `BernoulliRegular.evenNonselfdualCharacterFinset`, `BernoulliRegular.evenNonselfdualCharacterReps`, `BernoulliRegular.fourierBaseRoot`, `BernoulliRegular.fourierCyclotomicDifferenceProduct`, `BernoulliRegular.fourierCyclotomicSingleDifferenceProduct`, `BernoulliRegular.fourierMatrix`, `BernoulliRegular.fourierMatrixFin`, `BernoulliRegular.fourierVandermonde`, `BernoulliRegular.fourierVandermondeNodes`, `BernoulliRegular.fourierVandermondeProduct`, `BernoulliRegular.instDecidableEqDirichletCharacterComplex_solutions`, `BernoulliRegular.instDecidableEqOptionDirichletCharacterComplex_solutions`, `BernoulliRegular.nonselfdualCharacterFinset`, `BernoulliRegular.nonselfdualCharacterReps`, `BernoulliRegular.normalizedDft`, `BernoulliRegular.normalizedDftConstOneBasisPerm`, `BernoulliRegular.normalizedDftConstOneBasisPermFun`, `BernoulliRegular.normalizedDftConstOneBasisScalar`, `BernoulliRegular.normalizedFourierMatrix`, `BernoulliRegular.normalizedFourierMatrixFin`, `BernoulliRegular.quadraticCharComplex`, `BernoulliRegular.restrictUnitsLinear`, `BernoulliRegular.zmodEquivFin`, `Complex.logGammaSeq`, `OAI.LargePrimeGaps.PrimePowerEq`, `OAI.LargePrimeGaps.biquadraticCoefficients`, `OAI.LargePrimeGaps.discrepancyTail`, `OAI.LargePrimeGaps.positiveCoefficients`, `OAI.LargePrimeGaps.productCharacter`, `OAI.LargePrimeGaps.regularSeries`, `OAI.LargePrimeGaps.regularizedZetaProduct`, `OAI.LargePrimeGaps.seriesDiscrepancy` and 51 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `Characters`, `GaussSum_Basic`, `GaussSum_SignInvariant_BlockDecomposition`, `GaussSum_SignInvariant_BlockDeterminant`, `GaussSum_SignInvariant_BranchChoice`, `GaussSum_SignInvariant_Operator`, `GaussSum_SignInvariant_Trace`, `GaussSum_SignInvariant_Vandermonde`, `Mathlib_Algebra_Order_Floor_Ring`, `Mathlib_Analysis_Complex_Basic`, `Mathlib_Analysis_Complex_Convex`, `Mathlib_Analysis_SpecialFunctions_Gamma_DigammaSeries`, `Mathlib_Analysis_SpecialFunctions_Pow_Deriv`, `Mathlib_MeasureTheory_Integral_IntegrableOn`, `Mathlib_NumberTheory_AbelSummation`, `Ostmann_Characters_CharacterCompletedDiskGrowth`, `Ostmann_Characters_CharacterCompletedDivergence`, `Ostmann_Characters_CharacterCompletedFiniteBound`, `Ostmann_Characters_CharacterCompletedFiniteFactors`, `Ostmann_Characters_CharacterCompletedLogDerivative`, `Ostmann_Characters_CharacterCompletedLogGrowth`, `Ostmann_Characters_CharacterCompletedRightGrowth`, `Ostmann_Characters_CharacterDiskIndices`, `Ostmann_Characters_CharacterEnumerationCount`, `Ostmann_Characters_CharacterFaithfulEnumeration`, `Ostmann_Characters_CharacterFunctionalEquation`, `Ostmann_Characters_CharacterMellinBound`, `Ostmann_Characters_CharacterMellinIntegral`, `Ostmann_Characters_CharacterPartialSum`, `Ostmann_Characters_CharacterRightHalfPlane`, `Ostmann_Characters_CharacterRightLogDerivativeBound`, `Ostmann_Characters_CharacterRootNumberBound`, `Ostmann_Characters_PrimitiveCharacterLifts`, `Ostmann_Quadratic_QuadraticCharacterReal`, `Ostmann_ZeroDensity_ActualRealZeroExpansion`, `Ostmann_ZeroDensity_AnalyticLogBall`, `Ostmann_ZeroDensity_CharacterCompletedZeros`, `Ostmann_ZeroDensity_CharacterContourZeros`, `Ostmann_ZeroDensity_CharacterFullZeroCount`, `Ostmann_ZeroDensity_CharacterGammaFactorialGrowth`, `Ostmann_ZeroDensity_CharacterGammaGrowthSequence`, `Ostmann_ZeroDensity_CharacterGammaRealBound`, `Ostmann_ZeroDensity_CharacterHadamardBounds`, `Ostmann_ZeroDensity_CharacterLocalZeroCount`, `Ostmann_ZeroDensity_CharacterRightZeroCount`, `Ostmann_ZeroDensity_CharacterZeroCopies`, `Ostmann_ZeroDensity_CharacterZeroCountRate`, `Ostmann_ZeroDensity_CharacterZeroCover`, `Ostmann_ZeroDensity_CharacterZeroInverseSquare`, `Ostmann_ZeroDensity_CharacterZeroMultiplicity`, `Ostmann_ZeroDensity_CharacterZeroPartialSums`, `Ostmann_ZeroDensity_CharacterZeroReflection`, `Ostmann_ZeroDensity_CharacterZeroSet`, `Ostmann_ZeroDensity_CharacterZerosInfinite`, `Ostmann_ZeroDensity_CompletedCharacterConjugation`, `Ostmann_ZeroDensity_CompletedDiskGrowthRate`, `Ostmann_ZeroDensity_CompletedDiskZeros`, `Ostmann_ZeroDensity_CompletedFiniteLogDerivative`, `Ostmann_ZeroDensity_CompletedPartialFractionLimit`, `Ostmann_ZeroDensity_CompletedQuotientGrowth`, `Ostmann_ZeroDensity_ComplexCharacterConjugation`, `Ostmann_ZeroDensity_ComplexCharacterHadamard`, `Ostmann_ZeroDensity_FiniteAnalyticZeroFactors`, `Ostmann_ZeroDensity_FiniteInverseSquareDensity`, `Ostmann_ZeroDensity_FiniteZeroLogDerivative`, `Ostmann_ZeroDensity_FiniteZeroPolynomialLogDerivative`, `Ostmann_ZeroDensity_FiniteZeroQuotientDisk`, `Ostmann_ZeroDensity_FiniteZeroQuotientGrowth`, `Ostmann_ZeroDensity_FiniteZeroQuotientNormalized`, `Ostmann_ZeroDensity_FullHeightRegionComparison`, `Ostmann_ZeroDensity_GammaFactorialGrowth`, `Ostmann_ZeroDensity_GammaLogDerivativeGrowth`, `Ostmann_ZeroDensity_GammaRealContourBound`, `Ostmann_ZeroDensity_GammaRealLogDerivative`, `Ostmann_ZeroDensity_GammaStripBound`, `Ostmann_ZeroDensity_ImprimitiveEulerBound`, `Ostmann_ZeroDensity_InverseSquareZeroSum`, `Ostmann_ZeroDensity_LogDerivativeDiskOscillation`, `Ostmann_ZeroDensity_LogDerivativeInnerSecondBound`, `Ostmann_ZeroDensity_LogDerivativeSecondBound`, `Ostmann_ZeroDensity_LogDerivativeVanishing`, `Ostmann_ZeroDensity_LogarithmicDiskRate`, `Ostmann_ZeroDensity_LogarithmicGammaBound`, `Ostmann_ZeroDensity_LowHeightArchimedean`, `Ostmann_ZeroDensity_LowHeightZeroBounds`, `Ostmann_ZeroDensity_PublishedComplexZeroDensity`, `Ostmann_ZeroDensity_PublishedProgressionInputs`, `Ostmann_ZeroDensity_PublishedRealZeros`, `Ostmann_ZeroDensity_RealCharacterComplexification`, `Ostmann_ZeroDensity_RealCharacterReflection`, `Ostmann_ZeroDensity_RealCharacterZeroConvergence`, `Ostmann_ZeroDensity_RealCompletedHadamard`, `Ostmann_ZeroDensity_RealZeroKernel`, `Ostmann_ZeroDensity_RealZeroReflectionPermutation`, `Ostmann_ZeroDensity_RealZeroSum`, `Ostmann_ZeroDensity_ShiftedRealHadamard`, `Ostmann_ZeroDensity_SmoothDirichletIntegral`, `Ostmann_ZeroDensity_SmoothTruncatedContour`, `Ostmann_ZeroDensity_SmoothVerticalKernel`, `PrimeGaps_DirichletGrowth`, `PrimeGaps_EqualityPatterns`, `PrimeGaps_PatternMoments`, `PrimeGaps_SiegelBounds`, `PrimeGaps_TaylorBounds`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ095D003`, `OAIQ095D004` and `OAIQ095D005`; the statement `OAI.Ostmann.density_packed_product_fourth`.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ095_OS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ095_OS.Characters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Characters of `Gal(ℚ(ζ_p)/ℚ)` — Teichmüller character

Let `p` be a prime. The Teichmüller character `ω : ZMod p →*₀ ℤ_[p]`
sends each nonzero residue class `a ∈ (ZMod p)ˣ` to the unique `(p-1)`-th
root of unity in `ℤ_[p]` that reduces to `a` modulo `p`, and sends the
zero residue class to `0`.

The construction reuses mathlib's `Perfection.teichmuller₀`: since the
residue field `ℤ_[p] ⧸ maximalIdeal ℤ_[p]` is canonically isomorphic to
`ZMod p`, which is perfect (finite of characteristic `p`), `ZMod p` is
identified with the perfection, after which the generic Teichmüller map
lands in `ℤ_[p]`.

## Main definitions

- `BernoulliRegular.teichmuller` — `ω : ZMod p →*₀ ℤ_[p]`.

## Main results

- `toZMod_teichmuller` — `ω(a) ≡ a (mod p)`.
- `teichmuller_pow_sub_one` — `ω(a)^{p-1} = 1` for `a ≠ 0`.
- The `MonoidWithZeroHom` structure is provided by the bundled
  definition, so `teichmuller_zero`, `teichmuller_one`,
  `teichmuller_mul` follow.

## References

- Diekmann, *FLT for regular primes* (2023), Lemma 20.
- Washington, *Introduction to Cyclotomic Fields*, §5.1.
-/


noncomputable section

open PadicInt IsLocalRing

namespace BernoulliRegular

variable (p : ℕ) [hp : Fact p.Prime]

/-! ### Instances on `ℤ_[p] ⧸ maximalIdeal ℤ_[p]`

We need `CharP _ p`, `Finite`, and `PerfectRing _ p` on the raw
quotient ring to feed into `Perfection.teichmuller₀`. All three propagate
across the canonical ring equivalence with `ZMod p` (mathlib's
`PadicInt.residueField` has codomain `IsLocalRing.ResidueField ℤ_[p]`,
which is definitionally the quotient; we rebuild it explicitly to avoid
typeclass-resolution friction through that wrapper). -/

/-! ### Teichmüller character via `Perfection.teichmuller₀` -/

variable {p}

/-! ### The Teichmüller character as a Dirichlet character -/

/-! ### Primitive `(p-1)`-th root of unity and
`HasEnoughRootsOfUnity` instance -/

instance instNeZeroNatHSubOfNat_solutions : NeZero (p - 1) := ⟨by have := hp.1.two_le; omega⟩

/-! ### T002: the character group is cyclic of order `p - 1` -/

/-! ### T004 — Character sum identity (Diekmann Lemma 24) -/

/-! ### T003 — Character parity (Diekmann Lemmas 23, 25) -/

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_Basic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Gauss sums for Dirichlet characters modulo a prime

Thin wrapper around mathlib's `gaussSum` specialised to Dirichlet characters
modulo a prime `p`, using the standard additive character
`ZMod.stdAddChar`.

## Main results

* `BernoulliRegular.gaussSum_one_stdAddChar`: the Gauss sum of the trivial
  Dirichlet character modulo a prime `p` with the standard additive character
  equals `-1`.
* `BernoulliRegular.gaussSum_mul_gaussSum_inv_stdAddChar`: for a non-trivial
  Dirichlet character `χ` modulo a prime `p`,
  `τ(χ) · τ(χ̄) = χ(-1) · p`.
* `BernoulliRegular.DirichletCharacter.isPrimitive_of_prime_of_ne_one`: for
  `p` prime, every non-trivial Dirichlet character mod `p` is primitive.
* `BernoulliRegular.gaussSum_stdAddChar_mulShift`: the key Galois-equivariance
  identity for the Gauss sum: for nontrivial `χ` mod prime `p` and `a : ZMod p`,
  `gaussSum χ (stdAddChar.mulShift a) = χ⁻¹ a · gaussSum χ stdAddChar`.
* `BernoulliRegular.isIntegral_gaussSum_stdAddChar`: the Gauss sum
  `τ(χ) = gaussSum χ ZMod.stdAddChar` is an algebraic integer — integral over `ℤ`
  as an element of `ℂ`.
-/


noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section GaussSum

variable (p : ℕ) [hp : Fact p.Prime]

/-- **T023d1a**: The quadratic Dirichlet character modulo `p`, viewed as
`ℂ`-valued so it can be paired with `ZMod.stdAddChar` in Gauss sums. -/
noncomputable def quadraticCharComplex : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

end GaussSum

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_Trace
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite-Fourier sign invariants for quadratic Gauss sums

This file contains the trace and character-cancellation side of the
finite-Fourier sign-invariant package.
-/


noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

/-- A chosen multiplicative equivalence between complex-valued Dirichlet
characters mod `p` and the unit group `(ZMod p)ˣ`. -/
noncomputable def complexCharacterMulEquivUnits : DirichletCharacter ℂ p ≃* (ZMod p)ˣ := by
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  exact (MulChar.mulEquiv_units (ZMod p) ℂ).some

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_Operator
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite-Fourier sign invariants for quadratic Gauss sums

This file contains the operator-theoretic and matrix-reduction part of the
finite-Fourier sign-invariant package.
-/


noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

/-- The DFT scaled by `1 / √p`, so that its square is pullback by negation. -/
noncomputable def normalizedDft : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ) :=
  ((Real.sqrt p : ℂ)⁻¹) •
    ((ZMod.dft : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ)).toLinearMap)

/-- The raw Fourier kernel matrix for `ZMod.dft` in the standard basis. -/
noncomputable def fourierMatrix : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun x k ↦ ZMod.stdAddChar (N := p) (-(x * k))

/-- The normalized Fourier matrix, i.e. the matrix of `normalizedDft`. -/
noncomputable def normalizedFourierMatrix : Matrix (ZMod p) (ZMod p) ℂ :=
  Matrix.of fun x k ↦ (Real.sqrt p : ℂ)⁻¹ * ZMod.stdAddChar (N := p) (-(x * k))

/-- A fixed equivalence used to reindex `ZMod p` by `Fin p` for matrix
determinant computations. -/
noncomputable def zmodEquivFin : ZMod p ≃ Fin p :=
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  (ZMod.finEquiv p).symm.toEquiv

/-- The normalized Fourier matrix reindexed by `Fin p`. -/
noncomputable def normalizedFourierMatrixFin : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.reindex (zmodEquivFin (p := p)) (zmodEquivFin (p := p)) (normalizedFourierMatrix p)

/-- The raw Fourier matrix reindexed by `Fin p`. -/
noncomputable def fourierMatrixFin : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.reindex (zmodEquivFin (p := p)) (zmodEquivFin (p := p)) (fourierMatrix p)

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_BlockDecomposition
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Determinant-ready block decomposition scaffolding for quadratic Gauss sums

This file packages the ambient `δ₀ +` character basis used to reorganize the
normalized finite Fourier transform into the trivial block, non-self-dual
character-pair blocks, and the surviving quadratic line.
-/


noncomputable section

namespace BernoulliRegular

section SignInvariant

open scoped BigOperators ComplexConjugate

variable (p : ℕ) [hp : Fact p.Prime]

/-- The delta function supported at `0`. -/
def deltaZeroFunction : ZMod p → ℂ :=
  Pi.basisFun ℂ (ZMod p) (0 : ZMod p)

/-- Restrict a function on `ZMod p` to the unit group. -/
def restrictUnitsLinear : (ZMod p → ℂ) →ₗ[ℂ] ((ZMod p)ˣ → ℂ) where
  toFun Φ u := Φ u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- View a Dirichlet character as a monoid homomorphism on the unit group with
values in `ℂ`. -/
def dirichletCharacterUnitMonoidHom (χ : DirichletCharacter ℂ p) : (ZMod p)ˣ →* ℂ :=
  (Units.coeHom ℂ).comp χ.toUnitHom

/-- Evaluating that monoid hom is evaluating the character. -/
@[simp] theorem dirichletCharacterUnitMonoidHom_apply
    (χ : DirichletCharacter ℂ p) (u : (ZMod p)ˣ) :
    dirichletCharacterUnitMonoidHom (p := p) χ u = χ u := by
  simp [dirichletCharacterUnitMonoidHom]

/-- A Dirichlet character is determined by its restriction to the unit group. -/
theorem dirichletCharacterUnitMonoidHom_injective :
    Function.Injective (dirichletCharacterUnitMonoidHom (p := p)) := by
  intro χ ψ hχψ
  apply (DirichletCharacter.toUnitHom_inj (χ := χ) (ψ := ψ)).mp
  ext u
  have hcoe : ((χ.toUnitHom u : ℂˣ) : ℂ) = ((ψ.toUnitHom u : ℂˣ) : ℂ) :=
    DFunLike.congr_fun hχψ u
  exact hcoe

/-- Dirichlet characters are linearly independent on the unit group. -/
theorem linearIndependent_dirichletCharactersOnUnits :
    LinearIndependent ℂ (fun χ : DirichletCharacter ℂ p =>
      (dirichletCharacterUnitMonoidHom (p := p) χ : (ZMod p)ˣ → ℂ)) :=
  (linearIndependent_monoidHom ((ZMod p)ˣ) ℂ).comp
      (dirichletCharacterUnitMonoidHom (p := p))
      (dirichletCharacterUnitMonoidHom_injective (p := p))

/-- Evaluation at `0`. -/
def evalAtZeroLinear : (ZMod p → ℂ) →ₗ[ℂ] ℂ where
  toFun Φ := Φ 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A Dirichlet character vanishes at `0`. -/
@[simp] theorem dirichletCharacter_apply_zero (χ : DirichletCharacter ℂ p) :
    χ (0 : ZMod p) = 0 :=
  χ.map_zero

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_BlockDeterminant
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Determinant bookkeeping for the block decomposition

This file reorganizes the `δ₀ +` character basis so that the normalized DFT is
monomial outside the surviving quadratic line. This packages the determinant
contribution of the trivial block and prepares the remaining non-self-dual
character-pair bookkeeping.
-/


noncomputable section

namespace BernoulliRegular

section SignInvariant

open scoped BigOperators ComplexConjugate

variable (p : ℕ) [hp : Fact p.Prime]

local instance instDecidableEqDirichletCharacterComplex_solutions : DecidableEq (DirichletCharacter ℂ p) := Classical.decEq _
local instance instDecidableEqOptionDirichletCharacterComplex_solutions : DecidableEq (Option (DirichletCharacter ℂ p)) := Classical.decEq _

/-- Replace the trivial Dirichlet character by the constant-`1` function, but
leave every other character unchanged. -/
def constOneDirichletCharacterFamily (χ : DirichletCharacter ℂ p) : ZMod p → ℂ :=
  by
    classical
    exact if hχ : χ = 1 then fun _ : ZMod p ↦ (1 : ℂ) else (χ : ZMod p → ℂ)

omit hp in
@[simp] theorem constOneDirichletCharacterFamily_one :
    constOneDirichletCharacterFamily (p := p) (1 : DirichletCharacter ℂ p) =
      (fun _ : ZMod p ↦ (1 : ℂ)) := by
  classical
  rw [constOneDirichletCharacterFamily]
  simp

omit hp in
/-- Away from the trivial character, the modified family is the character itself. -/
theorem constOneDirichletCharacterFamily_eq_character {χ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) :
    constOneDirichletCharacterFamily (p := p) χ = (χ : ZMod p → ℂ) := by
  classical
  rw [constOneDirichletCharacterFamily]
  simp [hχ]

@[simp] theorem restrictUnits_deltaZero :
    restrictUnitsLinear (p := p) (deltaZeroFunction (p := p)) = 0 := by
  ext u
  have hu : ((u : (ZMod p)) ≠ 0) := Units.ne_zero u
  simp [restrictUnitsLinear, deltaZeroFunction, hu]

@[simp] theorem restrictUnits_constOneDirichletCharacterFamily
    (χ : DirichletCharacter ℂ p) :
    restrictUnitsLinear (p := p) (constOneDirichletCharacterFamily (p := p) χ) =
      (dirichletCharacterUnitMonoidHom (p := p) χ : (ZMod p)ˣ → ℂ) := by
  classical
  by_cases hχ : χ = 1
  · subst hχ
    ext u
    rw [constOneDirichletCharacterFamily_one (p := p)]
    simp [restrictUnitsLinear, dirichletCharacterUnitMonoidHom]
  · ext u
    rw [constOneDirichletCharacterFamily_eq_character (p := p) hχ]
    simp [restrictUnitsLinear, dirichletCharacterUnitMonoidHom]

/-- The characters remain linearly independent after replacing the trivial
character by the constant-`1` function. -/
theorem linearIndependent_constOneDirichletCharacterFamily :
    LinearIndependent ℂ (constOneDirichletCharacterFamily (p := p)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha χ
  have h_units :
      ∑ ψ, a ψ • (dirichletCharacterUnitMonoidHom (p := p) ψ : (ZMod p)ˣ → ℂ) = 0 := by
    simpa using congrArg (restrictUnitsLinear (p := p)) ha
  exact
    (Fintype.linearIndependent_iff.mp
      (linearIndependent_dirichletCharactersOnUnits (p := p))) a h_units χ

/-- `δ₀` is not in the span of the modified character family. -/
theorem deltaZero_not_mem_span_constOneDirichletCharacterFamily :
    deltaZeroFunction (p := p) ∉
      Submodule.span ℂ
        (Set.range fun χ : DirichletCharacter ℂ p ↦
          constOneDirichletCharacterFamily (p := p) χ) := by
  intro hdelta
  obtain ⟨a, ha⟩ :=
    (Submodule.mem_span_range_iff_exists_fun
      (R := ℂ)
      (v := fun χ : DirichletCharacter ℂ p ↦
        constOneDirichletCharacterFamily (p := p) χ)).mp hdelta
  have h_units :
      ∑ χ, a χ • (dirichletCharacterUnitMonoidHom (p := p) χ : (ZMod p)ˣ → ℂ) = 0 := by
    simpa using congrArg (restrictUnitsLinear (p := p)) ha
  have ha_zero : ∀ χ : DirichletCharacter ℂ p, a χ = 0 :=
    (Fintype.linearIndependent_iff.mp
      (linearIndependent_dirichletCharactersOnUnits (p := p))) a h_units
  have hone : (1 : ℂ) = 0 := by
    simpa [evalAtZeroLinear, deltaZeroFunction, constOneDirichletCharacterFamily,
      dirichletCharacter_apply_zero, ha_zero] using
      congrArg (evalAtZeroLinear (p := p)) ha
  exact one_ne_zero hone

/-- The ambient family for determinant computations: `δ₀`, the constant-`1`
function, and all nontrivial Dirichlet characters. -/
def deltaZeroConstOneDirichletCharacterFamily :
    Option (DirichletCharacter ℂ p) → (ZMod p → ℂ) :=
  fun o ↦ Option.casesOn' o (deltaZeroFunction (p := p))
    (constOneDirichletCharacterFamily (p := p))

/-- Adjoining `δ₀` to the modified family keeps it linearly independent. -/
theorem linearIndependent_deltaZeroConstOneDirichletCharacterFamily :
    LinearIndependent ℂ (deltaZeroConstOneDirichletCharacterFamily (p := p)) := by
  change LinearIndependent ℂ
    (fun o ↦ Option.casesOn' o (deltaZeroFunction (p := p))
      (constOneDirichletCharacterFamily (p := p)))
  exact (linearIndependent_constOneDirichletCharacterFamily (p := p)).option
      (x := deltaZeroFunction (p := p))
      (deltaZero_not_mem_span_constOneDirichletCharacterFamily (p := p))

/-- A basis adapted to the trivial `δ₀/1` block: `δ₀`, the constant-`1`
function, and all nontrivial Dirichlet characters. -/
def deltaZeroConstOneDirichletCharacterBasis :
    Module.Basis (Option (DirichletCharacter ℂ p)) ℂ (ZMod p → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_deltaZeroConstOneDirichletCharacterFamily (p := p)) <| by
      rw [Fintype.card_option, ← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity (R := ℂ) (n := p),
        Nat.totient_prime hp.out]
      rw [Module.finrank_fintype_fun_eq_card, ZMod.card]
      exact Nat.sub_add_cancel hp.out.one_le

@[simp] theorem deltaZeroConstOneDirichletCharacterBasis_apply_none :
    deltaZeroConstOneDirichletCharacterBasis (p := p) none = deltaZeroFunction (p := p) := by
  rw [deltaZeroConstOneDirichletCharacterBasis,
    coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

@[simp] theorem deltaZeroConstOneDirichletCharacterBasis_apply_some
    (χ : DirichletCharacter ℂ p) :
    deltaZeroConstOneDirichletCharacterBasis (p := p) (some χ) =
      constOneDirichletCharacterFamily (p := p) χ := by
  rw [deltaZeroConstOneDirichletCharacterBasis,
    coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

@[simp] theorem deltaZeroConstOneDirichletCharacterBasis_apply_some_one :
    deltaZeroConstOneDirichletCharacterBasis (p := p)
        (some (1 : DirichletCharacter ℂ p)) =
      (fun _ : ZMod p ↦ (1 : ℂ)) := by
  simp [deltaZeroConstOneDirichletCharacterBasis_apply_some, constOneDirichletCharacterFamily_one]

/-- The underlying involution on the adapted basis indices. -/
def normalizedDftConstOneBasisPermFun :
    Option (DirichletCharacter ℂ p) → Option (DirichletCharacter ℂ p) :=
  by
    classical
    exact fun
      | none => some 1
      | some χ => if hχ : χ = 1 then none else some χ⁻¹

/-- The permutation of the adapted basis induced by the normalized DFT. -/
def normalizedDftConstOneBasisPerm :
    Equiv.Perm (Option (DirichletCharacter ℂ p)) where
  toFun := normalizedDftConstOneBasisPermFun (p := p)
  invFun := normalizedDftConstOneBasisPermFun (p := p)
  left_inv := by
    classical
    intro i
    cases i with
    | none =>
        simp [normalizedDftConstOneBasisPermFun]
    | some χ =>
        by_cases hχ : χ = 1
        · subst hχ
          simp [normalizedDftConstOneBasisPermFun]
        · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := inv_ne_one.2 hχ
          simp [normalizedDftConstOneBasisPermFun, hχ, hχinv]
  right_inv := by
    classical
    intro i
    cases i with
    | none =>
        simp [normalizedDftConstOneBasisPermFun]
    | some χ =>
        by_cases hχ : χ = 1
        · subst hχ
          simp [normalizedDftConstOneBasisPermFun]
        · have hχinv : χ⁻¹ ≠ (1 : DirichletCharacter ℂ p) := inv_ne_one.2 hχ
          simp [normalizedDftConstOneBasisPermFun, hχ, hχinv]

/-- The scalar attached to each basis vector under the normalized DFT. -/
def normalizedDftConstOneBasisScalar (i : Option (DirichletCharacter ℂ p)) : ℂ :=
  by
    classical
    exact match i with
    | none => (Real.sqrt p : ℂ)⁻¹
    | some χ =>
        if hχ : χ = 1 then ((Real.sqrt p : ℂ)⁻¹) * p
        else ((Real.sqrt p : ℂ)⁻¹) *
          (χ⁻¹ (-1) * gaussSum χ (ZMod.stdAddChar (N := p)))

/-- The nontrivial characters other than the quadratic character. For `p ≠ 2`,
these are exactly the non-self-dual characters. -/
def nonselfdualCharacterFinset : Finset (DirichletCharacter ℂ p) :=
  (Finset.univ.erase (1 : DirichletCharacter ℂ p)).erase (quadraticCharComplex p)

/-- A chosen indexing of Dirichlet characters by `Fin`, used to pick one
representative from each inverse-pair orbit. -/
noncomputable def characterIndexEquiv :
    DirichletCharacter ℂ p ≃ Fin (Fintype.card (DirichletCharacter ℂ p)) :=
  Fintype.equivFin (DirichletCharacter ℂ p)

/-- One representative from each non-self-dual inverse pair, chosen by the
fixed `Fin`-indexing on characters. -/
noncomputable def nonselfdualCharacterReps :
    Finset (DirichletCharacter ℂ p) :=
  (nonselfdualCharacterFinset (p := p)).filter
    fun χ ↦ characterIndexEquiv (p := p) χ < characterIndexEquiv (p := p) χ⁻¹

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_Vandermonde
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite-Fourier sign invariants for quadratic Gauss sums

This file contains the Vandermonde and cyclotomic normalization side of the
finite-Fourier sign-invariant package.
-/


noncomputable section

namespace BernoulliRegular

open scoped BigOperators ComplexConjugate

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

/-!
## Determinant / Vandermonde scaffold for `T023d1g2b`

This section isolates the matrix-level reductions for the determinant route:

1. express `normalizedDft` as an explicit normalized Fourier matrix;
2. reindex that matrix by `Fin p`, so the remaining algebra is on a standard
   square matrix type;
3. package the Vandermonde product that should eventually evaluate the
   determinant.
-/

/-- The distinguished Fourier root whose powers enumerate the Vandermonde nodes. -/
noncomputable def fourierBaseRoot : ℂ :=
  ZMod.stdAddChar (N := p) (-(1 : ZMod p))

/-- The `p` Fourier nodes expected to appear in the Vandermonde description. -/
noncomputable def fourierVandermondeNodes : Fin p → ℂ :=
  fun i => ZMod.stdAddChar (N := p) (-((zmodEquivFin (p := p)).symm i))

/-- The candidate Vandermonde matrix for the determinant computation. -/
noncomputable def fourierVandermonde : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.vandermonde (fourierVandermondeNodes (p := p))

/-- The explicit Vandermonde product attached to the Fourier nodes. -/
noncomputable def fourierVandermondeProduct : ℂ :=
  ∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
    (fourierVandermondeNodes (p := p) j - fourierVandermondeNodes (p := p) i)

/-- The cyclotomic difference product that remains after factoring each
Vandermonde term by the lower Fourier power. -/
noncomputable def fourierCyclotomicDifferenceProduct : ℂ :=
  ∏ i : Fin p, ∏ j ∈ Finset.Ioi i,
    ((fourierBaseRoot (p := p)) ^ ((j : ℕ) - (i : ℕ)) - 1)

/-- The same cyclotomic difference product, reindexed by the single difference
`d = j - i` and grouped by multiplicity. -/
noncomputable def fourierCyclotomicSingleDifferenceProduct : ℂ :=
  ∏ d ∈ Finset.range (p - 1),
    ((fourierBaseRoot (p := p)) ^ (d + 1) - 1) ^ (p - 1 - d)

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.GaussSum_SignInvariant_BranchChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Branch choice for the quadratic Gauss sum

This file compares the determinant formula coming from the block decomposition
with the independent Vandermonde computation, and uses that comparison to fix
the quadratic Gauss-sum branch in the two mod-`4` cases.
-/


noncomputable section

namespace BernoulliRegular

section SignInvariant

variable (p : ℕ) [hp : Fact p.Prime]

attribute [local instance] Classical.decEq Classical.propDecidable

/-- The even non-self-dual characters. -/
noncomputable def evenNonselfdualCharacterFinset : Finset (DirichletCharacter ℂ p) :=
  (nonselfdualCharacterFinset (p := p)).filter fun χ => χ.Even

/-- One representative from each even non-self-dual inverse pair. -/
noncomputable def evenNonselfdualCharacterReps : Finset (DirichletCharacter ℂ p) :=
  (nonselfdualCharacterReps (p := p)).filter fun χ => χ.Even

end SignInvariant

end BernoulliRegular
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_Algebra_Order_Floor_Ring
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Floor and fractional-part estimates

Small floor-ring lemmas used by summation and Abel-continuation arguments.
-/

section

namespace Int

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [FloorRing R]

theorem fract_abs_le_one (a : R) : |fract a| ≤ 1 := by
  rw [abs_fract]
  exact (fract_lt_one a).le

end Int
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_Analysis_Complex_Basic
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Elementary complex-analysis API

Small algebraic and metric lemmas for complex half-planes and basic rational expressions.
-/

section

namespace Complex

/-- If `a < re z`, nested open balls around `z` stay in the half-plane `re · ≥ a`. -/
theorem exists_pos_radius_forall_mem_ball_re_ge {z₀ : ℂ} {a : ℝ} (ha : a < z₀.re) :
    ∃ δ > 0, ∀ (x y : ℂ), dist x z₀ < δ → dist y x < δ → a ≤ y.re := by
  set δ : ℝ := (z₀.re - a) / 2 with hδdef
  have hpos : 0 < z₀.re - a := sub_pos.mpr ha
  have hδpos : 0 < δ := by simpa [hδdef] using half_pos hpos
  refine ⟨δ, hδpos, ?_⟩
  intro x y hx hy
  have htri : dist y z₀ ≤ dist y x + dist x z₀ := dist_triangle y x z₀
  have hsumlt : dist y x + dist x z₀ < δ + δ := add_lt_add hy hx
  have hnorm_lt : ‖y - z₀‖ < δ + δ := by simpa [dist_eq_norm] using lt_of_le_of_lt htri hsumlt
  have hdeltaSum : δ + δ = z₀.re - a := by simp [hδdef, add_halves]
  have hnorm_lt_re : ‖y - z₀‖ < z₀.re - a := by simpa [hdeltaSum] using hnorm_lt
  have h_eps_lt : a < z₀.re - ‖y - z₀‖ := by
    have hsum' : a + ‖y - z₀‖ < z₀.re := by
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
        (add_lt_add_left hnorm_lt_re a)
    simpa [lt_sub_iff_add_lt] using hsum'
  have hre_lower : -‖y - z₀‖ ≤ (y - z₀).re := (abs_le.mp (abs_re_le_norm (y - z₀))).1
  have hyge : z₀.re - ‖y - z₀‖ ≤ y.re := by
    have h' : z₀.re + (-‖y - z₀‖) ≤ z₀.re + (y - z₀).re := add_le_add_right hre_lower z₀.re
    have h'' : z₀.re + (y - z₀).re = y.re := by
      simp [sub_eq_add_neg]
    simpa [sub_eq_add_neg, h''] using h'
  exact le_of_lt (lt_of_lt_of_le h_eps_lt hyge)

end Complex
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_Analysis_Complex_Convex
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Path-connected half-planes

This file proves that a right half-plane remains path-connected after removing one point.
The lemma is used to choose logarithms on punctured half-planes in complex-analysis arguments.
-/

section

namespace Complex

theorem isPathConnected_halfSpace_re_gt_diff_singleton (a : ℝ) (p : ℂ) (hp : a < p.re) :
    IsPathConnected ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) := by
  classical
  let S1 : Set ℂ := {z : ℂ | a < z.re ∧ z.im < p.im}
  let S2 : Set ℂ := {z : ℂ | a < z.re ∧ z.re < p.re}
  let S3 : Set ℂ := {z : ℂ | a < z.re ∧ p.im < z.im}
  let S4 : Set ℂ := {z : ℂ | p.re < z.re}
  have hS1conv : Convex ℝ S1 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.im < p.im} := convex_halfSpace_im_lt (r := p.im)
    simpa [S1, Set.ofPred_and] using h1.inter h2
  have hS2conv : Convex ℝ S2 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | z.re < p.re} := convex_halfSpace_re_lt (r := p.re)
    simpa [S2, Set.ofPred_and] using h1.inter h2
  have hS3conv : Convex ℝ S3 := by
    have h1 : Convex ℝ {z : ℂ | a < z.re} := convex_halfSpace_re_gt (r := a)
    have h2 : Convex ℝ {z : ℂ | p.im < z.im} := convex_halfSpace_im_gt (r := p.im)
    simpa [S3, Set.ofPred_and] using h1.inter h2
  have hS4conv : Convex ℝ S4 := by
    simpa [S4] using (convex_halfSpace_re_gt (r := p.re))
  have hS1ne : S1.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : (p.im - 1) < p.im := by linarith
    simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS2ne : S2.Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im : ℝ) * Complex.I, ?_⟩
    have h1 : a < (a + p.re) / 2 := by linarith
    have h2 : (a + p.re) / 2 < p.re := by linarith
    simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS3ne : S3.Nonempty := by
    refine ⟨((max a p.re) + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h1 : a < (max a p.re) + 1 := by
      have : a ≤ max a p.re := le_max_left _ _
      exact lt_of_le_of_lt this (by linarith)
    have h2 : p.im < (p.im + 1) := by linarith
    simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
      using And.intro h1 h2
  have hS4ne : S4.Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (0 : ℝ) * Complex.I, ?_⟩
    have : p.re < p.re + 1 := by linarith
    simp [S4, Complex.add_re]
  have hS1pc : IsPathConnected S1 := (hS1conv.isPathConnected hS1ne)
  have hS2pc : IsPathConnected S2 := (hS2conv.isPathConnected hS2ne)
  have hS3pc : IsPathConnected S3 := (hS3conv.isPathConnected hS3ne)
  have hS4pc : IsPathConnected S4 := (hS4conv.isPathConnected hS4ne)
  let A : Set ℂ := S1 ∪ S2
  let B : Set ℂ := S3 ∪ S4
  have hS1S2_int : (S1 ∩ S2).Nonempty := by
    refine ⟨((a + p.re) / 2 : ℝ) + (p.im - (1/2)) * Complex.I, ?_⟩
    have h1a : a < (a + p.re) / 2 := by linarith
    have h1b : (p.im - (1/2)) < p.im := by linarith
    have h2a : a < (a + p.re) / 2 := by linarith
    have h2b : (a + p.re) / 2 < p.re := by linarith
    constructor
    · simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1a h1b
    · simpa [S2, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h2a h2b
  have hApc : IsPathConnected A :=
    IsPathConnected.union (U := S1) (V := S2) hS1pc hS2pc (by
      rcases hS1S2_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hS3S4_int : (S3 ∩ S4).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im + 1) * Complex.I, ?_⟩
    have h3a : a < p.re + 1 := lt_trans hp (by linarith)
    have h3b : p.im < p.im + 1 := by linarith
    have h4 : p.re < p.re + 1 := by linarith
    constructor
    · simpa [S3, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h3a h3b
    · simp [S4, Complex.add_re, Complex.mul_re]
  have hBpc : IsPathConnected B :=
    IsPathConnected.union (U := S3) (V := S4) hS3pc hS4pc (by
      rcases hS3S4_int with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hABint : (A ∩ B).Nonempty := by
    refine ⟨(p.re + 1 : ℝ) + (p.im - 1) * Complex.I, ?_⟩
    constructor
    · refine Or.inl ?_
      have h1 : a < p.re + 1 := lt_trans hp (by linarith)
      have h2 : (p.im - 1) < p.im := by linarith
      simpa [S1, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        using And.intro h1 h2
    · refine Or.inr ?_
      have h4 : p.re < p.re + 1 := by linarith
      simp [S4, Complex.add_re, Complex.mul_re]
  have hUnionPC : IsPathConnected (A ∪ B) :=
    IsPathConnected.union (U := A) (V := B) hApc hBpc (by
      rcases hABint with ⟨z, hz⟩; exact ⟨z, hz⟩)
  have hcover : ({z : ℂ | a < z.re} \ ({p} : Set ℂ)) = A ∪ B := by
    ext z; constructor
    · intro hz
      rcases hz with ⟨hzH, hznot⟩
      rcases lt_trichotomy z.re p.re with hlt | heq | hgt
      · exact Or.inl (Or.inr ⟨hzH, hlt⟩)
      · rcases lt_trichotomy z.im p.im with himlt | himeq | himgt
        · exact Or.inl (Or.inl ⟨hzH, himlt⟩)
        · have hz_eq : z = p := by
            have hzdecomp : (z.re : ℂ) + (z.im : ℝ) * Complex.I = z := by simp
            have hpdecomp : (p.re : ℂ) + (p.im : ℝ) * Complex.I = p := by simp
            have : (z.re : ℂ) + (z.im : ℝ) * Complex.I = (p.re : ℂ) + (p.im : ℝ) * Complex.I := by
              simp [heq, himeq]
            simpa [hzdecomp, hpdecomp] using this
          have : z ∈ ({p} : Set ℂ) := by simp [Set.mem_singleton_iff, hz_eq]
          exact (hznot this).elim
        · exact Or.inr (Or.inl ⟨hzH, himgt⟩)
      · exact Or.inr (Or.inr hgt)
    · intro hz
      have hzH : a < z.re := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · exact hS1.1
          · exact hS2.1
        · rcases hB with hS3 | hS4
          · exact hS3.1
          · exact lt_trans hp hS4
      have hzneq : z ≠ p := by
        rcases hz with hA | hB
        · rcases hA with hS1 | hS2
          · intro h
            have : z.im = p.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS1.2
            exact lt_irrefl _ this
          · intro h
            have : z.re = p.re := by simp [h]
            exact (ne_of_lt hS2.2) this
        · rcases hB with hS3 | hS4
          · intro h
            have : p.im = z.im := by simp [h]
            have : z.im < z.im := by simpa [this] using hS3.2
            exact lt_irrefl _ this
          · intro h
            have : p.re = z.re := by simp [h]
            exact (ne_of_gt hS4) this.symm
      exact And.intro hzH (by intro hzmem; exact hzneq (by simpa [Set.mem_singleton_iff] using hzmem))
  simpa [hcover] using hUnionPC


end Complex
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_Analysis_SpecialFunctions_Gamma_DigammaSeries
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# The series representation of the digamma function

This file proves the classical series representation of the digamma function:
for `z : ℂ` avoiding the poles of `Gamma`,
`digamma z = -γ + ∑' n : ℕ, (1 / (n + 1) - 1 / (n + z))`,
where `γ` is the Euler-Mascheroni constant.

The proof goes through the Euler limit form of the Gamma function. We introduce
`Complex.logGammaSeq`, the complex analogue of `Real.BohrMollerup.logGammaSeq`, show that
it converges pointwise on the right half-plane (to a logarithm of `Gamma`, via
`Complex.GammaSeq_tendsto_Gamma`), that its derivatives converge uniformly on bounded
substrips of the half-plane, and apply `hasDerivAt_of_tendstoUniformlyOn` to identify
`digamma` with the limit of the derivatives there. The recurrence
`Complex.digamma_apply_add_one` then propagates the identity from the half-plane to the
whole domain.

## Main statements

* `Complex.hasSum_digamma`: for `z` avoiding `-ℕ`, the series
  `∑ (1 / (n + 1) - 1 / (n + z))` sums to `digamma z + γ`.
* `Complex.digamma_eq_tsum`: the same identity, written as a formula for `digamma z`.
-/

section

open Filter Topology Finset Nat

namespace Complex

/-! ## Elementary helper lemmas -/

/-- The norm of `(n : ℂ) + 1` is `n + 1`. -/
lemma norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, norm_natCast]
  push_cast
  ring

/-- The partial sums of the series `∑ 1 / (m + 1)` are the harmonic numbers. -/
lemma sum_inv_natCast_add_one (n : ℕ) :
    ∑ m ∈ Finset.range n, ((m : ℂ) + 1)⁻¹ = ((harmonic n : ℚ) : ℂ) := by
  rw [harmonic]
  push_cast
  rfl

/-- The partial sums of the series `∑ 1 / (m + 1)` are the harmonic numbers, real version. -/
lemma sum_inv_natCast_add_one_real (n : ℕ) :
    ∑ m ∈ Finset.range n, ((m : ℝ) + 1)⁻¹ = ((harmonic n : ℚ) : ℝ) := by
  rw [harmonic]
  push_cast
  rfl

/-- The summand of the digamma series, in closed form. -/
lemma inv_add_one_sub_inv_eq {z : ℂ} {m : ℕ} (hzm : z + m ≠ 0) :
    ((m : ℂ) + 1)⁻¹ - (z + m)⁻¹ = (z - 1) * (((m : ℂ) + 1) * (z + m))⁻¹ := by
  have hm : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  field_simp
  ring

/-- The Weierstrass bound for the digamma series summand on a bounded substrip of the
right half-plane. -/
lemma norm_inv_add_one_sub_inv_le {a R : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {z : ℂ}
    (hza : a ≤ z.re) (hzR : ‖z‖ ≤ R) (m : ℕ) :
    ‖((m : ℂ) + 1)⁻¹ - (z + m)⁻¹‖ ≤ (R + 1) / (a * ((m : ℝ) + 1) ^ 2) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hR0 : (0 : ℝ) ≤ R := le_trans (norm_nonneg z) hzR
  have hrepos : 0 < (z + m).re := by
    rw [add_re, natCast_re]
    linarith
  have hzm : z + m ≠ 0 := fun h => by simp [h] at hrepos
  have hnorm_zm : a * ((m : ℝ) + 1) ≤ ‖z + m‖ := by
    have h1 : (z + m).re ≤ ‖z + m‖ := re_le_norm _
    rw [add_re, natCast_re] at h1
    nlinarith
  have hz1 : ‖z - 1‖ ≤ R + 1 := le_trans (norm_sub_le z 1) (by rw [norm_one]; linarith)
  rw [inv_add_one_sub_inv_eq hzm, norm_mul, norm_inv, norm_mul, norm_natCast_add_one,
    ← div_eq_mul_inv]
  calc ‖z - 1‖ / (((m : ℝ) + 1) * ‖z + m‖)
      ≤ (R + 1) / (((m : ℝ) + 1) * (a * ((m : ℝ) + 1))) := by
        gcongr
    _ = (R + 1) / (a * ((m : ℝ) + 1) ^ 2) := by ring_nf

/-- The linear-decay bound for the digamma series summand on a right half-plane, used for
the head of the series in the growth estimate. -/
lemma norm_inv_add_one_sub_inv_le' {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {z : ℂ}
    (hza : a ≤ z.re) (m : ℕ) :
    ‖((m : ℂ) + 1)⁻¹ - (z + m)⁻¹‖ ≤ 2 / (a * ((m : ℝ) + 1)) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hnorm_zm : a * ((m : ℝ) + 1) ≤ ‖z + m‖ := by
    have h1 : (z + m).re ≤ ‖z + m‖ := re_le_norm _
    rw [add_re, natCast_re] at h1
    nlinarith
  have hinv : ((m : ℝ) + 1)⁻¹ ≤ (a * ((m : ℝ) + 1))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hinv2 : ‖z + m‖⁻¹ ≤ (a * ((m : ℝ) + 1))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hnorm_zm
  calc ‖((m : ℂ) + 1)⁻¹ - (z + m)⁻¹‖
      ≤ ‖((m : ℂ) + 1)⁻¹‖ + ‖(z + m)⁻¹‖ := norm_sub_le _ _
    _ = ((m : ℝ) + 1)⁻¹ + ‖z + m‖⁻¹ := by
        rw [norm_inv, norm_inv, norm_natCast_add_one]
    _ ≤ 2 / (a * ((m : ℝ) + 1)) := by
        rw [div_eq_mul_inv]
        linarith

/-- Summability of the comparison series `∑ 1 / (m + 1) ^ 2`. -/
lemma summable_one_div_natCast_add_one_sq :
    Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
  have h := Real.summable_one_div_nat_pow.mpr (one_lt_two : (1 : ℕ) < 2)
  exact ((summable_nat_add_iff 1).mpr h).congr fun n => by push_cast; ring

/-- A summable telescoping series whose terms tend to zero sums to its first term. -/
lemma hasSum_sub_succ_of_tendsto_zero {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [T2Space E] {a : ℕ → E} (h0 : Tendsto a atTop (𝓝 0))
    (hs : Summable fun n => a n - a (n + 1)) :
    HasSum (fun n => a n - a (n + 1)) (a 0) := by
  have h1 : Tendsto (fun n => ∑ i ∈ Finset.range n, (a i - a (i + 1))) atTop (𝓝 (a 0)) := by
    have he : ∀ n, ∑ i ∈ Finset.range n, (a i - a (i + 1)) = a 0 - a n :=
      fun n => Finset.sum_range_sub' a n
    simp only [he]
    simpa using tendsto_const_nhds.sub h0
  have h2 := hs.hasSum
  rwa [tendsto_nhds_unique h2.tendsto_sum_nat h1] at h2

/-- The tail of the series `∑ 1 / (m + 1) ^ 2` past `N` is at most `1 / N`. -/
lemma tsum_one_div_natCast_add_add_one_sq_le {N : ℕ} (hN : 1 ≤ N) :
    ∑' i : ℕ, 1 / (((i + N : ℕ) : ℝ) + 1) ^ 2 ≤ (N : ℝ)⁻¹ := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : ∀ i : ℕ, (0 : ℝ) < (i : ℝ) + N := fun i => by
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  set u : ℕ → ℝ := fun i => ((i : ℝ) + N)⁻¹ with hu_def
  have h0 : Tendsto u atTop (𝓝 0) := by
    apply Filter.Tendsto.inv_tendsto_atTop
    exact tendsto_atTop_add_const_right atTop _ tendsto_natCast_atTop_atTop
  have hdiff : ∀ i : ℕ, u i - u (i + 1) = (((i : ℝ) + N) * ((i : ℝ) + 1 + N))⁻¹ := by
    intro i
    simp only [hu_def]
    have h1 : ((i : ℝ) + N) ≠ 0 := (hpos i).ne'
    have h2 : ((i : ℝ) + 1 + N) ≠ 0 := by
      have := hpos i
      intro h
      linarith
    push_cast
    rw [inv_sub_inv h1 h2]
    have e1 : (i : ℝ) + 1 + N - ((i : ℝ) + N) = 1 := by ring
    rw [e1, one_div]
  have hsumu : Summable (fun i : ℕ => u i - u (i + 1)) := by
    apply Summable.of_nonneg_of_le (f := fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) ?_ ?_
      summable_one_div_natCast_add_one_sq
    · intro i
      rw [hdiff i]
      positivity
    · intro i
      rw [hdiff i, ← one_div]
      apply one_div_le_one_div_of_le (by positivity)
      have h3 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      nlinarith
  have htel := hasSum_sub_succ_of_tendsto_zero h0 hsumu
  have hu0 : u 0 = (N : ℝ)⁻¹ := by
    simp only [hu_def]
    norm_num
  have hsumL : Summable (fun i : ℕ => 1 / (((i + N : ℕ) : ℝ) + 1) ^ 2) :=
    (summable_nat_add_iff N).mpr summable_one_div_natCast_add_one_sq
  have hcomp : ∀ i : ℕ, 1 / (((i + N : ℕ) : ℝ) + 1) ^ 2 ≤ u i - u (i + 1) := by
    intro i
    rw [hdiff i, ← one_div]
    have h3 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have h4 : (0 : ℝ) < ((i : ℝ) + N) * ((i : ℝ) + 1 + N) := by
      have := hpos i
      nlinarith
    push_cast
    apply one_div_le_one_div_of_le h4
    nlinarith
  calc ∑' i : ℕ, 1 / (((i + N : ℕ) : ℝ) + 1) ^ 2
      ≤ ∑' i : ℕ, (u i - u (i + 1)) := hsumL.tsum_le_tsum hcomp htel.summable
    _ = u 0 := htel.tsum_eq
    _ = (N : ℝ)⁻¹ := hu0

/-! ## The complex logarithmic Gamma sequence -/

/-- The sequence of approximations to a logarithm of `Gamma z`, the complex analogue of
`Real.BohrMollerup.logGammaSeq`. For `0 < z.re` it converges to a logarithm of `Gamma z`,
and its derivative sequence converges, uniformly on bounded substrips of the half-plane,
to `digamma z`. -/
noncomputable def logGammaSeq (z : ℂ) (n : ℕ) : ℂ :=
  z * (Real.log n : ℂ) + (Real.log (n !) : ℂ) - ∑ m ∈ Finset.range (n + 1), log (z + m)

/-- The increment of `logGammaSeq` in closed form. -/
lemma logGammaSeq_succ_sub {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    logGammaSeq z (n + 1) - logGammaSeq z n
      = z * ((Real.log ((n : ℝ) + 1) - Real.log n : ℝ) : ℂ) - log (1 + z / ((n : ℂ) + 1)) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnC : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hx : 1 + z / ((n : ℂ) + 1) ≠ 0 := by
    intro h
    have hzval : z = -((n : ℂ) + 1) := by
      field_simp at h
      linear_combination h
    rw [hzval] at hz
    simp only [neg_re, add_re, natCast_re, one_re] at hz
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hfacC : (Real.log ((n + 1)!) : ℂ)
      = (Real.log ((n : ℝ) + 1) : ℂ) + (Real.log (n !) : ℂ) := by
    have hfac : Real.log (((n + 1)! : ℕ) : ℝ)
        = Real.log ((n : ℝ) + 1) + Real.log ((n ! : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      rw [Real.log_mul (by positivity) (by exact_mod_cast n.factorial_ne_zero)]
    rw [← ofReal_add]
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hfac
  have hlog : log (z + ((n + 1 : ℕ) : ℂ))
      = (Real.log ((n : ℝ) + 1) : ℂ) + log (1 + z / ((n : ℂ) + 1)) := by
    have hxx : ((((n : ℝ) + 1) : ℝ) : ℂ) * (1 + z / ((n : ℂ) + 1)) = z + ((n + 1 : ℕ) : ℂ) := by
      push_cast
      field_simp
      ring
    rw [← hxx, log_ofReal_mul hn1 hx]
  unfold logGammaSeq
  rw [Finset.sum_range_succ, hfacC, hlog]
  push_cast
  ring

/-- For `0 < z.re`, the sequence `logGammaSeq z` is Cauchy. -/
lemma cauchySeq_logGammaSeq {z : ℂ} (hz : 0 < z.re) : CauchySeq (logGammaSeq z) := by
  apply cauchySeq_of_summable_dist
  apply Summable.of_norm_bounded_eventually_nat
    (g := fun n => (2 * ‖z‖ + ‖z‖ ^ 2) * (1 / ((n : ℝ) + 1) ^ 2))
    (summable_one_div_natCast_add_one_sq.mul_left _)
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with n hn1 hn2
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn2R : 2 * ‖z‖ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn2)
  have hw : ‖z / ((n : ℂ) + 1)‖ = ‖z‖ / ((n : ℝ) + 1) := by
    rw [norm_div, norm_natCast_add_one]
  have hw2 : ‖z / ((n : ℂ) + 1)‖ ≤ 1 / 2 := by
    rw [hw, div_le_iff₀ (by positivity)]
    linarith
  simp only [Nat.succ_eq_add_one]
  rw [Real.norm_of_nonneg dist_nonneg, dist_eq_norm, ← norm_neg, neg_sub,
    logGammaSeq_succ_sub hz n]
  have key : z * ((Real.log ((n : ℝ) + 1) - Real.log n : ℝ) : ℂ) - log (1 + z / ((n : ℂ) + 1))
      = z * ((Real.log ((n : ℝ) + 1) - Real.log n - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)
        + (z / ((n : ℂ) + 1) - log (1 + z / ((n : ℂ) + 1))) := by
    push_cast
    ring
  rw [key]
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog_est : |Real.log ((n : ℝ) + 1) - Real.log n - ((n : ℝ) + 1)⁻¹|
      ≤ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
    have hdiv : Real.log ((n : ℝ) + 1) - Real.log n = Real.log (((n : ℝ) + 1) / n) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have l1 : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
      rw [hdiv]
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
      have he : ((n : ℝ) + 1) / n - 1 = 1 / n := by
        field_simp
        ring
      linarith
    have l2 : ((n : ℝ) + 1)⁻¹ ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) / ((n : ℝ) + 1) by positivity)
      rw [Real.log_div hn0.ne' (by positivity)] at h
      have he : (n : ℝ) / ((n : ℝ) + 1) - 1 = -((n : ℝ) + 1)⁻¹ := by
        field_simp
        ring
      rw [he] at h
      linarith
    have hcomp : 1 / (n : ℝ) - ((n : ℝ) + 1)⁻¹ ≤ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
      have he : 1 / (n : ℝ) - ((n : ℝ) + 1)⁻¹ = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        field_simp
        ring
      rw [he, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [abs_le]
    constructor
    · have : (0 : ℝ) ≤ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by positivity
      linarith
    · linarith
  calc ‖z * ((Real.log ((n : ℝ) + 1) - Real.log n - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)
        + (z / ((n : ℂ) + 1) - log (1 + z / ((n : ℂ) + 1)))‖
      ≤ ‖z * ((Real.log ((n : ℝ) + 1) - Real.log n - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)‖
        + ‖z / ((n : ℂ) + 1) - log (1 + z / ((n : ℂ) + 1))‖ := norm_add_le _ _
    _ ≤ ‖z‖ * (2 * (1 / ((n : ℝ) + 1) ^ 2)) + ‖z‖ ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
        apply _root_.add_le_add
        · rw [norm_mul, norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hlog_est (norm_nonneg z)
        · have hlt : ‖z / ((n : ℂ) + 1)‖ < 1 := lt_of_le_of_lt hw2 (by norm_num)
          have hb := norm_log_one_add_sub_self_le hlt
          rw [← norm_neg, neg_sub]
          calc ‖log (1 + z / ((n : ℂ) + 1)) - z / ((n : ℂ) + 1)‖
              ≤ ‖z / ((n : ℂ) + 1)‖ ^ 2 * (1 - ‖z / ((n : ℂ) + 1)‖)⁻¹ / 2 := hb
            _ ≤ ‖z / ((n : ℂ) + 1)‖ ^ 2 * 2 / 2 := by
                have h2 : (1 - ‖z / ((n : ℂ) + 1)‖)⁻¹ ≤ 2 := by
                  rw [← one_div]
                  have h3 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
                    (by linarith : (1 : ℝ) / 2 ≤ 1 - ‖z / ((n : ℂ) + 1)‖)
                  simpa using h3
                gcongr
            _ = ‖z / ((n : ℂ) + 1)‖ ^ 2 := by ring
            _ = ‖z‖ ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
                rw [hw, div_pow]
                ring
    _ = (2 * ‖z‖ + ‖z‖ ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by ring

/-- On the right half-plane, `exp (logGammaSeq z n) = GammaSeq z n` for `n ≠ 0`. -/
lemma exp_logGammaSeq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    exp (logGammaSeq z n) = GammaSeq z n := by
  have hne : ∀ m : ℕ, z + (m : ℂ) ≠ 0 := by
    intro m h
    have hpos : 0 < (z + (m : ℂ)).re := by
      rw [add_re, natCast_re]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    simp [h] at hpos
  unfold logGammaSeq GammaSeq
  rw [exp_sub, exp_add, exp_sum]
  congr 1
  · congr 1
    · rw [natCast_log, cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), mul_comm z (log (n : ℂ))]
    · rw [natCast_log, exp_log (by exact_mod_cast n.factorial_ne_zero)]
  · exact Finset.prod_congr rfl fun m _ => exp_log (hne m)

/-! ## The series on the right half-plane -/

/-- The digamma series on the right half-plane. -/
lemma hasSum_digamma_of_re_pos {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasSum (fun m : ℕ => ((m : ℂ) + 1)⁻¹ - (z₀ + m)⁻¹)
      (digamma z₀ + Real.eulerMascheroniConstant) := by
  set a : ℝ := min (z₀.re / 2) 1 with ha_def
  set R : ℝ := ‖z₀‖ + 1 with hR_def
  have ha : 0 < a := lt_min (by linarith) one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  set s : Set ℂ := {w : ℂ | a < w.re} ∩ {w : ℂ | ‖w‖ < R} with hs_def
  have hs_open : IsOpen s :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have haz : a < z₀.re := by
    rw [ha_def]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hz₀R : ‖z₀‖ < R := by rw [hR_def]; linarith
  have hz₀s : z₀ ∈ s := ⟨haz, hz₀R⟩
  have hmem : ∀ w ∈ s, a ≤ w.re ∧ ‖w‖ ≤ R := fun w hw => ⟨le_of_lt hw.1, le_of_lt hw.2⟩
  have hre_pos : ∀ w ∈ s, 0 < w.re := fun w hw => lt_trans ha hw.1
  -- the Weierstrass majorant
  have hu : Summable (fun m : ℕ => (R + 1) / (a * ((m : ℝ) + 1) ^ 2)) := by
    refine (summable_one_div_natCast_add_one_sq.mul_left ((R + 1) / a)).congr fun m => ?_
    rw [mul_one_div, div_div]
  -- uniform convergence of the partial sums of the packet series
  have hM : TendstoUniformlyOn
      (fun (N : ℕ) (w : ℂ) => ∑ m ∈ Finset.range N, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹))
      (fun (w : ℂ) => ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹)) atTop s :=
    tendstoUniformlyOn_tsum_nat hu fun m w hw =>
      norm_inv_add_one_sub_inv_le ha ha1 (hmem w hw).1 (hmem w hw).2 m
  have hM1 : TendstoUniformlyOn
      (fun (n : ℕ) (w : ℂ) => ∑ m ∈ Finset.range (n + 1), (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹))
      (fun (w : ℂ) => ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹)) atTop s := by
    intro u hu'
    exact (tendsto_add_atTop_nat 1).eventually (hM u hu')
  -- the constant part tends to `-γ`
  have hcR : Tendsto (fun n : ℕ => Real.log n - (harmonic n : ℝ) - ((n : ℝ) + 1)⁻¹) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h1 : Tendsto (fun n : ℕ => Real.log n - (harmonic n : ℝ)) atTop
        (𝓝 (-Real.eulerMascheroniConstant)) :=
      Real.tendsto_harmonic_sub_log.neg.congr fun n => by ring
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      apply Filter.Tendsto.inv_tendsto_atTop
      exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa using h1.sub h2
  have hcC : Tendsto (fun n : ℕ => ((Real.log n - (harmonic n : ℝ) - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ))
      atTop (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
    have h := (continuous_ofReal.tendsto (-Real.eulerMascheroniConstant)).comp hcR
    have hval : ((-Real.eulerMascheroniConstant : ℝ) : ℂ) = -(Real.eulerMascheroniConstant : ℂ) := by
      push_cast
      ring
    rw [← hval]
    exact h
  have hcU := hcC.tendstoUniformlyOn_const s
  -- assemble: the derivative sequence converges uniformly on `s`
  have hF' : TendstoUniformlyOn
      (fun (n : ℕ) (w : ℂ) => (Real.log n : ℂ) - ∑ m ∈ Finset.range (n + 1), (w + m)⁻¹)
      (fun (w : ℂ) => -(Real.eulerMascheroniConstant : ℂ)
        + ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹)) atTop s := by
    have hadd := hcU.add hM1
    refine hadd.congr ?_
    filter_upwards with n
    intro w hw
    simp only [Pi.add_apply]
    rw [Finset.sum_sub_distrib, sum_inv_natCast_add_one (n + 1)]
    push_cast [harmonic_succ]
    ring
  -- the derivatives of `logGammaSeq`
  have hderiv : ∀ n : ℕ, ∀ x : ℂ, x ∈ s →
      HasDerivAt (fun w => logGammaSeq w n)
        ((Real.log n : ℂ) - ∑ m ∈ Finset.range (n + 1), (x + m)⁻¹) x := by
    intro n x hx
    have hre : 0 < x.re := hre_pos x hx
    have h1 : HasDerivAt (fun w : ℂ => w * (Real.log n : ℂ) + (Real.log (n !) : ℂ))
        ((Real.log n : ℂ)) x := (hasDerivAt_mul_const _).add_const _
    have h2 : HasDerivAt (fun w : ℂ => ∑ m ∈ Finset.range (n + 1), log (w + m))
        (∑ m ∈ Finset.range (n + 1), (x + m)⁻¹) x := by
      apply HasDerivAt.fun_sum
        (A := fun (m : ℕ) (w : ℂ) => log (w + m)) (A' := fun m : ℕ => (x + m)⁻¹)
      intro m _
      have hmem : x + (m : ℂ) ∈ slitPlane := by
        rw [mem_slitPlane_iff]
        left
        rw [add_re, natCast_re]
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      have hinner : HasDerivAt (fun w : ℂ => w + (m : ℂ)) 1 x := (hasDerivAt_id x).add_const _
      simpa using! (hasDerivAt_log hmem).comp x hinner
    simpa only [logGammaSeq] using! h1.sub h2
  -- pointwise convergence to the limit function
  have hptw : ∀ x : ℂ, x ∈ s →
      Tendsto (fun n => logGammaSeq x n) atTop (𝓝 (limUnder atTop (logGammaSeq x))) :=
    fun x hx => (cauchySeq_logGammaSeq (hre_pos x hx)).tendsto_limUnder
  -- differentiate the limit
  have hkey : HasDerivAt (fun w => limUnder atTop (logGammaSeq w))
      (-(Real.eulerMascheroniConstant : ℂ)
        + ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (z₀ + m)⁻¹)) z₀ :=
    hasDerivAt_of_tendstoUniformlyOn hs_open hF'
      (Filter.Eventually.of_forall fun n x hx => hderiv n x hx) hptw hz₀s
  -- identify the exponential of the limit with `Gamma`
  have hEq : ∀ w ∈ s, exp (limUnder atTop (logGammaSeq w)) = Gamma w := by
    intro w hw
    have h2 := (continuous_exp.tendsto _).comp (hptw w hw)
    have h3 : Tendsto (fun n => GammaSeq w n) atTop
        (𝓝 (exp (limUnder atTop (logGammaSeq w)))) := by
      apply h2.congr'
      filter_upwards [eventually_ne_atTop 0] with n hn
      exact exp_logGammaSeq (hre_pos w hw) hn
    exact tendsto_nhds_unique h3 (GammaSeq_tendsto_Gamma w)
  have hGd : HasDerivAt Gamma (Gamma z₀ * (-(Real.eulerMascheroniConstant : ℂ)
      + ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (z₀ + m)⁻¹))) z₀ := by
    have hexp := hkey.cexp
    rw [hEq z₀ hz₀s] at hexp
    exact hexp.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hs_open.mem_nhds hz₀s) fun w hw => (hEq w hw).symm)
  have hne : ∀ m : ℕ, z₀ ≠ -(m : ℂ) := by
    intro m h
    rw [h] at hz₀
    simp only [neg_re, natCast_re] at hz₀
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hdig : digamma z₀ = -(Real.eulerMascheroniConstant : ℂ)
      + ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (z₀ + m)⁻¹) := by
    rw [digamma_def, logDeriv_apply, hGd.deriv, mul_div_cancel_left₀ _ (Gamma_ne_zero hne)]
  have hsm : Summable (fun m : ℕ => ((m : ℂ) + 1)⁻¹ - (z₀ + m)⁻¹) :=
    Summable.of_norm_bounded hu fun m =>
      norm_inv_add_one_sub_inv_le ha ha1 haz.le hz₀R.le m
  have ht : ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (z₀ + m)⁻¹)
      = digamma z₀ + Real.eulerMascheroniConstant := by
    rw [hdig]
    ring
  exact ht ▸ hsm.hasSum

/-! ## The main statements -/

/-- The series representation of the digamma function: for `z` away from the poles of
`Gamma`, the series `∑ (1 / (n + 1) - 1 / (n + z))` sums to `digamma z + γ`, where `γ` is
the Euler-Mascheroni constant. -/
theorem hasSum_digamma {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))
      (digamma z + Real.eulerMascheroniConstant) := by
  suffices h : HasSum (fun m : ℕ => ((m : ℂ) + 1)⁻¹ - (z + m)⁻¹)
      (digamma z + Real.eulerMascheroniConstant) by
    have e : (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))
        = fun m : ℕ => ((m : ℂ) + 1)⁻¹ - (z + m)⁻¹ := by
      funext m
      rw [one_div, one_div, add_comm (m : ℂ) z]
    rw [e]
    exact h
  obtain ⟨N, hN⟩ : ∃ N : ℕ, -(N : ℝ) < z.re :=
    ⟨⌈-z.re⌉₊ + 1, by have := Nat.le_ceil (-z.re); push_cast; linarith⟩
  induction N generalizing z with
  | zero =>
    apply hasSum_digamma_of_re_pos
    simpa using hN
  | succ N ih =>
    by_cases hcase : -(N : ℝ) < z.re
    · exact ih hz hcase
    · -- shift by one and use the recurrence
      have hz1 : ∀ n : ℕ, z + 1 ≠ -(n : ℂ) := by
        intro n hcon
        apply hz (n + 1)
        push_cast
        linear_combination hcon
      have hre1 : -(N : ℝ) < (z + 1).re := by
        rw [add_re, one_re]
        push_cast at hN
        linarith
      have hih := ih hz1 hre1
      rw [digamma_apply_add_one z hz] at hih
      have hzm : ∀ n : ℕ, z + (n : ℂ) ≠ 0 := fun n hcon => hz n (by linear_combination hcon)
      have hnorm_lb : ∀ n : ℕ, (n : ℝ) - ‖z‖ ≤ ‖z + n‖ := by
        intro n
        have h := norm_sub_norm_le (n : ℂ) (-z)
        rw [sub_neg_eq_add, norm_neg, norm_natCast] at h
        rw [show z + (n : ℂ) = (n : ℂ) + z from add_comm _ _]
        exact h
      have ha0 : Tendsto (fun n : ℕ => (z + (n : ℂ))⁻¹) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simp only [norm_inv]
        apply Filter.Tendsto.inv_tendsto_atTop
        apply tendsto_atTop_mono hnorm_lb
        have h := tendsto_atTop_add_const_right atTop (-‖z‖) tendsto_natCast_atTop_atTop
        exact h.congr fun n => by ring
      have hts : Summable (fun n : ℕ => (z + (n : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹) := by
        apply Summable.of_norm_bounded_eventually_nat
          (g := fun n : ℕ => 4 * (1 / ((n : ℝ) + 1) ^ 2))
          (summable_one_div_natCast_add_one_sq.mul_left _)
        filter_upwards [eventually_ge_atTop ⌈2 * ‖z‖ + 1⌉₊] with n hn
        have hnR : 2 * ‖z‖ + 1 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
        have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
        have hb1 : ((n : ℝ) + 1) / 2 ≤ ‖z + n‖ := le_trans (by linarith) (hnorm_lb n)
        have hb2 : ((n : ℝ) + 1) / 2 ≤ ‖z + ((n + 1 : ℕ) : ℂ)‖ := by
          refine le_trans ?_ (hnorm_lb (n + 1))
          push_cast
          linarith
        have hid : (z + (n : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹
            = ((z + n) * (z + ((n + 1 : ℕ) : ℂ)))⁻¹ := by
          have h1 := hzm n
          have h2 := hzm (n + 1)
          field_simp
          push_cast
          ring
        rw [hid, norm_inv, norm_mul,
          show (4 : ℝ) * (1 / ((n : ℝ) + 1) ^ 2)
            = ((((n : ℝ) + 1) / 2) * (((n : ℝ) + 1) / 2))⁻¹ by field_simp; ring]
        gcongr
      have htel := hasSum_sub_succ_of_tendsto_zero ha0 hts
      simp only [Nat.cast_zero, add_zero] at htel
      have hfin := hih.sub htel
      have e2 : (fun n : ℕ => (((n : ℂ) + 1)⁻¹ - (z + 1 + n)⁻¹)
            - ((z + (n : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹))
          = fun n : ℕ => ((n : ℂ) + 1)⁻¹ - (z + n)⁻¹ := by
        funext n
        push_cast
        ring
      rw [e2] at hfin
      convert! hfin using 1
      all_goals try with_reducible_and_instances rfl
      ring

/-! ## The growth bound on vertical strips -/

set_option maxHeartbeats 1600000 in
/-- The digamma function grows at most logarithmically on vertical strips inside the right
half-plane: on `a ≤ z.re ≤ b` with `0 < a`, `‖digamma z‖ ≤ C * Real.log (|z.im| + 2)`. -/
theorem exists_norm_digamma_le_log {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
      ‖digamma z‖ ≤ C * Real.log (|z.im| + 2) := by
  set c : ℝ := min a 1 with hc_def
  have hc : 0 < c := lt_min ha one_pos
  have hc1 : c ≤ 1 := min_le_right _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set D : ℝ := |Real.eulerMascheroniConstant| + 2 / c + (|b| + 2) / c with hD_def
  have hD0 : 0 ≤ D := by positivity
  refine ⟨D / Real.log 2 + 2 / c, ?_, fun z hza hzb => ?_⟩
  · have h1 : 0 ≤ D / Real.log 2 := div_nonneg hD0 hlog2.le
    have h2 : 0 < 2 / c := by positivity
    linarith
  have hre : 0 < z.re := lt_of_lt_of_le ha hza
  have hzc : c ≤ z.re := le_trans (min_le_left _ _) hza
  have hb0 : 0 < b := lt_of_lt_of_le hre hzb
  have hpoles : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n h
    rw [h] at hre
    simp only [neg_re, natCast_re] at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsum : HasSum (fun n : ℕ => ((n : ℂ) + 1)⁻¹ - (z + n)⁻¹)
      (digamma z + Real.eulerMascheroniConstant) := by
    have h := hasSum_digamma hpoles
    have e : (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))
        = fun m : ℕ => ((m : ℂ) + 1)⁻¹ - (z + m)⁻¹ := by
      funext m
      rw [one_div, one_div, add_comm (m : ℂ) z]
    rwa [e] at h
  -- the splitting index
  set N : ℕ := ⌈|z.im|⌉₊ + 1 with hN_def
  have him0 : (0 : ℝ) ≤ |z.im| := abs_nonneg _
  have hN1 : 1 ≤ N := Nat.le_add_left 1 _
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNim : |z.im| ≤ (N : ℝ) := by
    rw [hN_def]
    push_cast
    have := Nat.le_ceil |z.im|
    linarith
  have hNle : (N : ℝ) ≤ |z.im| + 2 := by
    rw [hN_def]
    push_cast
    have := Nat.ceil_lt_add_one him0
    linarith
  set L : ℝ := Real.log (|z.im| + 2) with hL_def
  have hL2 : Real.log 2 ≤ L := by
    rw [hL_def]
    exact Real.log_le_log (by norm_num) (by linarith)
  -- summability of the norm series and its majorant
  have hmaj : Summable (fun m : ℕ => (‖z‖ + 1) / (c * ((m : ℝ) + 1) ^ 2)) := by
    refine (summable_one_div_natCast_add_one_sq.mul_left ((‖z‖ + 1) / c)).congr fun m => ?_
    rw [mul_one_div, div_div]
  have hnormsum : Summable (fun n : ℕ => ‖((n : ℂ) + 1)⁻¹ - (z + n)⁻¹‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => norm_inv_add_one_sub_inv_le hc hc1 hzc (le_refl ‖z‖) n) hmaj
  -- head estimate: the first `N` terms contribute at most a multiple of `log`
  have hhead : ∑ n ∈ Finset.range N, ‖((n : ℂ) + 1)⁻¹ - (z + n)⁻¹‖
      ≤ 2 / c + 2 / c * L := by
    calc ∑ n ∈ Finset.range N, ‖((n : ℂ) + 1)⁻¹ - (z + n)⁻¹‖
        ≤ ∑ n ∈ Finset.range N, 2 / (c * ((n : ℝ) + 1)) :=
          Finset.sum_le_sum fun n _ => norm_inv_add_one_sub_inv_le' hc hc1 hzc n
      _ = 2 / c * ∑ n ∈ Finset.range N, ((n : ℝ) + 1)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun n _ => by rw [← div_div, div_eq_mul_inv]
      _ = 2 / c * ((harmonic N : ℚ) : ℝ) := by rw [sum_inv_natCast_add_one_real]
      _ ≤ 2 / c * (1 + Real.log N) :=
          mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (by positivity)
      _ ≤ 2 / c * (1 + L) := by
          have h3 : Real.log N ≤ L := by
            rw [hL_def]
            exact Real.log_le_log hNpos hNle
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2 / c + 2 / c * L := by ring
  -- tail estimate: past `N` the series contributes a bounded amount
  have hshift_norm : Summable (fun i : ℕ => ‖(((i + N : ℕ) : ℂ) + 1)⁻¹ - (z + (i + N : ℕ))⁻¹‖) :=
    (summable_nat_add_iff N).mpr hnormsum
  have hshift_maj : Summable (fun i : ℕ => (‖z‖ + 1) / (c * (((i + N : ℕ) : ℝ) + 1) ^ 2)) :=
    (summable_nat_add_iff N).mpr hmaj
  have htail : ‖∑' i : ℕ, ((((i + N : ℕ) : ℂ) + 1)⁻¹ - (z + (i + N : ℕ))⁻¹)‖
      ≤ (b + 2) / c := by
    have hz_norm : ‖z‖ ≤ b + |z.im| := by
      have h1 : ‖z‖ ≤ |z.re| + |z.im| := norm_le_abs_re_add_abs_im z
      have h2 : |z.re| = z.re := abs_of_pos hre
      linarith
    have hN_key : ‖z‖ + 1 ≤ (b + 2) * (N : ℝ) := by
      have h1 : b * 1 ≤ b * (N : ℝ) := mul_le_mul_of_nonneg_left hN1R hb0.le
      have h2 : (b + 2) * (N : ℝ) = b * N + 2 * N := by ring
      rw [h2]
      linarith
    calc ‖∑' i : ℕ, ((((i + N : ℕ) : ℂ) + 1)⁻¹ - (z + (i + N : ℕ))⁻¹)‖
        ≤ ∑' i : ℕ, ‖(((i + N : ℕ) : ℂ) + 1)⁻¹ - (z + (i + N : ℕ))⁻¹‖ :=
          norm_tsum_le_tsum_norm hshift_norm
      _ ≤ ∑' i : ℕ, (‖z‖ + 1) / (c * (((i + N : ℕ) : ℝ) + 1) ^ 2) :=
          hshift_norm.tsum_le_tsum
            (fun i => norm_inv_add_one_sub_inv_le hc hc1 hzc (le_refl ‖z‖) (i + N)) hshift_maj
      _ = (‖z‖ + 1) / c * ∑' i : ℕ, 1 / (((i + N : ℕ) : ℝ) + 1) ^ 2 := by
          rw [← tsum_mul_left]
          exact tsum_congr fun i => by rw [mul_one_div, div_div]
      _ ≤ (‖z‖ + 1) / c * (N : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (tsum_one_div_natCast_add_add_one_sq_le hN1)
            (by positivity)
      _ = ((‖z‖ + 1) * (N : ℝ)⁻¹) / c := by ring
      _ ≤ (b + 2) / c := by
          have h2 : (‖z‖ + 1) * (N : ℝ)⁻¹ ≤ b + 2 := by
            rw [← div_eq_mul_inv, div_le_iff₀ hNpos]
            linarith
          gcongr
  -- split the series and assemble
  have hsplit : (∑ n ∈ Finset.range N, (((n : ℂ) + 1)⁻¹ - (z + n)⁻¹))
      + ∑' i : ℕ, ((((i + N : ℕ) : ℂ) + 1)⁻¹ - (z + (i + N : ℕ))⁻¹)
      = ∑' n : ℕ, (((n : ℂ) + 1)⁻¹ - (z + n)⁻¹) :=
    hsum.summable.sum_add_tsum_nat_add N
  have h5 : ‖∑' n : ℕ, (((n : ℂ) + 1)⁻¹ - (z + n)⁻¹)‖
      ≤ (2 / c + 2 / c * L) + (b + 2) / c := by
    rw [← hsplit]
    refine le_trans (norm_add_le _ _) ?_
    exact _root_.add_le_add (le_trans (norm_sum_le _ _) hhead) htail
  have hdig_eq : digamma z = (∑' n : ℕ, (((n : ℂ) + 1)⁻¹ - (z + n)⁻¹))
      - (Real.eulerMascheroniConstant : ℂ) := by
    rw [hsum.tsum_eq]
    ring
  have h7 : ‖digamma z‖
      ≤ |Real.eulerMascheroniConstant| + ((2 / c + 2 / c * L) + (b + 2) / c) := by
    rw [hdig_eq]
    refine le_trans (norm_sub_le _ _) ?_
    have h8 : ‖((Real.eulerMascheroniConstant : ℝ) : ℂ)‖ = |Real.eulerMascheroniConstant| := by
      rw [norm_real, Real.norm_eq_abs]
    rw [h8]
    linarith [h5]
  -- absorb the constants into the logarithm
  have habs : D ≤ D / Real.log 2 * L := by
    calc D = D / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ D / Real.log 2 * L :=
          mul_le_mul_of_nonneg_left hL2 (div_nonneg hD0 hlog2.le)
  have hb_abs : (b + 2) / c ≤ (|b| + 2) / c := by
    gcongr
    exact le_abs_self b
  have hexpand : (D / Real.log 2 + 2 / c) * L = D / Real.log 2 * L + 2 / c * L := by ring
  rw [hexpand]
  linarith [h7, habs, hb_abs]

/-- The growth bound for `digamma (w / 2)` on vertical strips, the form consumed by
explicit-formula contour integrals. -/
theorem exists_norm_digamma_div_two_le_log {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ b →
      ‖digamma (w / 2)‖ ≤ C * Real.log (|w.im| + 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_digamma_le_log (a := a / 2) (b := b / 2) (by linarith)
  refine ⟨C, hC, fun w hwa hwb => ?_⟩
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  have hre2 : (w / 2).re = w.re / 2 := by rw [h2, div_ofReal_re]
  have him2 : (w / 2).im = w.im / 2 := by rw [h2, div_ofReal_im]
  have h := hbound (w / 2) (by rw [hre2]; linarith) (by rw [hre2]; linarith)
  refine le_trans h ?_
  have him_le : |(w / 2).im| + 2 ≤ |w.im| + 2 := by
    rw [him2, abs_div]
    have h4 : (0 : ℝ) ≤ |w.im| := abs_nonneg _
    have h5 : |(2 : ℝ)| = 2 := by norm_num
    rw [h5]
    linarith
  exact mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) him_le) hC.le

end Complex
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_Analysis_SpecialFunctions_Pow_Deriv
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Derivatives of complex powers

Derivative identities for functions of the form `w ↦ a * (u : ℂ) ^ (-w - 1)`.
-/
section

namespace Complex

/-- `(u : ℂ) ^ r` is continuous on `[a, b]` when `a > 0`. -/
theorem continuousOn_ofReal_cpow {r : ℂ} {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ r) (Set.Icc a b) :=
  (continuous_ofReal.continuousOn.cpow continuousOn_const
    (fun _ hu => (ofReal_mem_slitPlane).2 (lt_of_lt_of_le ha hu.1))).mono Set.Subset.rfl

theorem deriv_ofReal_cpow_neg (s : ℂ) {x : ℝ} (hx : 0 < x) :
    deriv (fun (t : ℝ) => (t : ℂ) ^ (-s)) x = -s * (x : ℂ) ^ (-s - 1) := by
  by_cases hs : s = 0
  · simp [hs, deriv_const, cpow_zero, sub_eq_add_neg]
  · simpa [sub_eq_add_neg] using deriv_ofReal_cpow_const hx.ne' (neg_ne_zero.mpr hs)

theorem continuousOn_deriv_ofReal_cpow_neg (s : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (deriv (fun (t : ℝ) => (t : ℂ) ^ (-s))) (Set.Icc a b) :=
    ((continuousOn_const : ContinuousOn (fun (_ : ℝ) => (-s : ℂ)) (Set.Icc a b)).mul
      (continuousOn_ofReal_cpow (r := -s - 1) ha)).congr fun _ ht =>
    deriv_ofReal_cpow_neg s (lt_of_lt_of_le ha ht.1)

theorem ofReal_cpow_mul_cpow_neg_sub_one (s : ℂ) {u : ℝ} (hu : 0 < u) :
    (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (-s) := by
  have hx : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  calc
    (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (1 : ℂ) * (u : ℂ) ^ (-s - 1) := by simp [cpow_one]
    _ = (u : ℂ) ^ (-s) := by rw [← cpow_add _ _ hx]; ring_nf

theorem natCast_mul_cpow_neg_eq_cpow_one_sub (N : ℕ) (s : ℂ) (hN : N ≠ 0) :
    (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 - s) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc
    (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 : ℂ) * (N : ℂ) ^ (-s) := by simp [cpow_one]
    _ = (N : ℂ) ^ (1 - s) := by rw [← cpow_add _ _ hN']; ring_nf

theorem HasDerivAt.const_mul_ofReal_cpow_neg_sub_one (a : ℂ) {u : ℝ} (hu : 0 < u) (z : ℂ) :
    HasDerivAt (fun w => a * (u : ℂ) ^ (-w - 1))
      (-a * (Complex.log u) * (u : ℂ) ^ (-z - 1)) z := by
  set huC : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have hf : HasDerivAt (fun w => -w - 1) (-1) z := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (hasDerivAt_id z).neg.sub_const (1 : ℂ)
  have hbase : HasDerivAt (fun w => (u : ℂ) ^ (-w - 1))
      ((u : ℂ) ^ (-z - 1) * Complex.log (u : ℂ) * (-1)) z :=
    HasDerivAt.const_cpow (c := (u : ℂ)) hf (Or.inl huC)
  have hbase' : HasDerivAt (fun w => (u : ℂ) ^ (-w - 1))
      (-(Complex.log (u : ℂ)) * (u : ℂ) ^ (-z - 1)) z := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hbase
  have hlog : (Real.log u : ℂ) = Complex.log (u : ℂ) := by
    simpa using (ofReal_log (x := u) (hx := le_of_lt hu))
  simpa [hlog, mul_comm, mul_left_comm, mul_assoc] using hbase'.const_mul a

end Complex
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_MeasureTheory_Integral_IntegrableOn
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Domination for `IntegrableOn`

A small `IntegrableOn` wrapper for a.e. norm domination on a restricted measure.
-/

section

namespace MeasureTheory

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
variable {μ : Measure α} {s : Set α}

/-- If `‖f x‖ ≤ g x` a.e. on `s` and `g` is integrable on `s`, then so is `f`. -/
lemma IntegrableOn.mono' {f : α → E} {g : α → ℝ} (hg : IntegrableOn g s μ)
    (hf : AEStronglyMeasurable f (μ.restrict s))
    (h : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ g x) : IntegrableOn f s μ := by
  exact Integrable.mono' hg hf h

end MeasureTheory
end
end

section
-- module Solutions.OAIQ095_OS.Mathlib_NumberTheory_AbelSummation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Finite-sum reindexing for Abel summation

Elementary reindexing lemmas for sums over initial intervals, used when passing between
floor sums and range sums.
-/

section

open Finset
open scoped BigOperators

variable {𝕜 : Type*} [AddCommGroup 𝕜]

/-- Reindex `∑ k ∈ Icc 1 N, f k` as `∑ n ∈ range N, f (n + 1)`. -/
theorem _root_.Finset.sum_Icc_one_eq_sum_range {N : ℕ} (f : ℕ → 𝕜) :
    ∑ k ∈ Icc 1 N, f k = ∑ n ∈ range N, f (n + 1) := by
  symm
  refine sum_bij (s := range N) (t := Icc 1 N)
    (f := fun n => f (n + 1)) (g := fun k => f k)
    (i := fun n _ => n + 1)
    ?hi ?hinj ?hsurj ?hcongr
  · intro n hn
    have hlt : n < N := mem_range.mp hn
    exact mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le n), Nat.succ_le_of_lt hlt⟩
  · intro a ha b hb h
    exact Nat.succ_injective h
  · intro k hk
    rcases mem_Icc.mp hk with ⟨hk1, hk2⟩
    refine ⟨k - 1, mem_range.mpr ?_, ?_⟩
    · have hsucc : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (by simpa [hsucc] using hk2)
    · simp [Nat.sub_add_cancel hk1]
  · intro n hn
    rfl

/-- If `f 0 = 0`, the term at `0` in `Icc 0 N` is redundant. -/
theorem _root_.Finset.sum_Icc_zero_eq_sum_Icc_one {N : ℕ} {f : ℕ → 𝕜} (h0 : f 0 = 0) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  have hdecomp : insert 0 (Icc 1 N) = Icc 0 N := by
    simpa [Nat.succ_eq_add_one] using
      insert_Icc_succ_left_eq_Icc (a := 0) (b := N) (h := Nat.zero_le N)
  have hnotmem : (0 : ℕ) ∉ Icc 1 N := by
    intro h
    exact (not_le.mpr (Nat.lt_succ_self 0)) (mem_Icc.mp h).1
  calc
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ insert 0 (Icc 1 N), f k := by simp [hdecomp]
    _ = f 0 + ∑ k ∈ Icc 1 N, f k := by simp
    _ = ∑ k ∈ Icc 1 N, f k := by simp [h0]

/-- If `f 0 = 0`, summing over `Icc 0 m` equals summing `f (n + 1)` over `range m`. -/
theorem _root_.Finset.sum_Icc_zero_eq_sum_range_succ {m : ℕ} {f : ℕ → 𝕜} (h0 : f 0 = 0) :
    ∑ k ∈ Icc 0 m, f k = ∑ n ∈ range m, f (n + 1) := by
  rw [sum_Icc_zero_eq_sum_Icc_one h0, sum_Icc_one_eq_sum_range]
end
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PublishedProgressionInputs
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Precisely stated published inputs for primes in progressions

Reference: H. L. Montgomery and R. C. Vaughan, *Multiplicative Number
Theory I: Classical Theory*, Cambridge Studies in Advanced Mathematics 97,
Chapter 11, DOI 10.1017/CBO9780511618314.013.

`PublishedProgressionInput.theta` is Corollary 11.20, equations (11.32) and
(11.34), p. 381. `complete` specifies the exceptional zero in Theorem 11.3,
p. 360. `unique` is the real-zero specialization of Corollary 11.10 (Page),
p. 369. The positive zero-free constant can be decreased so these use one
constant and the harmless denominator `log (4*q)` throughout.

These are explicit conditional inputs. In particular, no logarithmic
interval estimate or arithmetic comparison is assumed here.
-/

namespace Ostmann

/-- An actual primitive real character and an actual zero of its continued
Dirichlet L-function, rather than an unrestricted correction coefficient. -/
structure PrimitiveRealZero where
  modulus : ℕ
  positive : 0 < modulus
  character : DirichletCharacter ℝ modulus
  primitive : character.IsPrimitive
  nontrivial : character ≠ 1
  beta : ℝ
  beta_pos : 0 < beta
  beta_lt_one : beta < 1
  zero : @DirichletCharacter.LFunction modulus ⟨Nat.ne_of_gt positive⟩
    (character.ringHomComp Complex.ofRealHom) (beta : ℂ) = 0

noncomputable def pageCoefficient (z : Option PrimitiveRealZero) (a : ℕ) : ℝ :=
  match z with
  | none => 0
  | some e => e.character (a : ZMod e.modulus)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PublishedComplexZeroDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published zero-density and zero-free inputs for the smooth prime mean

H. L. Montgomery, *Zeros of L-functions*, Invent. Math. 8 (1969), 346–354,
Theorem 1, in the explicit form of S. Inoue, *Some explicit formulas for
partial sums of Möbius functions*, JTNB 33 (2021), 273–315, Lemma 1, p. 282:
https://jtnb.centre-mersenne.org/item/10.5802/jtnb.1162.pdf .

The region below is the bounded-height consequence of K. Ford, B. Green,
S. Konyagin, J. Maynard and T. Tao, *Long gaps between primes*, JAMS 31
(2018), 65–105, Lemma 7.1. Deleting the whole exceptional primitive character
and replacing `Q*(1+|t|)` by `2*Q*T` only weakens that statement.
https://doi.org/10.1090/jams/876 .

These are explicit conditional parameters. The zero enumeration is shared
with the explicit-formula input; no smooth-prime-mean estimate is assumed.
-/

namespace Ostmann
open scoped Classical BigOperators

structure PrimitiveComplexCharacter where
  modulus : ℕ
  positive : 0 < modulus
  character : DirichletCharacter ℂ modulus
  primitive : character.IsPrimitive
  nontrivial : character ≠ 1

noncomputable def PrimitiveComplexCharacter.L (χ : PrimitiveComplexCharacter) : ℂ → ℂ :=
  @DirichletCharacter.LFunction χ.modulus ⟨χ.positive.ne'⟩ χ.character

/-- A fixed enumeration with multiplicities used by the published density
and explicit-formula statements. Bounded ordinate ranges are finite. -/
structure ComplexZeroEnumeration (χ : PrimitiveComplexCharacter) where
  zeros : ℕ → ℂ
  in_strip : ∀ i, 0 < (zeros i).re ∧ (zeros i).re < 1
  actual_zero : ∀ i, χ.L (zeros i) = 0
  finite_height : ∀ T : ℝ, {i | |(zeros i).im| ≤ T}.Finite

noncomputable def ComplexZeroEnumeration.heightIndices {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (T : ℝ) : Finset ℕ := (Z.finite_height T).toFinset

@[simp] theorem ComplexZeroEnumeration.mem_heightIndices {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (T : ℝ) (i : ℕ) :
    i ∈ Z.heightIndices T ↔ |(Z.zeros i).im| ≤ T := Set.Finite.mem_toFinset _

noncomputable def ComplexZeroEnumeration.count {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (σ T : ℝ) : ℕ :=
  ((Z.heightIndices T).filter (fun i => σ ≤ (Z.zeros i).re)).card

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterPartialSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Elementary cancellation in primitive nonprincipal character sums

These concrete prefix bounds are the first step in the remaining analytic
zero-count and explicit-formula obligations.
-/

namespace Ostmann

open Finset Filter
open scoped Classical BigOperators

theorem PrimitiveComplexCharacter.period_sum (χ : PrimitiveComplexCharacter) :
    (∑ n ∈ range χ.modulus, χ.character (n : ZMod χ.modulus)) = 0 := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hsum : (∑ n ∈ range χ.modulus, χ.character (n : ZMod χ.modulus)) =
      ∑ a : ZMod χ.modulus, χ.character a := by
    apply sum_bij (t := (univ : Finset (ZMod χ.modulus)))
      (fun (n : ℕ) _ => (n : ZMod χ.modulus))
    · intro n hn
      exact mem_univ _
    · intro n hn m hm he
      have h := congrArg ZMod.val he
      simpa only [ZMod.val_natCast_of_lt (mem_range.mp hn),
        ZMod.val_natCast_of_lt (mem_range.mp hm)] using h
    · intro a ha
      exact ⟨a.val, mem_range.mpr a.val_lt, ZMod.natCast_zmod_val a⟩
    · intro n hn
      rfl
  rw [hsum]
  exact MulChar.sum_eq_zero_of_ne_one χ.nontrivial

theorem PrimitiveComplexCharacter.period_blocks_sum (χ : PrimitiveComplexCharacter) (k : ℕ) :
    (∑ n ∈ range (k * χ.modulus), χ.character (n : ZMod χ.modulus)) = 0 := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih, zero_add]
    simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]
      using χ.period_sum

theorem PrimitiveComplexCharacter.prefix_remainder (χ : PrimitiveComplexCharacter) (N : ℕ) :
    (∑ n ∈ range N, χ.character (n : ZMod χ.modulus)) =
      ∑ n ∈ range (N % χ.modulus), χ.character (n : ZMod χ.modulus) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hN : N = (N / χ.modulus) * χ.modulus + N % χ.modulus := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  conv_lhs => rw [hN]
  rw [sum_range_add, χ.period_blocks_sum, zero_add]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]

theorem PrimitiveComplexCharacter.prefix_bound (χ : PrimitiveComplexCharacter) (N : ℕ) :
    ‖∑ n ∈ range N, χ.character (n : ZMod χ.modulus)‖ ≤ χ.modulus := by
  rw [χ.prefix_remainder]
  calc
    _ ≤ ∑ n ∈ range (N % χ.modulus), ‖χ.character (n : ZMod χ.modulus)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range (N % χ.modulus), (1 : ℝ) := sum_le_sum (fun _ _ => χ.character.norm_le_one _)
    _ = (N % χ.modulus : ℕ) := by simp
    _ ≤ (χ.modulus : ℝ) := by exact_mod_cast (Nat.mod_lt N χ.positive).le

theorem PrimitiveComplexCharacter.prefix_Icc_bound (χ : PrimitiveComplexCharacter) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, χ.character (n : ZMod χ.modulus)‖ ≤ χ.modulus + 1 := by
  have he : (∑ n ∈ range (N + 1), χ.character (n : ZMod χ.modulus)) =
      χ.character 0 + ∑ n ∈ Icc 1 N, χ.character (n : ZMod χ.modulus) := by
    rw [Nat.range_succ_eq_Icc_zero,
      ← insert_Icc_add_one_left_eq_Icc (Nat.zero_le N), sum_insert (by simp)]
    simp
  have hb := χ.prefix_bound (N + 1)
  have hn := norm_sub_le (∑ n ∈ range (N + 1), χ.character (n : ZMod χ.modulus)) (χ.character 0)
  rw [he] at hn hb
  simpa only [add_sub_cancel_left] using hn.trans
    (add_le_add hb (χ.character.norm_le_one 0))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterRightHalfPlane
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative initial bounds for the continued character L-function

The elementary coefficient bounds and Möbius inverse give a uniform positive
lower bound on Re(s)=2, used as the center value in the zero-count argument.
-/

namespace Ostmann

open MeasureTheory Filter
open scoped Classical BigOperators

theorem lSeries_norm_bound_re_two (f : ℕ → ℂ)
    (hf : ∀ n : ℕ, n ≠ 0 → ‖f n‖ ≤ 1) (s : ℂ) (hs : s.re = 2) :
    ‖LSeries f s‖ ≤ Real.pi ^ 2 / 6 := by
  have hsum : LSeriesSummable f s :=
    LSeriesSummable_of_bounded_of_one_lt_re hf (by rw [hs]; norm_num)
  have hpoint (n : ℕ) : ‖LSeries.term f s n‖ ≤ 1 / (n : ℝ) ^ 2 := by
    rw [LSeries.norm_term_eq, hs, Real.rpow_two]
    split_ifs with hn
    · simp [hn]
    · exact div_le_div_of_nonneg_right (hf n hn) (sq_nonneg _)
  calc
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
      hsum.norm.tsum_le_tsum hpoint hasSum_zeta_two.summable
    _ = _ := hasSum_zeta_two.tsum_eq

theorem PrimitiveComplexCharacter.L_lower_re_two (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : s.re = 2) : 1 / 3 ≤ ‖χ.L s‖ := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  let f : ℕ → ℂ := fun n => χ.character (n : ZMod χ.modulus) * ArithmeticFunction.moebius n
  have hf (n : ℕ) (hn : n ≠ 0) : ‖f n‖ ≤ 1 := by
    dsimp only [f]
    rw [norm_mul]
    have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      norm_cast
      exact ArithmeticFunction.abs_moebius_le_one
    exact (mul_le_mul (χ.character.norm_le_one _) hm (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul 1)
  have hb := lSeries_norm_bound_re_two f hf s hs
  have he : χ.L s * LSeries f s = 1 := by
    rw [PrimitiveComplexCharacter.L, DirichletCharacter.LFunction_eq_LSeries _ (by rw [hs]; norm_num)]
    exact DirichletCharacter.LSeries.mul_mu_eq_one χ.character (by rw [hs]; norm_num)
  have hn := congrArg norm he
  rw [norm_mul, norm_one] at hn
  have hpi : Real.pi ^ 2 / 6 ≤ 3 := by
    have h := Real.pi_lt_four
    nlinarith [Real.pi_pos]
  have hmul := mul_le_mul_of_nonneg_left (hb.trans hpi) (norm_nonneg (χ.L s))
  rw [hn] at hmul
  linarith

theorem PrimitiveComplexCharacter.partial_sum_bigO (χ : PrimitiveComplexCharacter) :
    (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, χ.character (n : ZMod χ.modulus)) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (χ.modulus + 1 : ℝ)
  filter_upwards with N
  simpa using χ.prefix_Icc_bound N

theorem PrimitiveComplexCharacter.L_integral_right (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 1 < s.re) :
    χ.L s = s * ∫ t in Set.Ioi (1 : ℝ),
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.character (n : ZMod χ.modulus)) *
        (t : ℂ) ^ (-(s + 1)) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  rw [PrimitiveComplexCharacter.L, DirichletCharacter.LFunction_eq_LSeries _ hs]
  apply LSeries_eq_mul_integral _ (r := 0) le_rfl (by linarith)
    (χ.character.LSeriesSummable_of_one_lt_re hs)
  simpa only [Real.rpow_zero] using χ.partial_sum_bigO

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealZeroKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing the real parts of zero contributions at two real points -/

namespace Ostmann

noncomputable def realZeroKernel (a y : ℝ) : ℝ := a / (a ^ 2 + y ^ 2)

theorem realZeroKernel_nonneg {a y : ℝ} (ha : 0 ≤ a) : 0 ≤ realZeroKernel a y :=
  div_nonneg ha (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem realZeroKernel_complex (s : ℝ) (ρ : ℂ) :
    ((s : ℂ) - ρ)⁻¹.re = realZeroKernel (s - ρ.re) ρ.im := by
  rw [Complex.inv_re]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.normSq_apply,
    Complex.sub_im, Complex.ofReal_im, zero_sub, neg_mul_neg, realZeroKernel, pow_two]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealZeroSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Summing the zero-free comparison with a finite exceptional set -/

namespace Ostmann

open scoped BigOperators Classical

theorem realZeroKernel_le_inv {a y : ℝ} (ha : 0 < a) :
    realZeroKernel a y ≤ a⁻¹ := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  calc
    _ ≤ a / a ^ 2 := div_le_div_of_nonneg_left ha.le ha2 (by nlinarith [sq_nonneg y])
    _ = _ := by field_simp

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_PublishedRealZeros
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Published inputs for the real-character zero argument

The Hadamard input is the real-axis specialization of H. A. Helfgott,
*The ternary Goldbach problem*, Part I, 15 December 2019, section 3.7.4,
equations (3.97)--(3.102), printed pp. 86--87:
https://webusers.imj-prg.fr/~harald.helfgott/anglais/PartI.pdf .
The bounded gamma term on 1 < s <= 2 is included in the absolute constant.

The low-height region and single simple exception are H. L. Montgomery and
R. C. Vaughan, *Multiplicative Number Theory I*, Theorem 11.3 and Corollary
11.10, pp. 360 and 369, using the same decreased constant as
`PublishedProgressionInput`. The separate Siegel specialization is Corollary
11.15 of that book. All these are explicit conditional parameters.
-/

namespace Ostmann

open scoped BigOperators

structure PrimitiveRealCharacter where
  modulus : ℕ
  positive : 0 < modulus
  character : DirichletCharacter ℝ modulus
  primitive : character.IsPrimitive
  nontrivial : character ≠ 1

noncomputable def PrimitiveRealCharacter.complexCharacter (χ : PrimitiveRealCharacter) :
    DirichletCharacter ℂ χ.modulus := χ.character.ringHomComp Complex.ofRealHom

noncomputable def PrimitiveRealCharacter.L (χ : PrimitiveRealCharacter) : ℂ → ℂ :=
  @DirichletCharacter.LFunction χ.modulus ⟨χ.positive.ne'⟩ χ.complexCharacter

noncomputable def PrimitiveRealCharacter.logDerivative (χ : PrimitiveRealCharacter) (s : ℝ) : ℝ :=
  (deriv χ.L (s : ℂ) / χ.L (s : ℂ)).re

/-- A genuine zero sequence, indexed with multiplicities. The Hadamard
identity specifies its sum; no downstream prime-mass bound is included. -/
structure RealCharacterZeroExpansion (χ : PrimitiveRealCharacter) (C : ℝ) where
  zeros : ℕ → ℂ
  in_strip : ∀ i, 0 < (zeros i).re ∧ (zeros i).re < 1
  actual_zero : ∀ i, χ.L (zeros i) = 0
  summable : ∀ s : ℝ, 1 < s → s ≤ 2 →
    Summable (fun i => realZeroKernel (s - (zeros i).re) (zeros i).im)
  hadamard : ∀ s : ℝ, 1 < s → s ≤ 2 →
    |(∑' i, realZeroKernel (s - (zeros i).re) (zeros i).im) -
      χ.logDerivative s - (1 / 2) * Real.log χ.modulus| ≤ C

noncomputable def RealCharacterZeroExpansion.realZero {χ : PrimitiveRealCharacter} {C : ℝ}
    (Z : RealCharacterZeroExpansion χ C) (i : ℕ) (hi : (Z.zeros i).im = 0) : PrimitiveRealZero where
  modulus := χ.modulus
  positive := χ.positive
  character := χ.character
  primitive := χ.primitive
  nontrivial := χ.nontrivial
  beta := (Z.zeros i).re
  beta_pos := (Z.in_strip i).1
  beta_lt_one := (Z.in_strip i).2
  zero := by
    have he : ((Z.zeros i).re : ℂ) = Z.zeros i := by
      apply Complex.ext <;> simp [hi]
    change χ.L _ = 0
    rw [he]
    exact Z.actual_zero i

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothVerticalKernel
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The absolutely convergent vertical kernel before contour shifting -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators

noncomputable def characterMangoldtCoefficient (χ : PrimitiveComplexCharacter) (n : ℕ) : ℂ :=
  χ.character (n : ZMod χ.modulus) * (ArithmeticFunction.vonMangoldt n : ℂ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothDirichletIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial vertical-line formula for the smooth Mangoldt sum -/

namespace Ostmann

open MeasureTheory
open scoped BigOperators

theorem PrimitiveComplexCharacter.mangoldt_LSeries_eq (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (characterMangoldtCoefficient χ) s = -deriv χ.L s / χ.L s := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  change LSeries (characterMangoldtCoefficient χ) s =
    -deriv (DirichletCharacter.LFunction χ.character) s / DirichletCharacter.LFunction χ.character s
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ.character hs,
    DirichletCharacter.LFunction_eq_LSeries χ.character hs]
  exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ.character hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterMellinIntegral
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded-prefix Mellin representation on Re(s)>0 -/

namespace Ostmann

open MeasureTheory Filter Set
open scoped Classical BigOperators Topology

noncomputable def characterSummatory (χ : PrimitiveComplexCharacter) (t : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator
    (fun t => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.character (n : ZMod χ.modulus)) t

theorem characterSummatory_zero (χ : PrimitiveComplexCharacter) {t : ℝ} (ht : t ≤ 1) :
    characterSummatory χ t = 0 := by simp [characterSummatory, not_lt.mpr ht]

theorem characterSummatory_bound (χ : PrimitiveComplexCharacter) (t : ℝ) :
    ‖characterSummatory χ t‖ ≤ χ.modulus + 1 := by
  by_cases ht : 1 < t
  · simpa [characterSummatory, ht] using χ.prefix_Icc_bound ⌊t⌋₊
  · rw [characterSummatory_zero χ (le_of_not_gt ht), norm_zero]
    positivity

theorem characterSummatory_locallyIntegrable (χ : PrimitiveComplexCharacter) :
    LocallyIntegrableOn (characterSummatory χ) (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  refine ⟨Icc (t / 2) (t + 1), nhdsWithin_le_nhds
    (Icc_mem_nhds (by linarith) (by linarith)), ?_⟩
  have hi := integrableOn_mul_sum_Icc
    (fun n => χ.character (n : ZMod χ.modulus)) (m := 1)
    (show 0 ≤ t / 2 by linarith) (b := t + 1)
    (show IntegrableOn (fun _ : ℝ => (1 : ℂ)) (Icc (t / 2) (t + 1)) from
      continuousOn_const.integrableOn_Icc)
  simp only [one_mul] at hi
  exact hi.indicator measurableSet_Ioi

theorem characterSummatory_bigO (χ : PrimitiveComplexCharacter) :
    characterSummatory χ =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  apply Asymptotics.IsBigO.of_bound (χ.modulus + 1 : ℝ)
  filter_upwards with t
  simpa using characterSummatory_bound χ t

theorem characterSummatory_zero_bigO (χ : PrimitiveComplexCharacter) (b : ℝ) :
    characterSummatory χ =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  apply Asymptotics.IsBigO.of_bound 0
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with t ht
  simp [characterSummatory_zero χ ht.le]

theorem characterSummatory_mellin (χ : PrimitiveComplexCharacter) (s : ℂ) :
    mellin (characterSummatory χ) (-s) = ∫ t in Ioi (1 : ℝ),
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.character (n : ZMod χ.modulus)) *
        (t : ℂ) ^ (-(s + 1)) := by
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (-s - 1) * characterSummatory χ t
  have hF (t : ℝ) (ht : t ≤ 1) : F t = 0 := by
    simp [F, characterSummatory_zero χ ht]
  change (∫ t in Ioi (0 : ℝ), F t) = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => hF t (by
    simp only [mem_Ioi, not_lt] at ht; linarith))]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Ioi (1 : ℝ)) (fun t ht => hF t (le_of_not_gt ht))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [F, characterSummatory, indicator_of_mem ht]
  rw [show -s - 1 = -(s + 1) by ring]
  exact mul_comm _ _

noncomputable def characterMellinL (χ : PrimitiveComplexCharacter) (s : ℂ) : ℂ :=
  s * mellin (characterSummatory χ) (-s)

theorem characterMellinL_differentiableAt (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 0 < s.re) : DifferentiableAt ℂ (characterMellinL χ) s := by
  have hm := mellin_differentiableAt_of_isBigO_rpow
    (characterSummatory_locallyIntegrable χ) (characterSummatory_bigO χ)
    (s := -s) (by simpa using neg_neg_of_pos hs)
    (characterSummatory_zero_bigO χ (-s.re - 1)) (by simp)
  exact differentiableAt_id.mul (hm.comp s differentiableAt_id.neg)

theorem characterMellinL_eq_L (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 0 < s.re) :
    characterMellinL χ s = χ.L s := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (characterMellinL χ) {s : ℂ | 0 < s.re} :=
    (show DifferentiableOn ℂ (characterMellinL χ) {s : ℂ | 0 < s.re} from
      fun s hs => (characterMellinL_differentiableAt χ s hs).differentiableWithinAt).analyticOnNhd hopen
  have hg : AnalyticOnNhd ℂ χ.L {s : ℂ | 0 < s.re} :=
    (DirichletCharacter.differentiable_LFunction χ.nontrivial).differentiableOn.analyticOnNhd hopen
  have he : characterMellinL χ =ᶠ[𝓝 (2 : ℂ)] χ.L := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with z hz
    rw [characterMellinL, characterSummatory_mellin, χ.L_integral_right z hz]
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    (convex_halfSpace_re_gt (0 : ℝ)).isPreconnected (by norm_num : (2 : ℂ) ∈ {s : ℂ | 0 < s.re})
    he hs

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterMellinBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A quantitative bound in the positive half-plane

The bounded periodic prefix sums give the polynomial growth needed for
local Jensen estimates, without assuming a convexity estimate for L.
-/

namespace Ostmann

open MeasureTheory Set
open scoped BigOperators

theorem PrimitiveComplexCharacter.L_integral_positive (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 0 < s.re) :
    χ.L s = s * ∫ t in Ioi (1 : ℝ),
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.character (n : ZMod χ.modulus)) *
        (t : ℂ) ^ (-(s + 1)) := by
  rw [← characterMellinL_eq_L χ s hs, characterMellinL, characterSummatory_mellin]

theorem PrimitiveComplexCharacter.L_norm_bound_positive (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 0 < s.re) :
    ‖χ.L s‖ ≤ ‖s‖ * ((χ.modulus : ℝ) + 1) / s.re := by
  have hg : IntegrableOn (fun t : ℝ => ((χ.modulus : ℝ) + 1) * t ^ (-s.re - 1))
      (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hmean : ‖∫ t in Ioi (1 : ℝ),
      (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, χ.character (n : ZMod χ.modulus)) *
        (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t in Ioi (1 : ℝ), ((χ.modulus : ℝ) + 1) * t ^ (-s.re - 1) := by
    apply norm_integral_le_of_norm_le hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    have ht0 : 0 < t := by linarith
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
    rw [show -(s.re + 1) = -s.re - 1 by ring]
    exact mul_le_mul_of_nonneg_right (χ.prefix_Icc_bound _) (Real.rpow_nonneg ht0.le _)
  have heval : (∫ t in Ioi (1 : ℝ), ((χ.modulus : ℝ) + 1) * t ^ (-s.re - 1)) =
      ((χ.modulus : ℝ) + 1) / s.re := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) (by norm_num : (0 : ℝ) < 1)]
    simp only [Real.one_rpow]
    field_simp [hs.ne']
    ring
  rw [χ.L_integral_positive s hs, norm_mul]
  calc
    _ ≤ ‖s‖ * (((χ.modulus : ℝ) + 1) / s.re) :=
      mul_le_mul_of_nonneg_left (hmean.trans_eq heval) (norm_nonneg _)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterLocalZeroCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local zero counts for primitive character L-functions

Jensen's formula is applied to disks centered on Re(s)=2.  The larger
radius stays in the positive half-plane; the smaller disk covers a unit
ordinate interval in the right half of the critical strip.
-/

namespace Ostmann

open Metric Set MeromorphicOn
open scoped BigOperators

noncomputable def characterZeroCenter (t : ℝ) : ℂ := 2 + (t : ℂ) * Complex.I

@[simp] theorem characterZeroCenter_re (t : ℝ) : (characterZeroCenter t).re = 2 := by
  simp [characterZeroCenter]

@[simp] theorem characterZeroCenter_im (t : ℝ) : (characterZeroCenter t).im = t := by
  simp [characterZeroCenter]

theorem characterZeroCenter_norm (t : ℝ) : ‖characterZeroCenter t‖ ≤ 2 + |t| := by
  simpa using Complex.norm_le_abs_re_add_abs_im (characterZeroCenter t)

theorem character_disk_re (t : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (characterZeroCenter t) (7 / 4 : ℝ)) : 1 / 4 ≤ z.re := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hr := (Complex.abs_re_le_norm (z - characterZeroCenter t)).trans hz
  simp only [Complex.sub_re, characterZeroCenter_re] at hr
  linarith [(abs_le.mp hr).1]

theorem character_disk_norm (t : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (characterZeroCenter t) (7 / 4 : ℝ)) : ‖z‖ ≤ |t| + 4 := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have htri := norm_add_le (z - characterZeroCenter t) (characterZeroCenter t)
  rw [sub_add_cancel] at htri
  linarith [characterZeroCenter_norm t]

theorem PrimitiveComplexCharacter.L_disk_bound (χ : PrimitiveComplexCharacter)
    (t : ℝ) (z : ℂ) (hz : z ∈ closedBall (characterZeroCenter t) (7 / 4 : ℝ)) :
    ‖χ.L z‖ ≤ 16 * (χ.modulus : ℝ) * (|t| + 2) := by
  have hr := character_disk_re t z hz
  have hnorm := character_disk_norm t z hz
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  calc
    _ ≤ ‖z‖ * ((χ.modulus : ℝ) + 1) / z.re := χ.L_norm_bound_positive z (by linarith)
    _ ≤ ‖z‖ * ((χ.modulus : ℝ) + 1) / (1 / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hr
    _ ≤ (|t| + 4) * ((χ.modulus : ℝ) + 1) / (1 / 4) := by gcongr
    _ ≤ _ := by
      norm_num only [div_eq_mul_inv, inv_div, inv_one]
      nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)]

noncomputable def characterLocalZeroMass (χ : PrimitiveComplexCharacter) (t : ℝ) : ℤ :=
  ∑ᶠ z, divisor χ.L (closedBall (characterZeroCenter t) (13 / 8 : ℝ)) z

/-- A logarithmic zero count, including analytic multiplicity, on each local disk. -/
theorem PrimitiveComplexCharacter.local_zero_mass_bound (χ : PrimitiveComplexCharacter)
    (t : ℝ) :
    (characterLocalZeroMass χ t : ℝ) ≤
      Real.log (48 * (χ.modulus : ℝ) * (|t| + 2)) / Real.log (14 / 13) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have ha : AnalyticOnNhd ℂ χ.L (closedBall (characterZeroCenter t) |(7 / 4 : ℝ)|) :=
    fun _ _ => (DirichletCharacter.differentiable_LFunction χ.nontrivial).analyticAt _
  have hlo := χ.L_lower_re_two (characterZeroCenter t) (characterZeroCenter_re t)
  have hne : χ.L (characterZeroCenter t) ≠ 0 := by
    intro he
    rw [he, norm_zero] at hlo
    linarith
  have hM : 1 ≤ 16 * (χ.modulus : ℝ) * (|t| + 2) := by
    nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hq) (abs_nonneg t)]
  have hj := ha.sum_divisor_le (r := (13 / 8 : ℝ)) (R := (7 / 4 : ℝ))
    (by norm_num) (by norm_num) hM hne (fun z hz =>
      χ.L_disk_bound t z (by simpa only [abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using
        sphere_subset_closedBall hz))
  have hratio : (16 * (χ.modulus : ℝ) * (|t| + 2)) / ‖χ.L (characterZeroCenter t)‖ ≤
      48 * (χ.modulus : ℝ) * (|t| + 2) := by
    apply (div_le_iff₀ (by linarith : 0 < ‖χ.L (characterZeroCenter t)‖)).2
    nlinarith [mul_le_mul_of_nonneg_left hlo
      (show 0 ≤ 48 * (χ.modulus : ℝ) * (|t| + 2) by positivity)]
  have hlog : 0 < Real.log (14 / 13 : ℝ) := Real.log_pos (by norm_num)
  have hlogratio := Real.log_le_log (div_pos (by positivity)
    (by linarith : 0 < ‖χ.L (characterZeroCenter t)‖)) hratio
  rw [show |(13 / 8 : ℝ)| = 13 / 8 by norm_num,
    show (7 / 4 : ℝ) / (13 / 8) = 14 / 13 by norm_num] at hj
  exact hj.trans (div_le_div_of_nonneg_right hlogratio hlog.le)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroMultiplicity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual analytic multiplicities of character zeros

The divisor on the whole plane is used consistently, so local disk counts
and later sums over finitely many zeros count the same multiplicities.
-/

namespace Ostmann

open Metric Set MeromorphicOn
open scoped BigOperators Classical

theorem PrimitiveComplexCharacter.L_analytic (χ : PrimitiveComplexCharacter) (z : ℂ) :
    AnalyticAt ℂ χ.L z := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact (DirichletCharacter.differentiable_LFunction χ.nontrivial).analyticAt z

theorem PrimitiveComplexCharacter.L_order_ne_top (χ : PrimitiveComplexCharacter) (z : ℂ) :
    analyticOrderAt χ.L z ≠ ⊤ := by
  intro h
  have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z χ.L_analytic).mp h
  have hn := χ.L_lower_re_two (2 : ℂ) (by norm_num)
  rw [he] at hn
  norm_num at hn

noncomputable def characterZeroOrder (χ : PrimitiveComplexCharacter) (z : ℂ) : ℤ :=
  divisor χ.L univ z

theorem characterZeroOrder_eq_local (χ : PrimitiveComplexCharacter) (t : ℝ) (z : ℂ)
    (hz : z ∈ closedBall (characterZeroCenter t) (13 / 8 : ℝ)) :
    characterZeroOrder χ z =
      divisor χ.L (closedBall (characterZeroCenter t) (13 / 8 : ℝ)) z := by
  simp only [characterZeroOrder, AnalyticOnNhd.divisor_apply
    (show AnalyticOnNhd ℂ χ.L univ from fun z _ => χ.L_analytic z) (mem_univ z),
    AnalyticOnNhd.divisor_apply
    (show AnalyticOnNhd ℂ χ.L (closedBall (characterZeroCenter t) (13 / 8 : ℝ)) from
      fun z _ => χ.L_analytic z) hz]

theorem characterZeroOrder_sum_le_local (χ : PrimitiveComplexCharacter) (t : ℝ)
    (S : Finset ℂ) (hS : ∀ z ∈ S, z ∈ closedBall (characterZeroCenter t) (13 / 8 : ℝ)) :
    ∑ z ∈ S, characterZeroOrder χ z ≤ characterLocalZeroMass χ t := by
  let D := divisor χ.L (closedBall (characterZeroCenter t) (13 / 8 : ℝ))
  have hfin := D.finiteSupport (isCompact_closedBall (characterZeroCenter t) (13 / 8 : ℝ))
  have hnonneg : ∀ z, 0 ≤ D z :=
    (show AnalyticOnNhd ℂ χ.L (closedBall (characterZeroCenter t) (13 / 8 : ℝ)) from
      fun z _ => χ.L_analytic z).divisor_nonneg
  calc
    _ = ∑ z ∈ S, D z := Finset.sum_congr rfl (fun z hz => characterZeroOrder_eq_local χ t z (hS z hz))
    _ ≤ ∑ z ∈ S ∪ hfin.toFinset, D z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro z _ _
      exact hnonneg z
    _ = ∑ᶠ z, D z := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro z hz
      exact Finset.mem_union_right _ (hfin.mem_toFinset.mpr hz)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroCover
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Covering the right critical half-strip by Jensen disks -/

namespace Ostmann

open Metric Set
open scoped BigOperators Classical

theorem character_strip_mem_disk (z : ℂ) (t : ℝ)
    (hr : 1 / 2 ≤ z.re) (hr' : z.re ≤ 1) (hi : |z.im - t| ≤ 1 / 2) :
    z ∈ closedBall (characterZeroCenter t) (13 / 8 : ℝ) := by
  rw [mem_closedBall, dist_eq_norm]
  have hs : ‖z - characterZeroCenter t‖ ^ 2 = (z.re - 2) ^ 2 + (z.im - t) ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two]
  have hire := abs_le.mp hi
  have hprod := mul_nonneg (show 0 ≤ z.re - 1 / 2 by linarith)
    (show 0 ≤ 1 - z.re by linarith)
  have hiprod := mul_nonneg (show 0 ≤ 1 / 2 - (z.im - t) by linarith)
    (show 0 ≤ 1 / 2 + (z.im - t) by linarith)
  nlinarith [norm_nonneg (z - characterZeroCenter t)]

noncomputable def characterOrdinateBins (T : ℝ) : Finset ℤ :=
  Finset.Icc ⌊-T⌋ ⌊T⌋

theorem characterOrdinateBins_mem (T : ℝ) (z : ℂ) (hz : |z.im| ≤ T) :
    ⌊z.im⌋ ∈ characterOrdinateBins T := by
  exact Finset.mem_Icc.mpr ⟨Int.floor_mono (abs_le.mp hz).1, Int.floor_mono (abs_le.mp hz).2⟩

theorem characterOrdinateBins_card (T : ℝ) (hT : 0 ≤ T) :
    ((characterOrdinateBins T).card : ℝ) ≤ 2 * T + 2 := by
  have hle : ⌊-T⌋ ≤ ⌊T⌋ + 1 := by
    have h := Int.floor_mono (show -T ≤ T by linarith)
    omega
  have hc := Int.card_Icc_of_le _ _ hle
  have hc' : ((characterOrdinateBins T).card : ℝ) = (⌊T⌋ : ℝ) + 1 - (⌊-T⌋ : ℝ) := by
    exact_mod_cast hc
  rw [hc']
  linarith [Int.floor_le T, Int.lt_floor_add_one (-T)]

theorem characterOrdinateBins_center_bound (T : ℝ) (n : ℤ)
    (hn : n ∈ characterOrdinateBins T) : |(n : ℝ) + 1 / 2| ≤ T + 1 := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hlo' : (⌊-T⌋ : ℝ) ≤ n := by exact_mod_cast hlo
  have hhi' : (n : ℝ) ≤ ⌊T⌋ := by exact_mod_cast hhi
  exact abs_le.mpr ⟨by linarith [Int.lt_floor_add_one (-T)], by linarith [Int.floor_le T]⟩

theorem character_floor_mem_disk (z : ℂ) (hr : 1 / 2 ≤ z.re) (hr' : z.re ≤ 1) :
    z ∈ closedBall (characterZeroCenter ((⌊z.im⌋ : ℝ) + 1 / 2)) (13 / 8 : ℝ) := by
  apply character_strip_mem_disk z _ hr hr'
  exact abs_le.mpr ⟨by linarith [Int.floor_le z.im], by linarith [Int.lt_floor_add_one z.im]⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterRightZeroCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative zero count in the right half of the critical strip -/

namespace Ostmann

open Metric Set
open scoped BigOperators Classical

/-- Sum of actual analytic multiplicities over any finite right-half family. -/
theorem PrimitiveComplexCharacter.right_zero_sum_bound (χ : PrimitiveComplexCharacter)
    (T : ℝ) (hT : 0 ≤ T) (S : Finset ℂ)
    (hS : ∀ z ∈ S, 1 / 2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) :
    ∑ z ∈ S, (characterZeroOrder χ z : ℝ) ≤
      (2 * T + 2) * (Real.log (48 * (χ.modulus : ℝ) * (T + 3)) / Real.log (14 / 13)) := by
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have hden : 0 < Real.log (14 / 13 : ℝ) := Real.log_pos (by norm_num)
  have hpos : 0 ≤ Real.log (48 * (χ.modulus : ℝ) * (T + 3)) / Real.log (14 / 13) := by
    apply div_nonneg _ hden.le
    apply Real.log_nonneg
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) hT]
  have hfiber (n : ℤ) (hn : n ∈ characterOrdinateBins T) :
      ∑ z ∈ S.filter (fun z => ⌊z.im⌋ = n), (characterZeroOrder χ z : ℝ) ≤
        Real.log (48 * (χ.modulus : ℝ) * (T + 3)) / Real.log (14 / 13) := by
    have hlocal := characterZeroOrder_sum_le_local χ ((n : ℝ) + 1 / 2)
      (S.filter fun z => ⌊z.im⌋ = n) (by
        intro z hz
        obtain ⟨hzS, hzn⟩ := Finset.mem_filter.mp hz
        simpa only [hzn] using character_floor_mem_disk z (hS z hzS).1 (hS z hzS).2.1)
    have hlocalR : ∑ z ∈ S.filter (fun z => ⌊z.im⌋ = n), (characterZeroOrder χ z : ℝ) ≤
        (characterLocalZeroMass χ ((n : ℝ) + 1 / 2) : ℝ) := by exact_mod_cast hlocal
    have hb := χ.local_zero_mass_bound ((n : ℝ) + 1 / 2)
    refine (hlocalR.trans hb).trans (div_le_div_of_nonneg_right ?_ hden.le)
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hn' := characterOrdinateBins_center_bound T n hn
    linarith
  calc
    _ = ∑ n ∈ characterOrdinateBins T,
        ∑ z ∈ S.filter (fun z => ⌊z.im⌋ = n), (characterZeroOrder χ z : ℝ) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun z hz => characterOrdinateBins_mem T z (hS z hz).2.2) _
    _ ≤ ∑ _n ∈ characterOrdinateBins T,
        Real.log (48 * (χ.modulus : ℝ) * (T + 3)) / Real.log (14 / 13) :=
      Finset.sum_le_sum hfiber
    _ = ((characterOrdinateBins T).card : ℝ) *
        (Real.log (48 * (χ.modulus : ℝ) * (T + 3)) / Real.log (14 / 13)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (characterOrdinateBins_card T hT) hpos

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroCountRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Standard conductor-height form of the right-half zero count -/

namespace Ostmann

open scoped BigOperators

theorem character_zero_log_cost (q T : ℝ) (hq : 1 ≤ q) (hT : 0 ≤ T) :
    Real.log (48 * q * (T + 3)) ≤ 8 * Real.log (q * (T + 2)) := by
  have hx : 2 ≤ q * (T + 2) := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) hT]
  have hpow : (2 : ℝ) ^ 7 ≤ (q * (T + 2)) ^ 7 := pow_le_pow_left₀ (by norm_num) hx 7
  have hy : 48 * q * (T + 3) ≤ 72 * (q * (T + 2)) := by
    nlinarith [mul_nonneg (show 0 ≤ q by linarith) hT]
  have hfinal : 48 * q * (T + 3) ≤ (q * (T + 2)) ^ 8 := by
    calc
      _ ≤ 72 * (q * (T + 2)) := hy
      _ ≤ 2 ^ 7 * (q * (T + 2)) := by nlinarith
      _ ≤ (q * (T + 2)) ^ 7 * (q * (T + 2)) :=
        mul_le_mul_of_nonneg_right hpow (by linarith)
      _ = _ := by ring
  have hl := Real.log_le_log (show 0 < 48 * q * (T + 3) by positivity) hfinal
  simpa [Real.log_pow] using hl

/-- The uniform ordinary zero-count rate on the right half of the critical strip. -/
theorem PrimitiveComplexCharacter.right_zero_sum_rate (χ : PrimitiveComplexCharacter)
    (T : ℝ) (hT : 0 ≤ T) (S : Finset ℂ)
    (hS : ∀ z ∈ S, 1 / 2 ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) :
    ∑ z ∈ S, (characterZeroOrder χ z : ℝ) ≤
      (16 / Real.log (14 / 13)) * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)) := by
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have hden : 0 ≤ Real.log (14 / 13 : ℝ) := (Real.log_pos (by norm_num)).le
  calc
    _ ≤ (2 * T + 2) * (Real.log (48 * (χ.modulus : ℝ) * (T + 3)) / Real.log (14 / 13)) :=
      χ.right_zero_sum_bound T hT S hS
    _ ≤ (2 * T + 2) * (8 * Real.log ((χ.modulus : ℝ) * (T + 2)) / Real.log (14 / 13)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (character_zero_log_cost _ _ hq hT) hden) (by linarith)
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFunctionalEquation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reflection of actual character-zero multiplicities

The library functional equation for the completed L-function is combined
with the nonvanishing reciprocal Gamma factor inside the critical strip.
-/

namespace Ostmann

open Filter Set
open scoped Topology

noncomputable def PrimitiveComplexCharacter.inverse (χ : PrimitiveComplexCharacter) :
    PrimitiveComplexCharacter := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact {
    modulus := χ.modulus
    positive := χ.positive
    character := χ.character⁻¹
    primitive := by
      simpa only [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
        using χ.primitive
    nontrivial := inv_ne_one.mpr χ.nontrivial }

@[simp] theorem PrimitiveComplexCharacter.inverse_modulus (χ : PrimitiveComplexCharacter) :
    χ.inverse.modulus = χ.modulus := rfl

noncomputable def PrimitiveComplexCharacter.completed (χ : PrimitiveComplexCharacter) : ℂ → ℂ :=
  @DirichletCharacter.completedLFunction χ.modulus ⟨χ.positive.ne'⟩ χ.character

noncomputable def PrimitiveComplexCharacter.gammaInverse (χ : PrimitiveComplexCharacter) : ℂ → ℂ :=
  fun s => (DirichletCharacter.gammaFactor χ.character s)⁻¹

theorem PrimitiveComplexCharacter.completed_analytic (χ : PrimitiveComplexCharacter) (z : ℂ) :
    AnalyticAt ℂ χ.completed z := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact (DirichletCharacter.differentiable_completedLFunction χ.nontrivial).analyticAt z

theorem PrimitiveComplexCharacter.gammaInverse_analytic (χ : PrimitiveComplexCharacter) (z : ℂ) :
    AnalyticAt ℂ χ.gammaInverse z := by
  classical
  unfold gammaInverse DirichletCharacter.gammaFactor
  split_ifs
  · exact Complex.differentiable_Gammaℝ_inv.analyticAt z
  · exact (Complex.differentiable_Gammaℝ_inv.comp
      (differentiable_id.add_const (1 : ℂ))).analyticAt z

theorem PrimitiveComplexCharacter.gammaInverse_ne_zero (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : 0 < z.re) : χ.gammaInverse z ≠ 0 := by
  classical
  unfold gammaInverse DirichletCharacter.gammaFactor
  split_ifs
  · exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz)
  · apply inv_ne_zero
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using (show 0 < z.re + 1 by linarith))

theorem PrimitiveComplexCharacter.L_eq_completed_mul (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : z ≠ 0) : χ.L z = χ.completed z * χ.gammaInverse z := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact (DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.character z (.inl hz)).trans
    (div_eq_mul_inv _ _)

theorem PrimitiveComplexCharacter.L_order_eq_completed (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : 0 < z.re) : analyticOrderAt χ.L z = analyticOrderAt χ.completed z := by
  have he : χ.L =ᶠ[𝓝 z] fun s => χ.completed s * χ.gammaInverse s := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with s hs
    apply χ.L_eq_completed_mul
    intro heq
    simp [heq] at hs
  rw [analyticOrderAt_congr he]
  rw [show (fun s => χ.completed s * χ.gammaInverse s) = χ.completed * χ.gammaInverse from rfl,
    analyticOrderAt_mul (χ.completed_analytic z) (χ.gammaInverse_analytic z),
    (χ.gammaInverse_analytic z).analyticOrderAt_eq_zero.mpr (χ.gammaInverse_ne_zero z hz), add_zero]

theorem PrimitiveComplexCharacter.rootNumber_ne_zero (χ : PrimitiveComplexCharacter) :
    @DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character ≠ 0 := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  intro hz
  have he := χ.primitive.completedLFunction_one_sub (-1)
  rw [hz, mul_zero, zero_mul] at he
  norm_num at he
  have hL := χ.L_eq_completed_mul 2 (by norm_num)
  change χ.completed 2 = 0 at he
  rw [he, zero_mul] at hL
  have hlo := χ.L_lower_re_two (2 : ℂ) (by norm_num)
  rw [hL, norm_zero] at hlo
  norm_num at hlo

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroReflection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Functional-equation symmetry preserves zero multiplicity -/

namespace Ostmann

open Filter Set
open scoped Topology

theorem PrimitiveComplexCharacter.completed_order_reflection (χ : PrimitiveComplexCharacter)
    (s : ℂ) : analyticOrderAt χ.completed (1 - s) =
      analyticOrderAt χ.inverse.completed s := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  let G : ℂ → ℂ := fun z => (χ.modulus : ℂ) ^ (z - 1 / 2) *
    DirichletCharacter.rootNumber χ.character
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  have hG : AnalyticAt ℂ G s :=
    (((differentiable_id.sub_const (1 / 2 : ℂ)).const_cpow (.inl hq)).mul_const
      (DirichletCharacter.rootNumber χ.character)).analyticAt s
  have hGne : G s ≠ 0 := mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (.inl hq)) χ.rootNumber_ne_zero
  have he : χ.completed ∘ (fun z => 1 - z) = G * χ.inverse.completed := by
    funext z
    exact χ.primitive.completedLFunction_one_sub z
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := χ.completed) (z₀ := s)
    (show AnalyticAt ℂ (fun z => 1 - z) s from analyticAt_const.sub analyticAt_id)
    (show deriv (fun z : ℂ => 1 - z) s ≠ 0 by
      change deriv (fun z : ℂ => 1 - id z) s ≠ 0
      rw [((hasDerivAt_id s).const_sub (1 : ℂ)).deriv]
      norm_num)
  rw [he, analyticOrderAt_mul hG (χ.inverse.completed_analytic s),
    hG.analyticOrderAt_eq_zero.mpr hGne, zero_add] at hcomp
  exact hcomp.symm

theorem PrimitiveComplexCharacter.L_order_reflection (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    analyticOrderAt χ.L (1 - s) = analyticOrderAt χ.inverse.L s := by
  rw [χ.L_order_eq_completed (1 - s) (by simp; linarith),
    χ.inverse.L_order_eq_completed s hs]
  exact χ.completed_order_reflection s

theorem characterZeroOrder_reflection (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 0 < s.re) (hs' : s.re < 1) :
    characterZeroOrder χ (1 - s) = characterZeroOrder χ.inverse s := by
  rw [characterZeroOrder, characterZeroOrder,
    MeromorphicOn.AnalyticOnNhd.divisor_apply
      (show AnalyticOnNhd ℂ χ.L univ from fun z _ => χ.L_analytic z) (mem_univ _),
    MeromorphicOn.AnalyticOnNhd.divisor_apply
      (show AnalyticOnNhd ℂ χ.inverse.L univ from fun z _ => χ.inverse.L_analytic z) (mem_univ _),
    χ.L_order_reflection s hs hs']

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterFullZeroCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Ordinary zero-count bound, with analytic multiplicities -/

namespace Ostmann

open Set
open scoped BigOperators Classical

theorem PrimitiveComplexCharacter.full_zero_sum_rate (χ : PrimitiveComplexCharacter)
    (T : ℝ) (hT : 0 ≤ T) (S : Finset ℂ)
    (hS : ∀ z ∈ S, 0 < z.re ∧ z.re < 1 ∧ |z.im| ≤ T) :
    ∑ z ∈ S, (characterZeroOrder χ z : ℝ) ≤
      (32 / Real.log (14 / 13)) * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)) := by
  let A := S.filter (fun z => 1 / 2 ≤ z.re)
  let B := S.filter (fun z => ¬ 1 / 2 ≤ z.re)
  let C := B.image (fun z : ℂ => 1 - z)
  have hA := χ.right_zero_sum_rate T hT A (by
    intro z hz
    obtain ⟨hzS, hzre⟩ := Finset.mem_filter.mp hz
    exact ⟨hzre, (hS z hzS).2.1.le, (hS z hzS).2.2⟩)
  have hC := χ.inverse.right_zero_sum_rate T hT C (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hzS, hzre⟩ := Finset.mem_filter.mp hz
    obtain ⟨hr, hr', hi⟩ := hS z hzS
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub, abs_neg]
    exact ⟨by linarith, by linarith, hi⟩)
  have heq : ∑ z ∈ B, (characterZeroOrder χ z : ℝ) =
      ∑ w ∈ C, (characterZeroOrder χ.inverse w : ℝ) := by
    dsimp only [C]
    rw [Finset.sum_image (by
      intro z hz w hw he
      exact sub_right_injective he)]
    apply Finset.sum_congr rfl
    intro z hz
    have hzS := (Finset.mem_filter.mp hz).1
    obtain ⟨hr, hr', hi⟩ := hS z hzS
    have hh := characterZeroOrder_reflection χ (1 - z)
      (by simp; linarith) (by simp; linarith)
    rw [show (1 : ℂ) - (1 - z) = z by ring] at hh
    exact_mod_cast hh
  have hsplit : ∑ z ∈ S, (characterZeroOrder χ z : ℝ) =
      (∑ z ∈ A, (characterZeroOrder χ z : ℝ)) + ∑ z ∈ B, (characterZeroOrder χ z : ℝ) := by
    exact (Finset.sum_filter_add_sum_filter_not S (fun z => 1 / 2 ≤ z.re)
      (fun z => (characterZeroOrder χ z : ℝ))).symm
  rw [hsplit, heq]
  simp only [PrimitiveComplexCharacter.inverse_modulus] at hC
  calc
    _ ≤ (16 / Real.log (14 / 13)) * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)) +
        (16 / Real.log (14 / 13)) * (T + 1) * Real.log ((χ.modulus : ℝ) * (T + 2)) :=
      add_le_add hA hC
    _ = _ := by ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroSet
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finiteness and multiplicity of actual zeros in bounded strips -/

namespace Ostmann

open Metric Set MeromorphicOn
open scoped BigOperators Classical

theorem characterZeroOrder_eq_nat (χ : PrimitiveComplexCharacter) (z : ℂ) :
    characterZeroOrder χ z = (analyticOrderNatAt χ.L z : ℤ) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (χ.L_order_ne_top z)
  rw [characterZeroOrder, AnalyticOnNhd.divisor_apply
    (show AnalyticOnNhd ℂ χ.L univ from fun z _ => χ.L_analytic z) (mem_univ z)]
  simp [analyticOrderNatAt, ← hn]

theorem characterZeroOrder_pos_iff (χ : PrimitiveComplexCharacter) (z : ℂ) :
    0 < characterZeroOrder χ z ↔ χ.L z = 0 := by
  rw [characterZeroOrder_eq_nat, Int.natCast_pos]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (χ.L_order_ne_top z)
  have hnat : analyticOrderNatAt χ.L z = n := by simp [analyticOrderNatAt, ← hn]
  rw [hnat]
  have hf := (χ.L_analytic z).analyticOrderAt_ne_zero
  have hnzero : n ≠ 0 ↔ χ.L z = 0 := by simpa only [← hn, Nat.cast_ne_zero] using hf
  exact Nat.pos_iff_ne_zero.trans hnzero

def complexCharacterZeros (χ : PrimitiveComplexCharacter) : Set ℂ :=
  {z | 0 < z.re ∧ z.re < 1 ∧ χ.L z = 0}

theorem PrimitiveComplexCharacter.strip_zeros_finite (χ : PrimitiveComplexCharacter) (T : ℝ) :
    {z : ℂ | z ∈ complexCharacterZeros χ ∧ |z.im| ≤ T}.Finite := by
  by_cases hT : 0 ≤ T
  · let K := closedBall (0 : ℂ) (T + 1)
    have ha : AnalyticOnNhd ℂ χ.L K := fun z _ => χ.L_analytic z
    apply ((divisor χ.L K).finiteSupport (isCompact_closedBall _ _)).subset
    intro z hz
    obtain ⟨⟨hr, hr', hzero⟩, hi⟩ := hz
    have hzK : z ∈ K := by
      rw [mem_closedBall, dist_zero_right]
      have hn := Complex.norm_le_abs_re_add_abs_im z
      rw [abs_of_pos hr] at hn
      linarith
    have hdiv : divisor χ.L K z = characterZeroOrder χ z := by
      rw [ha.divisor_apply hzK, characterZeroOrder,
        AnalyticOnNhd.divisor_apply
          (show AnalyticOnNhd ℂ χ.L univ from fun z _ => χ.L_analytic z) (mem_univ z)]
    change divisor χ.L K z ≠ 0
    rw [hdiv]
    exact ne_of_gt ((characterZeroOrder_pos_iff χ z).mpr hzero)
  · have he : {z : ℂ | z ∈ complexCharacterZeros χ ∧ |z.im| ≤ T} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hT ((abs_nonneg z.im).trans hz.2)
    rw [he]
    exact finite_empty

theorem PrimitiveComplexCharacter.zeros_countable (χ : PrimitiveComplexCharacter) :
    (complexCharacterZeros χ).Countable := by
  apply (Set.countable_iUnion (fun n : ℕ => (χ.strip_zeros_finite (n : ℝ)).countable)).mono
  intro z hz
  obtain ⟨n, hn⟩ := exists_nat_ge |z.im|
  exact Set.mem_iUnion.mpr ⟨n, hz, hn⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterContourZeros
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The only zeros crossed by the fixed smooth contour

Between Re(s)=-1/2 and Re(s)=2 the poles of the logarithmic derivative are
precisely the critical-strip zeros, together with the possible zero at zero.
-/

namespace Ostmann

open Complex

theorem PrimitiveComplexCharacter.L_ne_zero_one_le_re (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : 1 ≤ z.re) : χ.L z ≠ 0 := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.character (.inl χ.nontrivial) hz

theorem PrimitiveComplexCharacter.completed_ne_zero_left (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : z.re ≤ 0) : χ.completed z ≠ 0 := by
  apply (χ.completed_analytic z).analyticOrderAt_eq_zero.mp
  have hpos : 0 < (1 - z).re := by simp; linarith
  have hge : 1 ≤ (1 - z).re := by simp; linarith
  calc
    analyticOrderAt χ.completed z = analyticOrderAt χ.inverse.completed (1 - z) := by
      simpa using χ.completed_order_reflection (1 - z)
    _ = analyticOrderAt χ.inverse.L (1 - z) := (χ.inverse.L_order_eq_completed _ hpos).symm
    _ = 0 := (χ.inverse.L_analytic _).analyticOrderAt_eq_zero.mpr
      (χ.inverse.L_ne_zero_one_le_re _ hge)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaStripBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for Gamma on the positive vertical strips used by the contour -/

namespace Ostmann

open Complex MeasureTheory Set

/-- The Euler integral bounds Gamma at a complex point by its real value. -/
theorem gamma_norm_le_real (z : ℂ) (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Complex.GammaIntegral, Real.Gamma_eq_integral hz]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp [Complex.norm_exp]

theorem gamma_positive_strip_bound (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖Complex.Gamma z‖ ≤ C := by
  have hc : ContinuousOn Real.Gamma (Icc a b) := by
    intro x hx
    apply (Real.differentiableAt_Gamma (fun n => ?_)).continuousAt.continuousWithinAt
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [hx.1]
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hza hzb
  calc
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := gamma_norm_le_real z (lt_of_lt_of_le ha hza)
    _ ≤ ‖Real.Gamma z.re‖ := le_abs_self _
    _ ≤ C := hC z.re ⟨hza, hzb⟩
    _ ≤ max C 1 := le_max_left _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_AnalyticLogBall
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A normalized logarithm on a zero-free disk

This is the local analytic bridge used to bound logarithmic derivatives on
zero-free disks. It is obtained by integrating the actual logarithmic derivative.
-/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

theorem exists_normalized_log_on_ball (g : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (hne : ∀ z ∈ ball 0 R, g z ≠ 0) :
    ∃ F : ℂ → ℂ, F 0 = 0 ∧ (∀ z ∈ ball 0 R, HasDerivAt F (logDeriv g z) z) ∧
      ∀ z ∈ ball 0 R, g z = g 0 * exp (F z) := by
  have hd : DifferentiableOn ℂ (logDeriv g) (ball 0 R) := by
    intro z hz
    exact ((hg z hz).deriv.div (hg z hz) (hne z hz)).differentiableWithinAt
  obtain ⟨F, hF0, hF⟩ := hd.isExactOn_ball.with_val_at 0 0
  refine ⟨F, hF0, hF, ?_⟩
  let H : ℂ → ℂ := fun z => g z * exp (-F z)
  have hH (z : ℂ) (hz : z ∈ ball 0 R) : HasDerivAt H 0 z := by
    have h := (hg z hz).differentiableAt.hasDerivAt.mul ((hF z hz).neg.cexp)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [logDeriv_apply]
    field_simp [hne z hz]
    ring
  have hHD : DifferentiableOn ℂ H (ball 0 R) := fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  intro z hz
  have hc := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) R).isPreconnected
    hHD (fun w hw => (hH w hw).deriv) hz (mem_ball_self hR)
  change g z * exp (-F z) = g 0 * exp (-F 0) at hc
  rw [hF0, neg_zero, exp_zero, mul_one, exp_neg] at hc
  have hmul := congrArg (fun w : ℂ => w * exp (F z)) hc
  simpa [mul_assoc, exp_ne_zero] using hmul

theorem normalized_log_re (g F : ℂ → ℂ) (z : ℂ) (hg0 : g 0 ≠ 0)
    (he : g z = g 0 * exp (F z)) :
    (F z).re = Real.log ‖g z‖ - Real.log ‖g 0‖ := by
  have hnorm := congrArg norm he
  rw [norm_mul, norm_exp] at hnorm
  have hh := congrArg Real.log hnorm
  rw [Real.log_mul (norm_ne_zero_iff.mpr hg0) (Real.exp_ne_zero _), Real.log_exp] at hh
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaRealLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic derivatives of the archimedean Gamma factor -/

namespace Ostmann

open Complex

theorem gammaReal_logDeriv (s : ℂ) (hs : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    logDeriv Complex.Gammaℝ s = (Complex.digamma (s / 2) - Complex.log (Real.pi : ℂ)) / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  let p : ℂ → ℂ := fun u => (Real.pi : ℂ) ^ (-u / 2)
  have hpne : p s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hpi)
  have hp := (((hasDerivAt_id s).neg).div_const 2).const_cpow (.inl hpi)
  have hplog : logDeriv p s = -(Complex.log (Real.pi : ℂ)) / 2 := by
    rw [logDeriv_apply, show deriv p s = p s * Complex.log (Real.pi : ℂ) * (-1 / 2) from hp.deriv]
    field_simp [hpne]
  have hgamma : logDeriv (fun u : ℂ => Complex.Gamma (u / 2)) s = Complex.digamma (s / 2) / 2 := by
    have h := logDeriv_comp (f := Complex.Gamma) (g := fun u : ℂ => u / 2) (x := s)
      (Complex.differentiableAt_Gamma _ hs) (differentiableAt_id.div_const 2)
    have hd : deriv (fun u : ℂ => u / 2) s = 1 / 2 := by
      simpa using ((hasDerivAt_id s).div_const 2).deriv
    rw [hd] at h
    change logDeriv (Complex.Gamma ∘ fun u : ℂ => u / 2) s = _
    rw [h, Complex.digamma_def]
    ring
  have hgd : DifferentiableAt ℂ (fun u : ℂ => Complex.Gamma (u / 2)) s :=
    (Complex.differentiableAt_Gamma _ hs).comp s (differentiableAt_id.div_const 2)
  have he : Complex.Gammaℝ = fun u => p u * Complex.Gamma (u / 2) := rfl
  rw [he, logDeriv_mul (f := p) (g := fun u => Complex.Gamma (u / 2)) s hpne
    (Complex.Gamma_ne_zero hs) hp.differentiableAt hgd, hplog, hgamma]
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaRealContourBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounds for the real-place Gamma factor on the shifted contour -/

namespace Ostmann

open Complex

theorem gammaReal_differentiableAt (s : ℂ) (hs : ∀ n : ℕ, s / 2 ≠ -(n : ℂ)) :
    DifferentiableAt ℂ Complex.Gammaℝ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact (((differentiableAt_id.neg).div_const 2).const_cpow (.inl hpi)).mul
    ((Complex.differentiableAt_Gamma _ hs).comp s (differentiableAt_id.div_const 2))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCompletedLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The functional equation at the level of logarithmic derivatives -/

namespace Ostmann

open Complex
open scoped Classical

theorem PrimitiveComplexCharacter.L_eq_completed_mul_all (χ : PrimitiveComplexCharacter) :
    χ.L = χ.completed * χ.gammaInverse := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hq : χ.modulus ≠ 1 := fun h => χ.nontrivial (DirichletCharacter.level_one' χ.character h)
  funext s
  exact (DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.character s (.inr hq)).trans
    (div_eq_mul_inv _ _)

theorem PrimitiveComplexCharacter.completed_ne_zero_right
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 1 ≤ s.re) : χ.completed s ≠ 0 := by
  have h := χ.L_ne_zero_one_le_re s hs
  rw [χ.L_eq_completed_mul_all] at h
  exact (mul_ne_zero_iff.mp h).1

theorem PrimitiveComplexCharacter.completed_logDeriv_reflection
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 1 ≤ s.re) :
    logDeriv χ.completed (1 - s) =
      -Complex.log (χ.modulus : ℂ) - logDeriv χ.inverse.completed s := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  let G : ℂ → ℂ := fun z => (χ.modulus : ℂ) ^ (z - 1 / 2) *
    DirichletCharacter.rootNumber χ.character
  have hq : (χ.modulus : ℂ) ≠ 0 := by exact_mod_cast χ.positive.ne'
  have hp := ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).const_cpow (.inl hq)
  simp only [id_eq, mul_one] at hp
  have hpne : (χ.modulus : ℂ) ^ (s - 1 / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (.inl hq)
  have hG : DifferentiableAt ℂ G s := hp.differentiableAt.mul_const _
  have hGne : G s ≠ 0 := mul_ne_zero hpne χ.rootNumber_ne_zero
  have hGlog : logDeriv G s = Complex.log (χ.modulus : ℂ) := by
    rw [show G = (fun z => (χ.modulus : ℂ) ^ (z - 1 / 2) *
      DirichletCharacter.rootNumber χ.character) from rfl,
      logDeriv_mul_const s _ χ.rootNumber_ne_zero, logDeriv_apply, hp.deriv]
    rw [mul_div_right_comm, div_self hpne, one_mul]
  have he : χ.completed ∘ (fun z => 1 - z) = fun z => G z * χ.inverse.completed z := by
    funext z
    exact χ.primitive.completedLFunction_one_sub z
  have hl := congrArg (fun f : ℂ → ℂ => logDeriv f s) he
  rw [logDeriv_comp (χ.completed_analytic (1 - s)).differentiableAt
      ((hasDerivAt_id s).const_sub 1).differentiableAt,
    logDeriv_mul s hGne (χ.inverse.completed_ne_zero_right s hs) hG
      (χ.inverse.completed_analytic s).differentiableAt, hGlog] at hl
  have hd : deriv (fun z : ℂ => 1 - z) s = -1 := by
    simp
  rw [hd] at hl
  linear_combination -hl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaFactorialGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A factorial bound for Gamma on expanding right-half-plane disks -/

namespace Ostmann

open Complex

theorem gamma_factorial_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (s : ℂ), (1 / 4 : ℝ) ≤ s.re → s.re ≤ (N : ℝ) + 2 →
      ‖Complex.Gamma s‖ ≤ C + ((N + 1).factorial : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := gamma_positive_strip_bound (1 / 4) 2 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro N s hs hs'
  by_cases hsmall : s.re ≤ 2
  · exact (hbound s hs hsmall).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  · have hpos : 0 < s.re := by linarith
    have hm : Real.Gamma s.re ≤ Real.Gamma ((N : ℝ) + 2) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn (by change 2 ≤ s.re; linarith)
        (by change 2 ≤ (N : ℝ) + 2; linarith [Nat.cast_nonneg (α := ℝ) N]) hs'
    have he : Real.Gamma ((N : ℝ) + 2) = ((N + 1).factorial : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
        Real.Gamma_nat_eq_factorial (N + 1)
    calc
      _ ≤ Real.Gamma s.re := gamma_norm_le_real s hpos
      _ ≤ Real.Gamma ((N : ℝ) + 2) := hm
      _ = _ := he
      _ ≤ _ := le_add_of_nonneg_left hC.le

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterGammaFactorialGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Factorial growth for the archimedean factors on expanding disks -/

namespace Ostmann

open Complex

theorem gammaReal_factorial_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (s : ℂ), (1 / 2 : ℝ) ≤ s.re → s.re ≤ (N : ℝ) + 2 →
      ‖Complex.Gammaℝ s‖ ≤ C + ((N + 1).factorial : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := gamma_factorial_growth
  refine ⟨C, hC, ?_⟩
  intro N s hs hs'
  have hg := hbound N (s / 2) (by simp; linarith) (by simp; linarith [Nat.cast_nonneg (α := ℝ) N])
  have hp : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi)
    simp
    linarith
  rw [Complex.Gammaℝ_def, norm_mul]
  exact (mul_le_mul hp hg (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem characterGamma_factorial_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (N : ℕ) (s : ℂ),
      (1 / 2 : ℝ) ≤ s.re → s.re ≤ (N : ℝ) + 1 →
      ‖DirichletCharacter.gammaFactor χ.character s‖ ≤ C + ((N + 1).factorial : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := gammaReal_factorial_growth
  refine ⟨C, hC, ?_⟩
  intro χ N s hs hs'
  classical
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact hbound N s hs (by linarith)
  · exact hbound N (s + 1) (by simp; linarith) (by simp; linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCompletedRightGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual completed L-function growth in the right half-plane -/

namespace Ostmann

open Complex

theorem PrimitiveComplexCharacter.completed_eq_L_mul_gamma
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 0 < s.re) :
    χ.completed s = χ.L s * DirichletCharacter.gammaFactor χ.character s := by
  have hgne : DirichletCharacter.gammaFactor χ.character s ≠ 0 := by
    intro h
    have hh := χ.gammaInverse_ne_zero s hs
    apply hh
    change (DirichletCharacter.gammaFactor χ.character s)⁻¹ = 0
    rw [h, inv_zero]
  have hL := congrFun χ.L_eq_completed_mul_all s
  change χ.L s = χ.completed s / DirichletCharacter.gammaFactor χ.character s at hL
  exact ((eq_div_iff hgne).mp hL).symm

theorem character_completed_right_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (N : ℕ) (s : ℂ),
      (1 / 2 : ℝ) ≤ s.re → ‖s‖ ≤ (N : ℝ) + 1 →
      ‖χ.completed s‖ ≤ 2 * ((N : ℝ) + 1) * ((χ.modulus : ℝ) + 1) *
        (C + ((N + 1).factorial : ℝ)) := by
  obtain ⟨C, hC, hgamma⟩ := characterGamma_factorial_growth
  refine ⟨C, hC, ?_⟩
  intro χ N s hs hn
  have hspos : 0 < s.re := by linarith
  have hl : ‖χ.L s‖ ≤ 2 * ((N : ℝ) + 1) * ((χ.modulus : ℝ) + 1) := by
    apply (χ.L_norm_bound_positive s hspos).trans
    apply (div_le_iff₀ hspos).mpr
    have hb := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ (χ.modulus : ℝ) + 1)
    have hc := mul_le_mul_of_nonneg_left hs (by positivity :
      0 ≤ 2 * ((N : ℝ) + 1) * ((χ.modulus : ℝ) + 1))
    nlinarith
  have hg := hgamma χ N s hs ((le_abs_self s.re).trans ((abs_re_le_norm s).trans hn))
  rw [χ.completed_eq_L_mul_gamma s hspos, norm_mul]
  exact mul_le_mul hl hg (norm_nonneg _) (by positivity)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterRootNumberBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A sufficient elementary bound for the character root number -/

namespace Ostmann

open Complex
open scoped BigOperators Classical

/-- The triangle inequality is sufficient for the growth estimate; no sharp
Gauss-sum evaluation is required here. -/
theorem PrimitiveComplexCharacter.rootNumber_norm_le (χ : PrimitiveComplexCharacter) :
    ‖@DirichletCharacter.rootNumber χ.modulus ⟨χ.positive.ne'⟩ χ.character‖ ≤ χ.modulus := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  have hG : ‖gaussSum χ.character ZMod.stdAddChar‖ ≤ (χ.modulus : ℝ) := by
    unfold gaussSum
    calc
      _ ≤ ∑ x : ZMod χ.modulus, ‖χ.character x * ZMod.stdAddChar x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : ZMod χ.modulus, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        have hnorm : ‖ZMod.stdAddChar x‖ = 1 := by simp [ZMod.stdAddChar_apply]; exact Circle.norm_coe _
        rw [norm_mul, hnorm, mul_one]
        exact χ.character.norm_le_one x
      _ = _ := by simp
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hp : 1 ≤ ‖(χ.modulus : ℂ) ^ (1 / 2 : ℂ)‖ := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.one_le_rpow hq
    norm_num
  simp only [DirichletCharacter.rootNumber, norm_div, norm_pow, norm_I, one_pow, div_one]
  apply (div_le_iff₀ (by linarith : 0 < ‖(χ.modulus : ℂ) ^ (1 / 2 : ℂ)‖)).mpr
  nlinarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCompletedDiskGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A factorial growth bound for the entire completed L-function -/

namespace Ostmann

open Complex

theorem character_completed_disk_growth : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (N : ℕ) (s : ℂ), ‖s‖ ≤ (N : ℝ) + 1 →
      ‖χ.completed s‖ ≤ 2 * ((N : ℝ) + 2) * ((χ.modulus : ℝ) + 1) *
        (χ.modulus : ℝ) ^ (N + 3) * (C + ((N + 2).factorial : ℝ)) := by
  obtain ⟨C, hC, hright⟩ := character_completed_right_growth
  refine ⟨C, hC, ?_⟩
  intro χ N s hs
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hqpos : 0 < (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hn : ‖s‖ ≤ ((N + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
  by_cases hr : 1 / 2 ≤ s.re
  · have hh := hright χ (N + 1) s hr hn
    push_cast at hh
    calc
      _ ≤ 2 * ((N : ℝ) + 2) * ((χ.modulus : ℝ) + 1) * (C + ((N + 2).factorial : ℝ)) := by
        simpa only [show N + 1 + 1 = N + 2 by omega,
          show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring] using hh
      _ ≤ _ := by
        have hp : 1 ≤ (χ.modulus : ℝ) ^ (N + 3) := one_le_pow₀ hq
        nlinarith [mul_le_mul_of_nonneg_left hp (by positivity :
          0 ≤ 2 * ((N : ℝ) + 2) * ((χ.modulus : ℝ) + 1) * (C + ((N + 2).factorial : ℝ)))]
  · let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
    have hns : ‖1 - s‖ ≤ ((N + 1 : ℕ) : ℝ) + 1 := by
      have hh := norm_sub_le (1 : ℂ) s
      norm_num at hh
      push_cast
      linarith
    have hw := hright χ.inverse (N + 1) (1 - s) (by simp; linarith) hns
    simp only [PrimitiveComplexCharacter.inverse_modulus, Nat.cast_add, Nat.cast_one] at hw
    have hp : ‖(χ.modulus : ℂ) ^ (1 / 2 - s)‖ ≤ (χ.modulus : ℝ) ^ (N + 2) := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
      calc
        _ ≤ (χ.modulus : ℝ) ^ ((N + 2 : ℕ) : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hq
          have hh := abs_re_le_norm s
          simp only [sub_re, div_ofNat_re, one_re]
          push_cast
          linarith [(abs_le.mp (hh.trans hs)).1]
        _ = _ := Real.rpow_natCast _ _
    have hf := χ.primitive.completedLFunction_one_sub (1 - s)
    rw [show (1 : ℂ) - (1 - s) = s by ring,
      show (1 : ℂ) - s - 1 / 2 = 1 / 2 - s by ring] at hf
    change χ.completed s = (χ.modulus : ℂ) ^ (1 / 2 - s) *
      DirichletCharacter.rootNumber χ.character * χ.inverse.completed (1 - s) at hf
    rw [hf, norm_mul, norm_mul]
    calc
      _ ≤ (χ.modulus : ℝ) ^ (N + 2) * (χ.modulus : ℝ) *
          (2 * ((N : ℝ) + 1 + 1) * ((χ.modulus : ℝ) + 1) *
            (C + ((N + 1 + 1).factorial : ℝ))) := by
        exact mul_le_mul (mul_le_mul hp χ.rootNumber_norm_le (norm_nonneg _) (by positivity))
          hw (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show N + 1 + 1 = N + 2 by omega,
          show N + 3 = (N + 2) + 1 by omega, pow_succ]
        ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterRightLogDerivativeBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform logarithmic derivative bound to the right of two -/

namespace Ostmann

open Complex

/-- Absolute convergence supplies a single bound for every primitive character. -/
theorem character_logDeriv_right_uniform_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 2 ≤ s.re → ‖logDeriv χ.L s‖ ≤ C := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let C : ℝ := ∑' n, ‖LSeries.term f (2 : ℂ) n‖
  have hsum : LSeriesSummable f (2 : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hC : 0 ≤ C := tsum_nonneg (fun _ => norm_nonneg _)
  refine ⟨C + 1, by positivity, ?_⟩
  intro χ s hs
  have hcs : LSeriesSummable (characterMangoldtCoefficient χ) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character (by linarith)
  have hterm (n : ℕ) : ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ ≤
      ‖LSeries.term f (2 : ℂ) n‖ := by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    rw [show (2 : ℂ).re = (2 : ℝ) by norm_num]
    split_ifs with hn
    · exact le_rfl
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      apply div_le_div₀ (norm_nonneg _) _ (Real.rpow_pos_of_pos hnpos _)
        (Real.rpow_le_rpow_of_exponent_le hn1 hs)
      dsimp only [characterMangoldtCoefficient, f]
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (χ.character.norm_le_one _)
  calc
    ‖logDeriv χ.L s‖ = ‖LSeries (characterMangoldtCoefficient χ) s‖ := by
      rw [χ.mangoldt_LSeries_eq s (by linarith), logDeriv_apply, neg_div, norm_neg]
    _ ≤ ∑' n, ‖LSeries.term (characterMangoldtCoefficient χ) s n‖ :=
      norm_tsum_le_tsum_norm hcs.norm
    _ ≤ C := hcs.norm.tsum_le_tsum hterm hsum.norm
    _ ≤ C + 1 := by linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_GammaLogDerivativeGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Divergence of the Gamma logarithmic derivative at positive integers -/

namespace Ostmann

open Complex Filter
open scoped Topology

theorem gamma_logDeriv_nat (n : ℕ) :
    logDeriv Complex.Gamma ((n : ℂ) + 1) =
      (-Real.eulerMascheroniConstant + (harmonic n : ℝ) : ℂ) := by
  rw [logDeriv_apply, Complex.deriv_Gamma_nat, Complex.Gamma_nat_eq_factorial]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [mul_div_cancel_left₀ _ hn]
  push_cast
  rfl

theorem gamma_logDeriv_nat_re_tendsto :
    Tendsto (fun n : ℕ => (logDeriv Complex.Gamma ((n : ℂ) + 1)).re) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have h1 := Real.tendsto_harmonic_sub_log.eventually
    (lt_mem_nhds (show Real.eulerMascheroniConstant - 1 < Real.eulerMascheroniConstant by linarith))
  have h2 := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (b + 1)
  filter_upwards [h1, h2] with n hn hn'
  simp only [Function.comp_apply] at hn'
  rw [gamma_logDeriv_nat]
  simp only [add_re, neg_re, ofReal_re]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterGammaGrowthSequence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An explicit sequence on which the character Gamma logarithmic derivative diverges -/

namespace Ostmann

open Complex Filter
open scoped Topology Classical

noncomputable def characterGammaSample (χ : PrimitiveComplexCharacter) (n : ℕ) : ℂ :=
  if χ.character.Even then 2 * ((n : ℂ) + 1) else 2 * (n : ℂ) + 1

theorem characterGammaSample_re_lower (χ : PrimitiveComplexCharacter) (n : ℕ) :
    2 * (n : ℝ) + 1 ≤ (characterGammaSample χ n).re := by
  unfold characterGammaSample
  split_ifs <;> simp
  linarith

theorem gammaReal_logDeriv_double_nat (n : ℕ) :
    logDeriv Complex.Gammaℝ (2 * ((n : ℂ) + 1)) =
      ((-Real.eulerMascheroniConstant + (harmonic n : ℝ) - Real.log Real.pi) / 2 : ℝ) := by
  have harg : 2 * ((n : ℂ) + 1) / 2 = (n : ℂ) + 1 := by ring
  have hn : ∀ k : ℕ, (n : ℂ) + 1 ≠ -(k : ℂ) := by
    intro k hk
    have hh := congrArg Complex.re hk
    simp only [add_re, natCast_re, one_re, neg_re] at hh
    have := Nat.cast_nonneg (α := ℝ) n
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [gammaReal_logDeriv _ (by rwa [harg]), harg, Complex.digamma_def,
    gamma_logDeriv_nat, ← Complex.ofReal_log Real.pi_pos.le]
  push_cast
  rfl

theorem characterGamma_logDeriv_sample (χ : PrimitiveComplexCharacter) (n : ℕ) :
    logDeriv (DirichletCharacter.gammaFactor χ.character) (characterGammaSample χ n) =
      ((-Real.eulerMascheroniConstant + (harmonic n : ℝ) - Real.log Real.pi) / 2 : ℝ) := by
  by_cases hc : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    simpa [characterGammaSample, hc] using gammaReal_logDeriv_double_nat n
  · have he : DirichletCharacter.gammaFactor χ.character =
        Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) := by
      funext u
      simp [DirichletCharacter.gammaFactor, hc]
    rw [he]
    simp only [characterGammaSample, hc, ↓reduceIte]
    have ha : 2 * (n : ℂ) + 1 + 1 = 2 * ((n : ℂ) + 1) := by ring
    have hreg : ∀ k : ℕ, (2 * (n : ℂ) + 1 + 1) / 2 ≠ -(k : ℂ) := by
      intro k hk
      have hh := congrArg Complex.re hk
      norm_num at hh
      have := Nat.cast_nonneg (α := ℝ) n
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    rw [logDeriv_comp (g := fun u : ℂ => u + 1) (x := 2 * (n : ℂ) + 1)
      (gammaReal_differentiableAt _ hreg)
      (differentiableAt_id.add_const (1 : ℂ))]
    simpa only [deriv_add_const, deriv_id'', mul_one, ha] using gammaReal_logDeriv_double_nat n

theorem characterGamma_logDeriv_sample_re_tendsto (χ : PrimitiveComplexCharacter) :
    Tendsto (fun n => (logDeriv (DirichletCharacter.gammaFactor χ.character)
      (characterGammaSample χ n)).re) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hh := gamma_logDeriv_nat_re_tendsto.eventually_ge_atTop (2 * b + Real.log Real.pi)
  filter_upwards [hh] with n hn
  rw [characterGamma_logDeriv_sample]
  rw [gamma_logDeriv_nat] at hn
  simp only [add_re, neg_re, ofReal_re] at hn ⊢
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCompletedDivergence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Growth of the completed logarithmic derivative on the positive real axis -/

namespace Ostmann

open Complex Filter Set
open scoped Topology Classical

theorem PrimitiveComplexCharacter.gammaFactor_differentiableAt_pos
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 0 < s.re) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ.character) s := by
  have hreg (z : ℂ) (hz : 0 < z.re) : ∀ k : ℕ, z / 2 ≠ -(k : ℂ) := by
    intro k hk
    have hh := congrArg Complex.re hk
    simp only [div_ofNat_re, neg_re, natCast_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) k]
  by_cases hc : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    exact gammaReal_differentiableAt s (hreg s hs)
  · rw [show DirichletCharacter.gammaFactor χ.character =
        Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, hc])]
    exact (gammaReal_differentiableAt (s + 1)
      (hreg _ (by simpa using (show 0 < s.re + 1 by linarith)))).comp
      (f := fun u : ℂ => u + 1) s (differentiableAt_id.add_const (1 : ℂ))

theorem PrimitiveComplexCharacter.completed_logDeriv_eq_add
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 1 ≤ s.re) :
    logDeriv χ.completed s = logDeriv χ.L s +
      logDeriv (DirichletCharacter.gammaFactor χ.character) s := by
  have hspos : 0 < s.re := by linarith
  have hne : DirichletCharacter.gammaFactor χ.character s ≠ 0 := by
    have hh := χ.gammaInverse_ne_zero s hspos
    intro hz
    apply hh
    simp [PrimitiveComplexCharacter.gammaInverse, hz]
  have he : χ.completed =ᶠ[𝓝 s] (fun z => χ.L z * DirichletCharacter.gammaFactor χ.character z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hspos] with z hz
    exact χ.completed_eq_L_mul_gamma z hz
  rw [(logDeriv_congr_nhds he).self_of_nhds]
  exact logDeriv_mul s (χ.L_ne_zero_one_le_re s hs) hne
    (χ.L_analytic s).differentiableAt (χ.gammaFactor_differentiableAt_pos s hspos)

/-- The Gamma term dominates the uniformly bounded absolutely convergent L-series term. -/
theorem completed_logDeriv_sample_re_tendsto (χ : PrimitiveComplexCharacter) :
    Tendsto (fun n => (logDeriv χ.completed (characterGammaSample χ n)).re) atTop atTop := by
  obtain ⟨C, hC, hbound⟩ := character_logDeriv_right_uniform_bound
  apply tendsto_atTop.2
  intro b
  have hh := (characterGamma_logDeriv_sample_re_tendsto χ).eventually_ge_atTop (b + C)
  filter_upwards [hh, eventually_ge_atTop 1] with n hn hn1
  have hs2 : 2 ≤ (characterGammaSample χ n).re := by
    have hb := characterGammaSample_re_lower χ n
    have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hb := hbound χ (characterGammaSample χ n) hs2
  have hr := (neg_le_abs ((logDeriv χ.L (characterGammaSample χ n)).re)).trans
    (abs_re_le_norm (logDeriv χ.L (characterGammaSample χ n)))
  rw [χ.completed_logDeriv_eq_add _ (by linarith), add_re]
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterCompletedZeros
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The zeros of the entire completed character L-function -/

namespace Ostmann

open Complex

theorem PrimitiveComplexCharacter.completed_order_ne_top (χ : PrimitiveComplexCharacter)
    (z : ℂ) : analyticOrderAt χ.completed z ≠ ⊤ := by
  intro h
  have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z χ.completed_analytic).mp h
  exact χ.completed_ne_zero_right 2 (by norm_num) (congrFun he 2)

theorem PrimitiveComplexCharacter.completed_zero_iff (χ : PrimitiveComplexCharacter)
    (z : ℂ) : χ.completed z = 0 ↔ z ∈ complexCharacterZeros χ := by
  constructor
  · intro hz
    have hpos : 0 < z.re := by
      by_contra h
      exact χ.completed_ne_zero_left z (not_lt.mp h) hz
    have hlt : z.re < 1 := by
      by_contra h
      exact χ.completed_ne_zero_right z (not_lt.mp h) hz
    refine ⟨hpos, hlt, ?_⟩
    have he := congrFun χ.L_eq_completed_mul_all z
    change χ.L z = χ.completed z * χ.gammaInverse z at he
    rw [he, hz, zero_mul]
  · rintro ⟨hpos, _, hzero⟩
    have he := congrFun χ.L_eq_completed_mul_all z
    change χ.L z = χ.completed z * χ.gammaInverse z at he
    rw [hzero] at he
    exact (mul_eq_zero.mp he.symm).resolve_right (χ.gammaInverse_ne_zero z hpos)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FiniteAnalyticZeroFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite zero-factor removal for the completed-character application -/

namespace Ostmann

open Filter Set
open scoped Topology BigOperators Classical

noncomputable def finiteZeroPolynomial (f : ℂ → ℂ)
    (S : Finset ℂ) (s : ℂ) : ℂ :=
  ∏ z ∈ S, (s - z) ^ analyticOrderNatAt f z

theorem finiteZeroPolynomial_analytic (f : ℂ → ℂ)
    (S : Finset ℂ) (s : ℂ) : AnalyticAt ℂ (finiteZeroPolynomial f S) s := by
  exact S.analyticAt_fun_prod fun z _ => (analyticAt_id.sub analyticAt_const).pow _

theorem finiteZeroPolynomial_ne_zero (f : ℂ → ℂ)
    (S : Finset ℂ) (s : ℂ) (hs : s ∉ S) : finiteZeroPolynomial f S s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hs (he ▸ hz)))

theorem finiteZeroPolynomial_insert (f : ℂ → ℂ)
    (S : Finset ℂ) (z s : ℂ) (hz : z ∈ S) :
    finiteZeroPolynomial f S s =
      (s - z) ^ analyticOrderNatAt f z * finiteZeroPolynomial f (S.erase z) s := by
  exact (Finset.mul_prod_erase S _ hz).symm

/-- The quotient by any finite collection of complete zero factors extends
analytically to the whole plane. It is nonzero at each removed zero. -/
theorem remove_finite_analytic_zeros (f : ℂ → ℂ)
    (hf : ∀ z, AnalyticAt ℂ f z) (horder : ∀ z, analyticOrderAt f z ≠ ⊤) (S : Finset ℂ) :
    ∃ g : ℂ → ℂ, (∀ s, AnalyticAt ℂ g s) ∧
      (∀ s, f s = finiteZeroPolynomial f S s * g s) ∧
      (∀ s ∈ S, g s ≠ 0) := by
  choose R hR hRne heR using fun z =>
    (hf z).analyticOrderAt_ne_top.mp (horder z)
  let g : ℂ → ℂ := fun z => if z ∈ S then
    R z z / finiteZeroPolynomial f (S.erase z) z
    else f z / finiteZeroPolynomial f S z
  have hlocal (z : ℂ) (hz : z ∈ S) :
      g =ᶠ[𝓝 z] fun s => R z s / finiteZeroPolynomial f (S.erase z) s := by
    have hav : ∀ᶠ s in 𝓝 z, s ∉ S.erase z :=
      (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [hav, heR z] with s hs he
    by_cases hsz : s = z
    · subst s
      simp only [g, ite_eq_left hz]
    · have hsS : s ∉ S := fun h => hs (Finset.mem_erase.mpr ⟨hsz, h⟩)
      simp only [g, ite_eq_right hsS]
      rw [finiteZeroPolynomial_insert f S z s hz, he]
      simp only [smul_eq_mul]
      exact mul_div_mul_left _ _ (pow_ne_zero _ (sub_ne_zero.mpr hsz))
  have ha : ∀ s, AnalyticAt ℂ g s := by
    intro s
    by_cases hs : s ∈ S
    · exact ((hR s).div (finiteZeroPolynomial_analytic f (S.erase s) s)
        (finiteZeroPolynomial_ne_zero f (S.erase s) s (by simp))).congr
          (hlocal s hs).symm
    · apply ((hf s).div (finiteZeroPolynomial_analytic f S s)
        (finiteZeroPolynomial_ne_zero f S s hs)).congr
      have hav : ∀ᶠ z in 𝓝 s, z ∉ S := S.finite_toSet.isClosed.isOpen_compl.mem_nhds hs
      filter_upwards [hav] with z hz
      simp only [g, ite_eq_right hz, Pi.div_apply]
  refine ⟨g, ha, ?_, ?_⟩
  · intro s
    by_cases hs : s ∈ S
    · rw [(hlocal s hs).self_of_nhds, finiteZeroPolynomial_insert f S s s hs]
      have he := (heR s).self_of_nhds
      simp only [smul_eq_mul] at he
      rw [he]
      field_simp [finiteZeroPolynomial_ne_zero f (S.erase s) s (by simp)]
    · simp only [g, ite_eq_right hs]
      exact (mul_div_cancel₀ _ (finiteZeroPolynomial_ne_zero f S s hs)).symm
  · intro s hs
    simp only [g, ite_eq_left hs]
    exact div_ne_zero (hRne s) (finiteZeroPolynomial_ne_zero f (S.erase s) s (by simp))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCompletedFiniteFactors
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Consequences of a finite nontrivial zero set for the completed function -/

namespace Ostmann

open Set
open scoped Classical

theorem character_completed_finite_factors (χ : PrimitiveComplexCharacter)
    (hfinite : (complexCharacterZeros χ).Finite) :
    ∃ g : ℂ → ℂ, (∀ s, AnalyticAt ℂ g s) ∧ (∀ s, g s ≠ 0) ∧
      ∀ s, χ.completed s = finiteZeroPolynomial χ.completed hfinite.toFinset s * g s := by
  obtain ⟨g, hg, he, hgne⟩ := remove_finite_analytic_zeros χ.completed
    χ.completed_analytic χ.completed_order_ne_top hfinite.toFinset
  refine ⟨g, hg, ?_, he⟩
  intro s
  by_cases hs : s ∈ hfinite.toFinset
  · exact hgne s hs
  · intro hzero
    have hc : χ.completed s = 0 := by rw [he, hzero, mul_zero]
    exact hs (hfinite.mem_toFinset.mpr ((χ.completed_zero_iff s).mp hc))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCompletedLogGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Subquadratic logarithmic growth of the entire completed L-function -/

namespace Ostmann

open Complex

theorem character_completed_log_growth (χ : PrimitiveComplexCharacter) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (s : ℂ), ‖s‖ ≤ (N : ℝ) + 1 →
      Real.log ‖χ.completed s‖ ≤
        A * ((N : ℝ) + 3) * (1 + Real.log ((N : ℝ) + 3)) := by
  obtain ⟨C, hC, hbound⟩ := character_completed_disk_growth
  let B := 2 * ((χ.modulus : ℝ) + 1) * (C + 1)
  let A := |Real.log B| + Real.log (χ.modulus : ℝ) + 1
  have hq : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hqpos : 0 < (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hlogq : 0 ≤ Real.log (χ.modulus : ℝ) := Real.log_nonneg hq
  have hB : 0 < B := by dsimp [B]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro N s hs
  have hN : 1 ≤ (N : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hpow : 1 ≤ ((N : ℝ) + 2) ^ (N + 2) := one_le_pow₀ hN
  have hfac : ((N + 2).factorial : ℝ) ≤ ((N : ℝ) + 2) ^ (N + 2) := by
    exact_mod_cast Nat.factorial_le_pow (N + 2)
  have hcf : C + ((N + 2).factorial : ℝ) ≤ (C + 1) * ((N : ℝ) + 2) ^ (N + 2) := by
    nlinarith
  have hnorm : ‖χ.completed s‖ ≤ B * (χ.modulus : ℝ) ^ (N + 3) * ((N : ℝ) + 2) ^ (N + 3) := by
    apply (hbound χ N s hs).trans
    apply (mul_le_mul_of_nonneg_left hcf (by positivity)).trans_eq
    dsimp [B]
    rw [show N + 3 = (N + 2) + 1 by omega, pow_succ]
    ring
  have hlogN : 0 ≤ Real.log ((N : ℝ) + 3) := Real.log_nonneg (by linarith)
  by_cases hzero : χ.completed s = 0
  · rw [hzero, norm_zero, Real.log_zero]
    positivity
  · have hl := Real.log_le_log (norm_pos_iff.mpr hzero) hnorm
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hl
    have hn : Real.log ((N : ℝ) + 2) ≤ Real.log ((N : ℝ) + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have hb : Real.log B ≤ |Real.log B| * ((N : ℝ) + 3) := by
      apply (le_abs_self _).trans
      exact le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    have hpos : 0 ≤ (|Real.log B| + Real.log (χ.modulus : ℝ)) *
        ((N : ℝ) + 3) * Real.log ((N : ℝ) + 3) := by positivity
    dsimp [A]
    push_cast at hl
    nlinarith [mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (N : ℝ) + 3)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FiniteZeroQuotientGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing finitely many zeros preserves the required logarithmic growth -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem finite_zero_quotient_log_growth (f g : ℂ → ℂ) (S : Finset ℂ) (R : ℕ)
    (hS : ∀ z ∈ S, ‖z‖ ≤ (R : ℝ)) (A : ℝ) (_hA : 0 < A)
    (hg : ∀ z, AnalyticAt ℂ g z) (hne : ∀ z, g z ≠ 0)
    (he : ∀ z, f z = finiteZeroPolynomial f S z * g z)
    (hf : ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ (N : ℝ) + 1 →
      Real.log ‖f z‖ ≤ A * ((N : ℝ) + 3) * (1 + Real.log ((N : ℝ) + 3))) :
    ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ (N : ℝ) + 1 →
      Real.log ‖g z‖ ≤ A * ((N : ℝ) + R + 4) * (1 + Real.log ((N : ℝ) + R + 4)) := by
  intro N z hz
  let r : ℝ := (N : ℝ) + R + 2
  let B : ℝ := A * ((N : ℝ) + R + 4) * (1 + Real.log ((N : ℝ) + R + 4))
  have hr : 0 < r := by dsimp [r]; positivity
  have hbd : ∀ w ∈ sphere (0 : ℂ) r, ‖g w‖ ≤ Real.exp B := by
    intro w hw
    have hnw : ‖w‖ = r := by simpa using hw
    have hdist (u : ℂ) (hu : u ∈ S) : 1 ≤ ‖w - u‖ := by
      have hh := norm_le_norm_sub_add w u
      have hsu := hS u hu
      dsimp [r] at hnw
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have hp : 1 ≤ ‖finiteZeroPolynomial f S w‖ := by
      rw [finiteZeroPolynomial, norm_prod]
      apply Finset.one_le_prod
      intro u hu
      rw [norm_pow]
      exact one_le_pow₀ (hdist u hu)
    have hfn : 0 < ‖f w‖ := by
      rw [he w, norm_mul]
      exact mul_pos (by linarith) (norm_pos_iff.mpr (hne w))
    have hlog := hf (N + R + 1) w (by push_cast; dsimp [r] at hnw; linarith)
    have hlog' : Real.log ‖f w‖ ≤ B := by
      simpa only [Nat.cast_add, Nat.cast_one, B,
        show (N : ℝ) + R + 1 + 3 = (N : ℝ) + R + 4 by ring] using hlog
    calc
      _ ≤ ‖finiteZeroPolynomial f S w‖ * ‖g w‖ := le_mul_of_one_le_left (norm_nonneg _) hp
      _ = ‖f w‖ := by rw [he w, norm_mul]
      _ ≤ Real.exp B := by simpa only [Real.exp_log hfn] using Real.exp_le_exp.mpr hlog'
  have hn : ‖g z‖ ≤ Real.exp B := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) r) isBounded_ball
    · exact DiffContOnCl.mk_ball (fun w _ => (hg w).differentiableAt.differentiableWithinAt)
        (fun w _ => (hg w).continuousAt.continuousWithinAt)
    · rwa [frontier_ball 0 hr.ne']
    · rw [closure_ball 0 hr.ne', mem_closedBall, dist_zero_right]
      dsimp [r]
      linarith [Nat.cast_nonneg (α := ℝ) R]
  have hh := Real.log_le_log (norm_pos_iff.mpr (hne z)) hn
  simpa only [Real.log_exp] using hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LogDerivativeSecondBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A second-derivative estimate for the normalized analytic logarithm -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

theorem deriv_logDeriv_norm_le_of_disk (g : ℂ → ℂ) (R A : ℝ)
    (hR : 0 < R) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (hne : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A) :
    ‖deriv (logDeriv g) 0‖ ≤ 16 * A / R ^ 2 := by
  obtain ⟨F, hF0, hF, heF⟩ := exists_normalized_log_on_ball g R hR hg hne
  have hd : DifferentiableOn ℂ F (ball 0 R) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  have hreal : MapsTo F (ball 0 R) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (F z).re ≤ A
    rw [normalized_log_re g F z (hne 0 (mem_ball_self hR)) (heF z hz)]
    exact hlog z hz
  have hhalf : 0 < R / 2 := by positivity
  have hsmall (z : ℂ) (hz : z ∈ closedBall 0 (R / 2)) : z ∈ ball 0 R :=
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  have hdc : DiffContOnCl ℂ F (ball 0 (R / 2)) := by
    refine ⟨hd.mono (ball_subset_ball (by linarith)), ?_⟩
    rw [closure_ball 0 hhalf.ne']
    exact fun z hz => (hF z (hsmall z hz)).continuousAt.continuousWithinAt
  have hb : ∀ z ∈ sphere 0 (R / 2), ‖F z‖ ≤ 2 * A := by
    intro z hz
    have hn : ‖z‖ = R / 2 := by simpa using hz
    have hh := Complex.borelCaratheodory_zero hA hd hreal hR
      (hsmall z (sphere_subset_closedBall hz)) hF0
    rw [hn] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  have he : deriv F =ᶠ[𝓝 (0 : ℂ)] logDeriv g := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with z hz
    exact (hF z hz).deriv
  have he' : iteratedDeriv 2 F 0 = deriv (logDeriv g) 0 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using he.deriv_eq
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hhalf hdc hb
  rw [he'] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  field_simp
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LogDerivativeVanishing
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing second logarithmic derivative from subquadratic disk bounds -/

namespace Ostmann

open Complex Filter Metric
open scoped Topology

theorem deriv_logDeriv_eq_zero_of_disk_bounds (g : ℂ → ℂ)
    (hg : ∀ z, AnalyticAt ℂ g z) (hne : ∀ z, g z ≠ 0)
    (R A : ℕ → ℝ) (hR : ∀ n, 0 < R n) (hA : ∀ n, 0 < A n)
    (hlog : ∀ n z, z ∈ ball 0 (R n) →
      Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A n)
    (hsmall : Tendsto (fun n => A n / (R n) ^ 2) atTop (𝓝 0)) :
    deriv (logDeriv g) 0 = 0 := by
  have hb (n : ℕ) : ‖deriv (logDeriv g) 0‖ ≤ 16 * (A n / (R n) ^ 2) := by
    simpa only [mul_div_assoc] using deriv_logDeriv_norm_le_of_disk g (R n) (A n)
      (hR n) (hA n) (fun z _ => hg z) (fun z _ => hne z) (hlog n)
  have ht : Tendsto (fun n => 16 * (A n / (R n) ^ 2)) atTop (𝓝 0) := by
    simpa using hsmall.const_mul 16
  have hh : ‖deriv (logDeriv g) 0‖ ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hb)
  exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LogarithmicDiskRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic growth rate needed for the finite-zero contradiction -/

namespace Ostmann

open Filter
open scoped Topology

theorem logarithmic_disk_rate (A b D : ℝ) (hb : 1 ≤ b) :
    Tendsto (fun n : ℕ =>
      (A * ((n : ℝ) + b) * (1 + Real.log ((n : ℝ) + b)) + D) / ((n : ℝ) + 1) ^ 2)
      atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => (n : ℝ) + b) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hy : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun n : ℕ => (b - 1) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hy
  have hr : Tendsto (fun n : ℕ => ((n : ℝ) + b) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
    have hh := hc.const_add 1
    convert hh using 1
    · funext n
      field_simp
      ring
    · simp
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + b) / ((n : ℝ) + b)) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hx
  have hlog' : Tendsto (fun n : ℕ => (1 + Real.log ((n : ℝ) + b)) / ((n : ℝ) + b)) atTop (𝓝 0) := by
    simpa only [zero_add, add_div] using (tendsto_const_nhds.div_atTop hx).add hlog
  have hpow : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hy
  have hd : Tendsto (fun n : ℕ => D / ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpow
  have hh := ((hr.pow 2).const_mul A).mul hlog' |>.add hd
  simp only [one_pow, mul_one, mul_zero, zero_add] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  have hxn : (n : ℝ) + b ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hyn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hxn, hyn]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FiniteZeroLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constant logarithmic derivative after removing a finite zero set -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology BigOperators

/-- The precise elementary finite-order consequence needed for a hypothetical
finite set of completed-character zeros. -/
theorem finite_zero_quotient_logDeriv_constant (f g : ℂ → ℂ) (S : Finset ℂ)
    (hg : ∀ z, AnalyticAt ℂ g z) (hne : ∀ z, g z ≠ 0)
    (he : ∀ z, f z = finiteZeroPolynomial f S z * g z)
    (A : ℝ) (hA : 0 < A)
    (hf : ∀ (N : ℕ) (z : ℂ), ‖z‖ ≤ (N : ℝ) + 1 →
      Real.log ‖f z‖ ≤ A * ((N : ℝ) + 3) * (1 + Real.log ((N : ℝ) + 3))) :
    ∃ c : ℂ, ∀ z, logDeriv g z = c := by
  obtain ⟨R, hR⟩ := exists_nat_gt (∑ z ∈ S, ‖z‖)
  have hS : ∀ z ∈ S, ‖z‖ ≤ (R : ℝ) := by
    intro z hz
    exact (Finset.single_le_sum (fun w _ => norm_nonneg w) hz).trans hR.le
  have hgrowth := finite_zero_quotient_log_growth f g S R hS A hA hg hne he hf
  have hderiv : ∀ w, deriv (logDeriv g) w = 0 := by
    intro w
    obtain ⟨m, hm⟩ := exists_nat_gt ‖w‖
    let b : ℝ := (m : ℝ) + R + 4
    let D : ℝ := |Real.log ‖g w‖| + 1
    let B : ℕ → ℝ := fun n => A * ((n : ℝ) + b) * (1 + Real.log ((n : ℝ) + b)) + D
    have hb : 1 ≤ b := by dsimp [b]; linarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) R]
    have hB (n : ℕ) : 0 < B n := by
      have hl : 0 ≤ Real.log ((n : ℝ) + b) :=
        Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
      dsimp [B, D]
      positivity
    have hlocal : ∀ (n : ℕ) (z : ℂ), z ∈ ball (0 : ℂ) ((n : ℝ) + 1) →
        Real.log ‖g (z + w)‖ - Real.log ‖g (0 + w)‖ ≤ B n := by
      intro n z hz
      have hzn : ‖z‖ < (n : ℝ) + 1 := by simpa only [mem_ball, dist_zero_right] using hz
      have hzw : ‖z + w‖ ≤ ((n + m : ℕ) : ℝ) + 1 := by
        have hh := norm_add_le z w
        push_cast
        linarith
      have hh := hgrowth (n + m) (z + w) hzw
      simp only [Nat.cast_add] at hh
      dsimp [B, b, D]
      simp only [zero_add]
      simp only [add_assoc] at hh ⊢
      linarith [neg_le_abs (Real.log ‖g w‖)]
    have hh := deriv_logDeriv_eq_zero_of_disk_bounds (fun z => g (z + w))
      (fun z => (hg (z + w)).comp (f := fun u : ℂ => u + w) (x := z) (by fun_prop))
      (fun z => hne (z + w)) (fun n => (n : ℝ) + 1) B (fun _ => by positivity) hB hlocal
      (logarithmic_disk_rate A b D hb)
    have hshift : logDeriv (fun z => g (z + w)) = fun z => logDeriv g (z + w) := by
      funext z
      have hc := logDeriv_comp (f := g) (g := fun u : ℂ => u + w) (x := z)
        (hg (z + w)).differentiableAt (differentiableAt_id.add_const w)
      simpa [Function.comp_def] using hc
    rw [hshift, deriv_comp_add_const, zero_add] at hh
    exact hh
  have hd : Differentiable ℂ (logDeriv g) := fun z =>
    ((hg z).deriv.div (hg z) (hne z)).differentiableAt
  refine ⟨logDeriv g 0, fun z => ?_⟩
  exact isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    hd.differentiableOn (fun w _ => hderiv w) (mem_univ z) (mem_univ 0)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FiniteZeroPolynomialLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic derivative of the actual finite zero polynomial -/

namespace Ostmann

open Complex
open scoped BigOperators

theorem finiteZeroPolynomial_logDeriv (f : ℂ → ℂ) (S : Finset ℂ)
    (s : ℂ) (hs : s ∉ S) :
    logDeriv (finiteZeroPolynomial f S) s =
      ∑ z ∈ S, (analyticOrderNatAt f z : ℂ) / (s - z) := by
  change logDeriv (fun w => ∏ z ∈ S, (w - z) ^ analyticOrderNatAt f z) s = _
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro z hz
    have hp := logDeriv_fun_pow (f := fun w : ℂ => w - z) (x := s)
      (differentiableAt_id.sub_const z) (analyticOrderNatAt f z)
    rw [hp]
    simp [logDeriv_apply, div_eq_mul_inv]
  · intro z hz
    exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => hs (he ▸ hz)))
  · intro z _
    exact (differentiableAt_id.sub_const z).pow _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterCompletedFiniteBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite nontrivial zero set would bound the completed logarithmic derivative -/

namespace Ostmann

open Complex
open scoped BigOperators Classical

theorem completed_logDeriv_bounded_of_finite_zeros (χ : PrimitiveComplexCharacter)
    (hfinite : (complexCharacterZeros χ).Finite) :
    ∃ R C : ℝ, 0 < R ∧ 0 < C ∧ ∀ s : ℂ, R ≤ s.re →
      ‖logDeriv χ.completed s‖ ≤ C := by
  obtain ⟨g, hg, hgne, he⟩ := character_completed_finite_factors χ hfinite
  obtain ⟨A, hA, hgrowth⟩ := character_completed_log_growth χ
  let S := hfinite.toFinset
  obtain ⟨c, hc⟩ := finite_zero_quotient_logDeriv_constant χ.completed g S hg hgne he A hA hgrowth
  obtain ⟨R, hR⟩ := exists_nat_gt (∑ z ∈ S, ‖z‖)
  let D : ℝ := ∑ z ∈ S, (analyticOrderNatAt χ.completed z : ℝ)
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  refine ⟨(R : ℝ) + 1, ‖c‖ + D + 1, by positivity, by positivity, ?_⟩
  intro s hs
  have hdist (z : ℂ) (hz : z ∈ S) : 1 ≤ ‖s - z‖ := by
    have hzR : ‖z‖ ≤ (R : ℝ) :=
      (Finset.single_le_sum (fun w _ => norm_nonneg w) hz).trans hR.le
    have ha := abs_re_le_norm (s - z)
    have hb := (le_abs_self z.re).trans (abs_re_le_norm z)
    have hh := le_abs_self ((s - z).re)
    simp only [sub_re] at ha hh
    linarith
  have hsnot : s ∉ S := by
    intro hz
    have hh := hdist s hz
    simp only [sub_self, norm_zero] at hh
    linarith
  have hsum : ‖∑ z ∈ S, (analyticOrderNatAt χ.completed z : ℂ) / (s - z)‖ ≤ D := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro z hz
    rw [norm_div, Complex.norm_natCast]
    exact div_le_self (Nat.cast_nonneg _) (hdist z hz)
  have hfun : χ.completed = fun z => finiteZeroPolynomial χ.completed S z * g z := funext he
  have hsplit : logDeriv χ.completed s = logDeriv (finiteZeroPolynomial χ.completed S) s + logDeriv g s := by
    conv_lhs => rw [hfun]
    exact logDeriv_mul s (finiteZeroPolynomial_ne_zero χ.completed S s hsnot) (hgne s)
      (finiteZeroPolynomial_analytic χ.completed S s).differentiableAt (hg s).differentiableAt
  rw [hsplit, hc s, finiteZeroPolynomial_logDeriv χ.completed S s hsnot]
  exact (norm_add_le _ _).trans (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterEnumerationCount
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Connecting zero enumerations to actual analytic multiplicities

This is a representation condition: an enumeration may list a zero no more
times than its analytic multiplicity. The numerical zero bound itself is
proved in `CharacterFullZeroCount`, not assumed here.
-/

namespace Ostmann

open scoped Classical BigOperators

def ComplexZeroEnumeration.RespectsMultiplicity {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) : Prop :=
  ∀ (S : Finset ℕ) (z : ℂ),
    (S.filter (fun i => Z.zeros i = z)).card ≤ analyticOrderNatAt χ.L z

theorem ComplexZeroEnumeration.count_zero_eq_card {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (T : ℝ) : Z.count 0 T = (Z.heightIndices T).card := by
  unfold ComplexZeroEnumeration.count
  congr 1
  apply Finset.filter_true_of_mem
  intro i _
  exact (Z.in_strip i).1.le

theorem ComplexZeroEnumeration.count_bound_of_multiplicity {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (hZ : Z.RespectsMultiplicity) (T : ℝ) (hT : 0 ≤ T) :
    (Z.count 0 T : ℝ) ≤ (32 / Real.log (14 / 13)) * (T + 1) *
      Real.log ((χ.modulus : ℝ) * (T + 2)) := by
  let S := Z.heightIndices T
  let F := S.image Z.zeros
  have hcard : S.card = ∑ z ∈ F, (S.filter fun i => Z.zeros i = z).card :=
    Finset.card_eq_sum_card_image Z.zeros S
  have hbound : (S.card : ℝ) ≤ ∑ z ∈ F, (characterZeroOrder χ z : ℝ) := by
    rw [hcard, Nat.cast_sum]
    apply Finset.sum_le_sum
    intro z hz
    have hh := hZ S z
    rw [characterZeroOrder_eq_nat]
    exact_mod_cast hh
  rw [Z.count_zero_eq_card]
  apply hbound.trans
  apply χ.full_zero_sum_rate T hT F
  intro z hz
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨(Z.in_strip i).1, (Z.in_strip i).2, (Z.mem_heightIndices T i).mp hi⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroCopies
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual zero set with multiplicity labels

Each copy is a genuine zero together with an integer smaller than its analytic
order. Any bijective numbering of these copies automatically has the correct
multiplicity bound and finite bounded-height ranges.
-/

namespace Ostmann

open Set
open scoped Classical

abbrev CharacterZeroCopy (χ : PrimitiveComplexCharacter) :=
  {p : ℂ × ℕ // p.1 ∈ complexCharacterZeros χ ∧ p.2 < analyticOrderNatAt χ.L p.1}

theorem characterZeroCopy_finite_height (χ : PrimitiveComplexCharacter) (T : ℝ) :
    {c : CharacterZeroCopy χ | |c.val.1.im| ≤ T}.Finite := by
  let V : Set (ℂ × ℕ) := ⋃ z ∈ {z : ℂ | z ∈ complexCharacterZeros χ ∧ |z.im| ≤ T},
    ({z} ×ˢ {n : ℕ | n < analyticOrderNatAt χ.L z})
  have hV : V.Finite := (χ.strip_zeros_finite T).biUnion
    (fun z _ => (finite_singleton z).prod (finite_lt_nat _))
  apply (hV.preimage (fun _ _ _ _ h => Subtype.ext h)).subset
  intro c hc
  exact Set.mem_iUnion.mpr ⟨c.val.1, Set.mem_iUnion.mpr
    ⟨⟨c.property.1, hc⟩, ⟨rfl, c.property.2⟩⟩⟩

noncomputable def characterZeroEnumeration (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) : ComplexZeroEnumeration χ where
  zeros i := (e i).val.1
  in_strip i := ⟨(e i).property.1.1, (e i).property.1.2.1⟩
  actual_zero i := (e i).property.1.2.2
  finite_height T := (characterZeroCopy_finite_height χ T).preimage
    (fun _ _ _ _ h => e.injective h)

theorem characterZeroEnumeration_respectsMultiplicity (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) : (characterZeroEnumeration χ e).RespectsMultiplicity := by
  intro S z
  change (S.filter (fun i => (e i).val.1 = z)).card ≤ analyticOrderNatAt χ.L z
  rw [← Finset.card_range (analyticOrderNatAt χ.L z)]
  apply Finset.card_le_card_of_injOn (fun i => (e i).val.2)
  · intro i hi
    have hzi := (Finset.mem_filter.mp hi).2
    have hbound := (e i).property.2
    rw [hzi] at hbound
    exact Finset.mem_range.mpr hbound
  · intro i hi j hj hindex
    apply e.injective
    apply Subtype.ext
    exact Prod.ext ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) hindex

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_SmoothTruncatedContour
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact truncated smooth explicit formula

The contour encloses all actual critical zeros of bounded height and the
origin. Its zero sum is a finite sum with analytic multiplicities.
-/

namespace Ostmann

open Complex Set
open scoped BigOperators Classical Interval

noncomputable def criticalZerosUpTo (χ : PrimitiveComplexCharacter) (T : ℝ) : Finset ℂ :=
  (χ.strip_zeros_finite T).toFinset

@[simp] theorem mem_criticalZerosUpTo {χ : PrimitiveComplexCharacter} {T : ℝ} {z : ℂ} :
    z ∈ criticalZerosUpTo χ T ↔ z ∈ complexCharacterZeros χ ∧ |z.im| ≤ T := by
  exact Set.Finite.mem_toFinset _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroPartialSums
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Identifying the finite contour zero sum with the true zero enumeration -/

namespace Ostmann

open Filter
open scoped Topology BigOperators Classical

theorem characterZeroEnumeration_fiber_card (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) (T : ℝ) (z : ℂ)
    (hz : z ∈ criticalZerosUpTo χ T) :
    (((characterZeroEnumeration χ e).heightIndices T).filter
      (fun i => (characterZeroEnumeration χ e).zeros i = z)).card = analyticOrderNatAt χ.L z := by
  have hz' := mem_criticalZerosUpTo.mp hz
  let Z := characterZeroEnumeration χ e
  calc
    _ = (Finset.range (analyticOrderNatAt χ.L z)).card := by
      apply Finset.card_bij (fun i _ => (e i).val.2)
      · intro i hi
        have hzi : (e i).val.1 = z := (Finset.mem_filter.mp hi).2
        exact Finset.mem_range.mpr (hzi ▸ (e i).property.2)
      · intro i hi j hj he
        apply e.injective
        apply Subtype.ext
        exact Prod.ext ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) he
      · intro k hk
        let c : CharacterZeroCopy χ := ⟨(z, k), hz'.1, Finset.mem_range.mp hk⟩
        refine ⟨e.symm c, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
        · change e.symm c ∈ Z.heightIndices T
          rw [Z.mem_heightIndices]
          change |(e (e.symm c)).val.1.im| ≤ T
          simpa [c] using hz'.2
        · change (e (e.symm c)).val.1 = z
          simp [c]
        · simp [c]
    _ = _ := Finset.card_range _

theorem characterZeroEnumeration_height_sum (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) (T : ℝ) (W : ℂ → ℂ) :
    (∑ z ∈ criticalZerosUpTo χ T, (analyticOrderNatAt χ.L z : ℂ) * W z) =
      ∑ i ∈ (characterZeroEnumeration χ e).heightIndices T,
        W ((characterZeroEnumeration χ e).zeros i) := by
  let Z := characterZeroEnumeration χ e
  have hm : ∀ i ∈ Z.heightIndices T, Z.zeros i ∈ criticalZerosUpTo χ T := by
    intro i hi
    exact mem_criticalZerosUpTo.mpr
      ⟨⟨(Z.in_strip i).1, (Z.in_strip i).2, Z.actual_zero i⟩, (Z.mem_heightIndices T i).mp hi⟩
  rw [← Finset.sum_fiberwise_of_maps_to hm (fun i => W (Z.zeros i))]
  apply Finset.sum_congr rfl
  intro z hz
  calc
    (analyticOrderNatAt χ.L z : ℂ) * W z =
        ∑ i ∈ (Z.heightIndices T).filter (fun i => Z.zeros i = z), W z := by
      simp [Z, characterZeroEnumeration_fiber_card χ e T z hz, nsmul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FiniteZeroQuotientDisk
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaled disk bounds for finite zero removal -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem finiteZeroPolynomial_norm_le (f : ℂ → ℂ) (S : Finset ℂ)
    (z : ℂ) (r : ℝ) (_hr : 0 ≤ r) (hS : ∀ w ∈ S, ‖z - w‖ ≤ r) :
    ‖finiteZeroPolynomial f S z‖ ≤ r ^ (∑ w ∈ S, analyticOrderNatAt f w) := by
  simp only [finiteZeroPolynomial, norm_prod, norm_pow]
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ => by positivity)
    (fun w hw => pow_le_pow_left₀ (norm_nonneg _) (hS w hw) _)

theorem finiteZeroPolynomial_norm_ge (f : ℂ → ℂ) (S : Finset ℂ)
    (z : ℂ) (r : ℝ) (hr : 0 ≤ r) (hS : ∀ w ∈ S, r ≤ ‖z - w‖) :
    r ^ (∑ w ∈ S, analyticOrderNatAt f w) ≤ ‖finiteZeroPolynomial f S z‖ := by
  simp only [finiteZeroPolynomial, norm_prod, norm_pow]
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ => pow_nonneg hr _)
    (fun w hw => pow_le_pow_left₀ hr (hS w hw) _)

/-- The annulus between radii 2R and 3R separates the removed zeros from
 the circle on which the original function is estimated. -/
theorem finite_zero_quotient_disk_bound (f g : ℂ → ℂ) (S : Finset ℂ)
    (R M : ℝ) (hR : 0 < R) (_hM : 0 ≤ M)
    (hS : ∀ w ∈ S, ‖w‖ ≤ 2 * R)
    (hg : ∀ s, AnalyticAt ℂ g s)
    (he : ∀ s, f s = finiteZeroPolynomial f S s * g s)
    (hf : ∀ z ∈ sphere (0 : ℂ) (3 * R), ‖f z‖ ≤ M) :
    ∀ z ∈ closedBall (0 : ℂ) (3 * R),
      ‖g z‖ ≤ M / R ^ (∑ w ∈ S, analyticOrderNatAt f w) := by
  let N := ∑ w ∈ S, analyticOrderNatAt f w
  have hb : ∀ z ∈ sphere (0 : ℂ) (3 * R), ‖g z‖ ≤ M / R ^ N := by
    intro z hz
    have hnorm : ‖z‖ = 3 * R := by simpa using hz
    have hp : R ^ N ≤ ‖finiteZeroPolynomial f S z‖ := by
      apply finiteZeroPolynomial_norm_ge f S z R hR.le
      intro w hw
      have ht := norm_add_le (z - w) w
      rw [sub_add_cancel] at ht
      linarith [hS w hw]
    have hfm := hf z hz
    rw [he, norm_mul] at hfm
    apply (le_div_iff₀ (pow_pos hR N)).mpr
    simpa only [mul_comm] using (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans hfm
  intro z hz
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) (3 * R))
    isBounded_ball (f := g)
  · exact DiffContOnCl.mk_ball (fun w _ => (hg w).differentiableAt.differentiableWithinAt)
      (fun w _ => (hg w).continuousAt.continuousWithinAt)
  · rw [frontier_ball (0 : ℂ) (by positivity : 3 * R ≠ 0)]
    exact hb
  · rwa [closure_ball (0 : ℂ) (by positivity : 3 * R ≠ 0)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FiniteZeroQuotientNormalized
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Normalized logarithmic bounds after removing all zeros in a disk -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem finite_zero_quotient_normalized_log (f g : ℂ → ℂ) (S : Finset ℂ)
    (R M : ℝ) (hR : 0 < R) (hM : 0 < M) (hf0 : f 0 ≠ 0)
    (hS : ∀ w ∈ S, ‖w‖ ≤ 2 * R)
    (hg : ∀ s, AnalyticAt ℂ g s)
    (he : ∀ s, f s = finiteZeroPolynomial f S s * g s)
    (hf : ∀ z ∈ sphere (0 : ℂ) (3 * R), ‖f z‖ ≤ M)
    (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (2 * R)) (hgz : g z ≠ 0) :
    Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ Real.log M +
      (∑ w ∈ S, (analyticOrderNatAt f w : ℝ)) * Real.log 2 - Real.log ‖f 0‖ := by
  let N := ∑ w ∈ S, analyticOrderNatAt f w
  have hgne : g 0 ≠ 0 := by
    intro h
    exact hf0 (by rw [he, h, mul_zero])
  have hgn : 0 < ‖g 0‖ := norm_pos_iff.mpr hgne
  have hfn : 0 < ‖f 0‖ := norm_pos_iff.mpr hf0
  have hp : ‖finiteZeroPolynomial f S 0‖ ≤ (2 * R) ^ N := by
    apply finiteZeroPolynomial_norm_le f S 0 (2 * R) (by positivity)
    intro w hw
    simpa only [zero_sub, norm_neg] using hS w hw
  have hb : ‖f 0‖ ≤ (2 * R) ^ N * ‖g 0‖ := by
    rw [he 0, norm_mul]
    exact mul_le_mul_of_nonneg_right hp (norm_nonneg _)
  have hu := finite_zero_quotient_disk_bound f g S R M hR hM.le hS hg he hf z
    (closedBall_subset_closedBall (by linarith) hz)
  have hm : ‖g z‖ * ‖f 0‖ ≤ M * 2 ^ N * ‖g 0‖ := by
    calc
      _ ≤ (M / R ^ N) * ((2 * R) ^ N * ‖g 0‖) :=
        mul_le_mul hu hb hfn.le (div_nonneg hM.le (pow_nonneg hR.le _))
      _ = _ := by
        rw [mul_pow]
        field_simp [hR.ne']
  have hratio : ‖g z‖ / ‖g 0‖ ≤ (M * 2 ^ N) / ‖f 0‖ :=
    (div_le_div_iff₀ hgn hfn).mpr hm
  have hzn : 0 < ‖g z‖ := norm_pos_iff.mpr hgz
  rw [← Real.log_div hzn.ne' hgn.ne']
  apply (Real.log_le_log (div_pos hzn hgn) hratio).trans_eq
  rw [Real.log_div (by positivity) hfn.ne', Real.log_mul hM.ne' (by positivity), Real.log_pow]
  simp only [N, Nat.cast_sum]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CompletedDiskZeros
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing precisely the completed L-function zeros in an expanding disk -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators Classical

noncomputable def completedDiskZeros (χ : PrimitiveComplexCharacter) (R : ℝ) : Finset ℂ :=
  (criticalZerosUpTo χ (2 * R)).filter (fun z => ‖z‖ ≤ 2 * R)

@[simp] theorem mem_completedDiskZeros (χ : PrimitiveComplexCharacter) (R : ℝ) (z : ℂ) :
    z ∈ completedDiskZeros χ R ↔ ‖z‖ ≤ 2 * R ∧ χ.completed z = 0 := by
  rw [completedDiskZeros, Finset.mem_filter, mem_criticalZerosUpTo]
  constructor
  · rintro ⟨⟨hz, _⟩, hn⟩
    exact ⟨hn, (χ.completed_zero_iff z).mpr hz⟩
  · rintro ⟨hn, hz⟩
    exact ⟨⟨(χ.completed_zero_iff z).mp hz, (abs_im_le_norm z).trans hn⟩, hn⟩

theorem completed_disk_quotient_exists (χ : PrimitiveComplexCharacter) (R : ℝ) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧
      (∀ z, χ.completed z = finiteZeroPolynomial χ.completed (completedDiskZeros χ R) z * g z) ∧
      (∀ z ∈ closedBall (0 : ℂ) (2 * R), g z ≠ 0) := by
  obtain ⟨g, hg, he, hne⟩ := remove_finite_analytic_zeros χ.completed χ.completed_analytic
    χ.completed_order_ne_top (completedDiskZeros χ R)
  refine ⟨g, hg, he, ?_⟩
  intro z hz
  by_cases hm : z ∈ completedDiskZeros χ R
  · exact hne z hm
  · intro hzero
    apply hm
    refine (mem_completedDiskZeros χ R z).mpr ⟨?_, ?_⟩
    · simpa using hz
    · rw [he, hzero, mul_zero]

theorem completedDiskZeros_mass_bound (χ : PrimitiveComplexCharacter) (R : ℝ) (hR : 0 ≤ R) :
    (∑ z ∈ completedDiskZeros χ R, (analyticOrderNatAt χ.completed z : ℝ)) ≤
      (32 / Real.log (14 / 13)) * (2 * R + 1) * Real.log ((χ.modulus : ℝ) * (2 * R + 2)) := by
  have he : ∀ z ∈ completedDiskZeros χ R,
      (analyticOrderNatAt χ.completed z : ℝ) = (characterZeroOrder χ z : ℝ) := by
    intro z hz
    have hr := ((χ.completed_zero_iff z).mp ((mem_completedDiskZeros χ R z).mp hz).2).1
    rw [characterZeroOrder_eq_nat]
    congr 1
    exact (congrArg ENat.toNat (χ.L_order_eq_completed z hr)).symm
  rw [Finset.sum_congr rfl he]
  apply χ.full_zero_sum_rate (2 * R) (by positivity)
  intro z hz
  obtain ⟨hn, hz0⟩ := (mem_completedDiskZeros χ R z).mp hz
  have hz' := (χ.completed_zero_iff z).mp hz0
  exact ⟨hz'.1, hz'.2.1, (abs_im_le_norm z).trans hn⟩

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CompletedFiniteLogDerivative
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic derivatives with precisely the disk zeros removed -/

namespace Ostmann

open Complex
open scoped BigOperators

noncomputable def completedZeroPartialFraction (χ : PrimitiveComplexCharacter) (R : ℝ) (s : ℂ) : ℂ :=
  ∑ z ∈ completedDiskZeros χ R, (analyticOrderNatAt χ.completed z : ℂ) / (s - z)

theorem completed_logDeriv_remove_finite (χ : PrimitiveComplexCharacter) (R : ℝ)
    (g : ℂ → ℂ) (hg : ∀ z, AnalyticAt ℂ g z)
    (he : ∀ z, χ.completed z = finiteZeroPolynomial χ.completed (completedDiskZeros χ R) z * g z)
    (s : ℂ) (hs : χ.completed s ≠ 0) :
    logDeriv χ.completed s - completedZeroPartialFraction χ R s = logDeriv g s := by
  have hsS : s ∉ completedDiskZeros χ R := fun h => hs ((mem_completedDiskZeros χ R s).mp h).2
  have hgn : g s ≠ 0 := by
    intro h
    exact hs (by rw [he, h, mul_zero])
  have hfun : χ.completed = fun z => finiteZeroPolynomial χ.completed (completedDiskZeros χ R) z * g z := funext he
  have hsplit : logDeriv χ.completed s =
      logDeriv (finiteZeroPolynomial χ.completed (completedDiskZeros χ R)) s + logDeriv g s := by
    conv_lhs => rw [hfun]
    exact logDeriv_mul s (finiteZeroPolynomial_ne_zero _ _ s hsS) hgn
      (finiteZeroPolynomial_analytic _ _ s).differentiableAt (hg s).differentiableAt
  rw [hsplit, finiteZeroPolynomial_logDeriv _ _ s hsS]
  simp [completedZeroPartialFraction]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterDiskIndices
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reindexing finite disk divisor sums by the faithful zero copies -/

namespace Ostmann

open Filter
open scoped Topology BigOperators Classical

noncomputable def ComplexZeroEnumeration.diskIndices {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (R : ℝ) : Finset ℕ :=
  (Z.heightIndices (2 * R)).filter (fun i => ‖Z.zeros i‖ ≤ 2 * R)

@[simp] theorem ComplexZeroEnumeration.mem_diskIndices {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) (R : ℝ) (i : ℕ) :
    i ∈ Z.diskIndices R ↔ ‖Z.zeros i‖ ≤ 2 * R := by
  simp only [ComplexZeroEnumeration.diskIndices, Finset.mem_filter, Z.mem_heightIndices]
  exact and_iff_right_of_imp (fun h => (Complex.abs_im_le_norm _).trans h)

theorem ComplexZeroEnumeration.tendsto_diskIndices {χ : PrimitiveComplexCharacter}
    (Z : ComplexZeroEnumeration χ) : Tendsto Z.diskIndices atTop atTop := by
  apply tendsto_atTop.2
  intro S
  have hh : ∀ᶠ R : ℝ in atTop, ∀ i ∈ S, ‖Z.zeros i‖ ≤ R :=
    (Filter.eventually_all_finset S).mpr (fun i _ => eventually_ge_atTop _)
  filter_upwards [hh, eventually_ge_atTop 0] with R hR hR0
  intro i hi
  exact (Z.mem_diskIndices R i).mpr (by linarith [hR i hi])

theorem characterZeroEnumeration_disk_sum (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) (R : ℝ) (W : ℂ → ℂ) :
    (∑ z ∈ completedDiskZeros χ R, (analyticOrderNatAt χ.completed z : ℂ) * W z) =
      ∑ i ∈ (characterZeroEnumeration χ e).diskIndices R,
        W ((characterZeroEnumeration χ e).zeros i) := by
  let Z := characterZeroEnumeration χ e
  have ho (z : ℂ) (hz : z ∈ criticalZerosUpTo χ (2 * R)) :
      analyticOrderNatAt χ.completed z = analyticOrderNatAt χ.L z :=
    (congrArg ENat.toNat (χ.L_order_eq_completed z (mem_criticalZerosUpTo.mp hz).1.1)).symm
  unfold completedDiskZeros ComplexZeroEnumeration.diskIndices
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    _ = ∑ z ∈ criticalZerosUpTo χ (2 * R),
        (analyticOrderNatAt χ.L z : ℂ) * (if ‖z‖ ≤ 2 * R then W z else 0) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [ho z hz]
      split_ifs <;> simp
    _ = _ := characterZeroEnumeration_height_sum χ e (2 * R) _

theorem completedZeroPartialFraction_index_sum (χ : PrimitiveComplexCharacter)
    (e : ℕ ≃ CharacterZeroCopy χ) (R : ℝ) (s : ℂ) :
    completedZeroPartialFraction χ R s =
      ∑ i ∈ (characterZeroEnumeration χ e).diskIndices R,
        (s - (characterZeroEnumeration χ e).zeros i)⁻¹ := by
  simpa only [completedZeroPartialFraction, div_eq_mul_inv] using
    characterZeroEnumeration_disk_sum χ e R (fun z => (s - z)⁻¹)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZerosInfinite
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Infinitely many actual nontrivial zeros for every primitive character -/

namespace Ostmann

open Complex Filter Set
open scoped Topology

/-- A finite zero set would force bounded logarithmic derivative, contradicting
its Gamma-factor growth along the positive real axis. -/
theorem PrimitiveComplexCharacter.zeros_infinite (χ : PrimitiveComplexCharacter) :
    (complexCharacterZeros χ).Infinite := by
  intro hfinite
  obtain ⟨R, C, hR, hC, hbound⟩ := completed_logDeriv_bounded_of_finite_zeros χ hfinite
  have hg := (completed_logDeriv_sample_re_tendsto χ).eventually_ge_atTop (C + 1)
  have hr := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (max R 2)
  obtain ⟨n, hn, hnR⟩ := (hg.and hr).exists
  have hsample := characterGammaSample_re_lower χ n
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hnr : R ≤ (n : ℝ) := (le_max_left R 2).trans hnR
  have hb := hbound (characterGammaSample χ n) (by linarith)
  have hre := (le_abs_self ((logDeriv χ.completed (characterGammaSample χ n)).re)).trans
    (abs_re_le_norm (logDeriv χ.completed (characterGammaSample χ n)))
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_CharacterFaithfulEnumeration
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A faithful enumeration of all actual zeros with their multiplicities -/

namespace Ostmann

open Set
open scoped Classical

theorem characterZeroCopy_countable (χ : PrimitiveComplexCharacter) :
    Countable (CharacterZeroCopy χ) := by
  let : Countable (complexCharacterZeros χ) := χ.zeros_countable.to_subtype
  let f : CharacterZeroCopy χ → (complexCharacterZeros χ) × ℕ :=
    fun c => (⟨c.val.1, c.property.1⟩, c.val.2)
  apply Function.Injective.countable (f := f)
  intro x y h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z : (complexCharacterZeros χ) × ℕ => z.2) h)

theorem characterZeroCopy_infinite (χ : PrimitiveComplexCharacter) :
    Infinite (CharacterZeroCopy χ) := by
  let : Infinite (complexCharacterZeros χ) := χ.zeros_infinite.to_subtype
  let f : (complexCharacterZeros χ) → CharacterZeroCopy χ := fun z =>
    ⟨(z.val, 0), z.property, by
      have hh := (characterZeroOrder_pos_iff χ z.val).mpr z.property.2.2
      rwa [characterZeroOrder_eq_nat, Int.natCast_pos] at hh⟩
  apply Infinite.of_injective f
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : CharacterZeroCopy χ => z.val.1) h

/-- No dummy zeros, repetitions, or omitted multiplicity labels occur. -/
noncomputable def faithfulCharacterZeroEquiv (χ : PrimitiveComplexCharacter) :
    ℕ ≃ CharacterZeroCopy χ := by
  letI := characterZeroCopy_countable χ
  letI := characterZeroCopy_infinite χ
  exact Classical.choice (inferInstance : Nonempty (ℕ ≃ CharacterZeroCopy χ))

noncomputable def actualCharacterZeros (χ : PrimitiveComplexCharacter) :
    ComplexZeroEnumeration χ := characterZeroEnumeration χ (faithfulCharacterZeroEquiv χ)

theorem actualCharacterZeros_respectsMultiplicity (χ : PrimitiveComplexCharacter) :
    (actualCharacterZeros χ).RespectsMultiplicity :=
  characterZeroEnumeration_respectsMultiplicity χ (faithfulCharacterZeroEquiv χ)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealCharacterComplexification
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real characters inside the actual complex-character zero development -/

namespace Ostmann

open scoped Classical

theorem PrimitiveRealCharacter.complex_factorsThrough_iff
    (χ : PrimitiveRealCharacter) (d : ℕ) :
    χ.complexCharacter.FactorsThrough d ↔ χ.character.FactorsThrough d := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  by_cases hd : d ∣ χ.modulus
  · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
      DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
    constructor <;> intro h x hx
    · have hh := h hx
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at hh ⊢
      simpa [PrimitiveRealCharacter.complexCharacter] using hh
    · have hh := h hx
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at hh ⊢
      simp [PrimitiveRealCharacter.complexCharacter, hh]
  · constructor <;> intro h <;> exact (hd h.dvd).elim

theorem PrimitiveRealCharacter.complex_conductor (χ : PrimitiveRealCharacter) :
    χ.complexCharacter.conductor = χ.character.conductor := by
  unfold DirichletCharacter.conductor
  congr 1
  ext d
  exact χ.complex_factorsThrough_iff d

/-- The coercion to complex values preserves the actual conductor and character. -/
noncomputable def PrimitiveRealCharacter.asComplex (χ : PrimitiveRealCharacter) :
    PrimitiveComplexCharacter where
  modulus := χ.modulus
  positive := χ.positive
  character := χ.complexCharacter
  primitive := by
    rw [DirichletCharacter.isPrimitive_def, χ.complex_conductor]
    exact χ.primitive
  nontrivial := (MulChar.ringHomComp_ne_one_iff Complex.ofReal_injective).mpr χ.nontrivial

@[simp] theorem PrimitiveRealCharacter.asComplex_L (χ : PrimitiveRealCharacter) :
    χ.asComplex.L = χ.L := rfl

noncomputable def realCharacterActualZeros (χ : PrimitiveRealCharacter) :
    ComplexZeroEnumeration χ.asComplex := actualCharacterZeros χ.asComplex

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealCharacterReflection
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual functional equation for a real primitive character -/

namespace Ostmann

open Complex
open scoped Classical

theorem PrimitiveRealCharacter.complex_inv_eq (χ : PrimitiveRealCharacter) :
    χ.complexCharacter⁻¹ = χ.complexCharacter := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  rw [← MulChar.star_eq_inv]
  ext x
  simp [PrimitiveRealCharacter.complexCharacter]

theorem PrimitiveRealCharacter.inverse_completed_eq (χ : PrimitiveRealCharacter) :
    χ.asComplex.inverse.completed = χ.asComplex.completed := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  funext s
  change DirichletCharacter.completedLFunction (χ.complexCharacter⁻¹) s =
    DirichletCharacter.completedLFunction χ.complexCharacter s
  rw [χ.complex_inv_eq]

theorem PrimitiveRealCharacter.inverse_L_eq (χ : PrimitiveRealCharacter) :
    χ.asComplex.inverse.L = χ.asComplex.L := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  funext s
  change DirichletCharacter.LFunction (χ.complexCharacter⁻¹) s =
    DirichletCharacter.LFunction χ.complexCharacter s
  rw [χ.complex_inv_eq]

theorem PrimitiveRealCharacter.completed_logDeriv_reflection
    (χ : PrimitiveRealCharacter) (s : ℂ) (hs : 1 ≤ s.re) :
    logDeriv χ.asComplex.completed (1 - s) =
      -Complex.log (χ.modulus : ℂ) - logDeriv χ.asComplex.completed s := by
  have hh := χ.asComplex.completed_logDeriv_reflection s hs
  rw [χ.inverse_completed_eq] at hh
  exact hh

theorem PrimitiveRealCharacter.zero_reflection_order (χ : PrimitiveRealCharacter)
    (z : ℂ) (hz : 0 < z.re) (hz1 : z.re < 1) :
    analyticOrderNatAt χ.L (1 - z) = analyticOrderNatAt χ.L z := by
  have hh := χ.asComplex.L_order_reflection z hz hz1
  rw [χ.inverse_L_eq] at hh
  exact congrArg ENat.toNat hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Characters_PrimitiveCharacterLifts
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Distinct primitive characters remain distinct at a common level -/

namespace Ostmann

theorem PrimitiveComplexCharacter.eq_of_changeLevel_eq (χ ψ : PrimitiveComplexCharacter)
    {N : ℕ} [NeZero N] (hχ : χ.modulus ∣ N) (hψ : ψ.modulus ∣ N)
    (he : DirichletCharacter.changeLevel hχ χ.character =
      DirichletCharacter.changeLevel hψ ψ.character) : χ = ψ := by
  have hm : χ.modulus = ψ.modulus := by
    have hh := congrArg DirichletCharacter.conductor he
    rw [DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_changeLevel] at hh
    exact χ.primitive.symm.trans (hh.trans ψ.primitive)
  cases χ with
  | mk q hq χ hprim hn =>
    cases ψ with
    | mk r hr ψ hprim' hn' =>
      dsimp only at hm hχ hψ he
      subst r
      have hc : χ = ψ := DirichletCharacter.changeLevel_injective hχ he
      subst ψ
      rfl

theorem PrimitiveRealCharacter.asComplex_injective :
    Function.Injective PrimitiveRealCharacter.asComplex := by
  intro χ ψ he
  have hm : χ.modulus = ψ.modulus := congrArg PrimitiveComplexCharacter.modulus he
  cases χ with
  | mk q hq χ hprim hn =>
    cases ψ with
    | mk r hr ψ hprim' hn' =>
      dsimp only at hm
      subst r
      have hc : χ = ψ := by
        let : NeZero q := ⟨hq.ne'⟩
        have hh := congrArg (fun η : PrimitiveComplexCharacter => fun n : ℕ => η.character n) he
        apply MulChar.ext
        intro x
        apply Complex.ofReal_injective
        have hv := congrFun hh (x : ZMod q).val
        change (χ (((x : ZMod q).val : ℕ) : ZMod q) : ℂ) =
          (ψ (((x : ZMod q).val : ℕ) : ZMod q) : ℂ) at hv
        simpa only [ZMod.natCast_zmod_val] using hv
      subst ψ
      rfl

theorem PrimitiveRealCharacter.lift_inverse_eq (χ : PrimitiveRealCharacter)
    {N : ℕ} (hχ : χ.modulus ∣ N) :
    (DirichletCharacter.changeLevel hχ χ.complexCharacter)⁻¹ =
      DirichletCharacter.changeLevel hχ χ.complexCharacter := by
  rw [← map_inv, χ.complex_inv_eq]

theorem distinct_real_lifts_product_nonprincipal (χ ψ : PrimitiveRealCharacter)
    (hne : χ ≠ ψ) {N : ℕ} [NeZero N] (hχ : χ.modulus ∣ N) (hψ : ψ.modulus ∣ N) :
    DirichletCharacter.changeLevel hχ χ.complexCharacter *
      DirichletCharacter.changeLevel hψ ψ.complexCharacter ≠ 1 := by
  intro he
  have heq := (eq_inv_iff_mul_eq_one.mpr he).trans (ψ.lift_inverse_eq hψ)
  have hc := χ.asComplex.eq_of_changeLevel_eq ψ.asComplex hχ hψ heq
  exact hne (PrimitiveRealCharacter.asComplex_injective hc)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_Quadratic_QuadraticCharacterReal
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quadratic complex characters as real primitive characters -/

namespace Ostmann

open Complex

theorem quadratic_character_im_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : χ ^ 2 = 1) (x : ZMod q) : (χ x).im = 0 := by
  by_cases hx : IsUnit x
  · have hh := congrArg (fun ψ : DirichletCharacter ℂ q => ψ x) hχ
    have hs : χ x ^ 2 = 1 := by simpa only [pow_two, MulChar.mul_apply, MulChar.one_apply hx] using hh
    rcases (sq_eq_one_iff).mp hs with he | he <;> simp [he]
  · rw [χ.map_nonunit hx]
    rfl

noncomputable def realPartCharacter {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : ∀ x, (χ x).im = 0) : DirichletCharacter ℝ q where
  toFun x := (χ x).re
  map_one' := by simp
  map_mul' := by
    intro x y
    simp only [map_mul, Complex.mul_re, hχ, mul_zero, sub_zero]
  map_nonunit' := by intro x hx; simp [χ.map_nonunit hx]

theorem realPartCharacter_complexification {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hχ : ∀ x, (χ x).im = 0) :
    (realPartCharacter χ hχ).ringHomComp Complex.ofRealHom = χ := by
  ext x
  apply Complex.ext
  · rfl
  · simpa only [MulChar.ringHomComp_apply, Complex.ofRealHom_eq_coe, Complex.ofReal_im] using (hχ x).symm

theorem complexification_conductor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℝ q) :
    DirichletCharacter.conductor (χ.ringHomComp Complex.ofRealHom) = χ.conductor := by
  have hf (d : ℕ) : DirichletCharacter.FactorsThrough
      (χ.ringHomComp Complex.ofRealHom) d ↔ χ.FactorsThrough d := by
    by_cases hd : d ∣ q
    · rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd,
        DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
      constructor <;> intro h x hx
      · have hh := h hx
        rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at hh ⊢
        simpa using hh
      · have hh := h hx
        rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at hh ⊢
        simp [hh]
    · exact ⟨fun h => (hd h.dvd).elim, fun h => (hd h.dvd).elim⟩
  unfold DirichletCharacter.conductor
  congr 1
  ext d
  exact hf d

noncomputable def PrimitiveComplexCharacter.asReal (χ : PrimitiveComplexCharacter)
    (hχ : χ.character ^ 2 = 1) : PrimitiveRealCharacter where
  modulus := χ.modulus
  positive := χ.positive
  character := realPartCharacter χ.character (quadratic_character_im_zero χ.character hχ)
  primitive := by
    let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
    rw [DirichletCharacter.isPrimitive_def, ← complexification_conductor,
      realPartCharacter_complexification]
    exact χ.primitive
  nontrivial := by
    intro he
    apply χ.nontrivial
    rw [← realPartCharacter_complexification χ.character (quadratic_character_im_zero χ.character hχ), he]
    simp

@[simp] theorem PrimitiveComplexCharacter.asReal_asComplex (χ : PrimitiveComplexCharacter)
    (hχ : χ.character ^ 2 = 1) : (χ.asReal hχ).asComplex = χ := by
  cases χ
  dsimp only [asReal, PrimitiveRealCharacter.asComplex, PrimitiveRealCharacter.complexCharacter]
  congr
  exact realPartCharacter_complexification _ _

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterGammaRealBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform archimedean error on the real interval used by the zero argument -/

namespace Ostmann

open Complex Set
open scoped Classical

theorem gammaReal_analyticAt_pos (z : ℂ) (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.Gammaℝ z := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
  apply gammaReal_differentiableAt
  intro n hn
  have hh := congrArg Complex.re hn
  simp only [div_ofNat_re, neg_re, natCast_re] at hh
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem gammaReal_logDeriv_real_bound : ∃ C : ℝ, 0 < C ∧
    ∀ t : ℝ, 1 ≤ t → t ≤ 3 → ‖logDeriv Complex.Gammaℝ (t : ℂ)‖ ≤ C := by
  have hc : ContinuousOn (fun t : ℝ => logDeriv Complex.Gammaℝ (t : ℂ)) (Icc 1 3) := by
    intro t ht
    have htpos : 0 < (t : ℂ).re := by simp; linarith [ht.1]
    have ha := gammaReal_analyticAt_pos (t : ℂ) htpos
    exact ((ha.deriv.div ha (Complex.Gammaℝ_ne_zero_of_re_pos htpos)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro t ht ht'
  exact (hC t ⟨ht, ht'⟩).trans (by linarith [le_abs_self C])

theorem characterGamma_real_logDeriv_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℝ), 1 < s → s ≤ 2 →
      ‖logDeriv (DirichletCharacter.gammaFactor χ.character) (s : ℂ)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := gammaReal_logDeriv_real_bound
  refine ⟨C, hC, ?_⟩
  intro χ s hs hs'
  by_cases he : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    exact hb s hs.le (by linarith)
  · rw [show DirichletCharacter.gammaFactor χ.character =
        Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    rw [logDeriv_comp (g := fun u : ℂ => u + 1) (x := (s : ℂ))
      (gammaReal_analyticAt_pos ((s : ℂ) + 1) (by simp; linarith)).differentiableAt
      (differentiableAt_id.add_const (1 : ℂ))]
    simpa using hb (s + 1) (by linarith) (by linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CompletedDiskGrowthRate
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Common logarithmic growth rates for the function and its disk divisor -/

namespace Ostmann

theorem affine_log_growth_bound (a b x : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hx : 1 ≤ x) (hxab : x ≤ a * b) :
    x * (1 + Real.log x) ≤ a * (1 + Real.log a) * b * (1 + Real.log b) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hx0 : 0 < x := by linarith
  have hla := Real.log_nonneg ha
  have hlb := Real.log_nonneg hb
  have hlx := Real.log_nonneg hx
  have hl := Real.log_le_log hx0 hxab
  rw [Real.log_mul ha0.ne' hb0.ne'] at hl
  calc
    _ ≤ (a * b) * (1 + Real.log a + Real.log b) :=
      mul_le_mul hxab (by linarith) (by positivity) (by positivity)
    _ ≤ _ := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ha0.le hb0.le) hla) hlb]

theorem completed_circle_log_growth (χ : PrimitiveComplexCharacter) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (z : ℂ), ‖z‖ ≤ 3 * ((n : ℝ) + 1) →
      Real.log ‖χ.completed z‖ ≤ C * ((n : ℝ) + 9) * (1 + Real.log ((n : ℝ) + 9)) := by
  obtain ⟨A, hA, hg⟩ := character_completed_log_growth χ
  refine ⟨A * (3 * (1 + Real.log 3)), by positivity [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)], ?_⟩
  intro n z hz
  have hb : 1 ≤ (n : ℝ) + 9 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hh := hg (3 * n + 3) z (by push_cast; linarith)
  have hx : 1 ≤ ((3 * n + 3 : ℕ) : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) (3 * n + 3)]
  have hxab : ((3 * n + 3 : ℕ) : ℝ) + 3 ≤ 3 * ((n : ℝ) + 9) := by push_cast; linarith
  have hh' := mul_le_mul_of_nonneg_left
    (affine_log_growth_bound 3 ((n : ℝ) + 9) _ (by norm_num) hb hx hxab) hA.le
  exact hh.trans (by convert hh' using 1 <;> ring)

theorem completed_disk_mass_log_growth (χ : PrimitiveComplexCharacter) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∑ z ∈ completedDiskZeros χ ((n : ℝ) + 1), (analyticOrderNatAt χ.completed z : ℝ)) ≤
        C * ((n : ℝ) + 9) * (1 + Real.log ((n : ℝ) + 9)) := by
  let K : ℝ := 32 / Real.log (14 / 13)
  let a : ℝ := 2 * χ.modulus
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have hK : 0 < K := div_pos (by norm_num) (Real.log_pos (by norm_num))
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hla := Real.log_nonneg ha
  refine ⟨K * a * (1 + Real.log a), by positivity, ?_⟩
  intro n
  let x : ℝ := χ.modulus * (2 * ((n : ℝ) + 1) + 2)
  have hx : 1 ≤ x := by dsimp [x]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hxlog := Real.log_nonneg hx
  have hb : 1 ≤ (n : ℝ) + 9 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hxab : x ≤ a * ((n : ℝ) + 9) := by
    dsimp [x, a]
    nlinarith
  have h0 : 0 ≤ 2 * ((n : ℝ) + 1) + 1 := by positivity
  have h1 : 2 * ((n : ℝ) + 1) + 1 ≤ x := by dsimp [x]; nlinarith
  have hm := completedDiskZeros_mass_bound χ ((n : ℝ) + 1) (by positivity)
  change _ ≤ K * (2 * ((n : ℝ) + 1) + 1) * Real.log x at hm
  have hp : K * (2 * ((n : ℝ) + 1) + 1) * Real.log x ≤ K * (x * (1 + Real.log x)) := by
    nlinarith [mul_le_mul h1 (show Real.log x ≤ 1 + Real.log x by linarith)
      hxlog (by linarith : 0 ≤ x)]
  have hh := mul_le_mul_of_nonneg_left
    (affine_log_growth_bound a ((n : ℝ) + 9) x ha hb hx hxab) hK.le
  exact hm.trans (hp.trans (by convert hh using 1; ring))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LogDerivativeInnerSecondBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform second-logarithmic-derivative control inside a zero-free disk -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

theorem deriv_logDeriv_norm_le_inner_disk (g : ℂ → ℂ) (R A : ℝ)
    (hR : 0 < R) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (hne : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A)
    (w : ℂ) (hw : ‖w‖ ≤ R / 4) :
    ‖deriv (logDeriv g) w‖ ≤ 64 * A / R ^ 2 := by
  obtain ⟨F, hF0, hF, heF⟩ := exists_normalized_log_on_ball g R hR hg hne
  have hd : DifferentiableOn ℂ F (ball 0 R) := fun z hz =>
    (hF z hz).differentiableAt.differentiableWithinAt
  have hreal : MapsTo F (ball 0 R) {z : ℂ | z.re ≤ A} := by
    intro z hz
    change (F z).re ≤ A
    rw [normalized_log_re g F z (hne 0 (mem_ball_self hR)) (heF z hz)]
    exact hlog z hz
  have hquarter : 0 < R / 4 := by positivity
  have hsmall (z : ℂ) (hz : z ∈ closedBall w (R / 4)) : ‖z‖ ≤ R / 2 := by
    have hz' : ‖z - w‖ ≤ R / 4 := mem_closedBall_iff_norm.mp hz
    have ht := norm_add_le (z - w) w
    rw [sub_add_cancel] at ht
    linarith
  have hin (z : ℂ) (hz : z ∈ closedBall w (R / 4)) : z ∈ ball 0 R := by
    simpa only [mem_ball, dist_zero_right] using (hsmall z hz).trans_lt (by linarith : R / 2 < R)
  have hdc : DiffContOnCl ℂ F (ball w (R / 4)) := by
    refine ⟨fun z hz => (hF z (hin z (ball_subset_closedBall hz))).differentiableAt.differentiableWithinAt, ?_⟩
    rw [closure_ball w hquarter.ne']
    exact fun z hz => (hF z (hin z hz)).continuousAt.continuousWithinAt
  have hb : ∀ z ∈ sphere w (R / 4), ‖F z‖ ≤ 2 * A := by
    intro z hz
    have hz' := sphere_subset_closedBall hz
    have hn := hsmall z hz'
    have hh := Complex.borelCaratheodory_zero hA hd hreal hR (hin z hz') hF0
    apply hh.trans
    have hden : 0 < R - ‖z‖ := by linarith
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hwball : w ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right] using hw.trans_lt (by linarith : R / 4 < R)
  have he : deriv F =ᶠ[𝓝 w] logDeriv g := by
    filter_upwards [isOpen_ball.mem_nhds hwball] with z hz
    exact (hF z hz).deriv
  have he' : iteratedDeriv 2 F w = deriv (logDeriv g) w := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using he.deriv_eq
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hquarter hdc hb
  rw [he'] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  field_simp
  ring

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LogDerivativeDiskOscillation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing oscillation of logarithmic derivatives on inner disks -/

namespace Ostmann

open Complex Metric Set

theorem logDeriv_disk_oscillation (g : ℂ → ℂ) (R A : ℝ)
    (hR : 0 < R) (hA : 0 < A)
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) (hne : ∀ z ∈ ball 0 R, g z ≠ 0)
    (hlog : ∀ z ∈ ball 0 R, Real.log ‖g z‖ - Real.log ‖g 0‖ ≤ A)
    (x y : ℂ) (hx : ‖x‖ ≤ R / 4) (hy : ‖y‖ ≤ R / 4) :
    ‖logDeriv g y - logDeriv g x‖ ≤ (64 * A / R ^ 2) * ‖y - x‖ := by
  have hin (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (R / 4)) : z ∈ ball 0 R := by
    have hz' : ‖z‖ ≤ R / 4 := by simpa using hz
    simpa only [mem_ball, dist_zero_right] using hz'.trans_lt (by linarith : R / 4 < R)
  have hd (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) (R / 4)) :
      DifferentiableAt ℂ (logDeriv g) z :=
    ((hg z (hin z hz)).deriv.div (hg z (hin z hz)) (hne z (hin z hz))).differentiableAt
  apply (convex_closedBall (0 : ℂ) (R / 4)).norm_image_sub_le_of_norm_deriv_le hd
  · intro z hz
    exact deriv_logDeriv_norm_le_inner_disk g R A hR hA hg hne hlog z (by simpa using hz)
  · simpa using hx
  · simpa using hy

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CompletedQuotientGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform normalized growth of the actual zero-removed quotients -/

namespace Ostmann

open Complex Metric Set
open scoped BigOperators

theorem completed_quotient_log_growth (χ : PrimitiveComplexCharacter) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∃ g : ℂ → ℂ,
      (∀ z, AnalyticAt ℂ g z) ∧
      (∀ z, χ.completed z =
        finiteZeroPolynomial χ.completed (completedDiskZeros χ ((n : ℝ) + 1)) z * g z) ∧
      (∀ z ∈ closedBall (0 : ℂ) (2 * ((n : ℝ) + 1)), g z ≠ 0) ∧
      (∀ z ∈ ball (0 : ℂ) (2 * ((n : ℝ) + 1)),
        Real.log ‖g z‖ - Real.log ‖g 0‖ ≤
          C * ((n : ℝ) + 9) * (1 + Real.log ((n : ℝ) + 9)) +
            |Real.log ‖χ.completed 0‖| + 1) := by
  obtain ⟨U, hU, hf⟩ := completed_circle_log_growth χ
  obtain ⟨V, hV, hmass⟩ := completed_disk_mass_log_growth χ
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨U + V * Real.log 2 + 1, by positivity, ?_⟩
  intro n
  let R : ℝ := (n : ℝ) + 1
  let B : ℝ := ((n : ℝ) + 9) * (1 + Real.log ((n : ℝ) + 9))
  let M : ℝ := Real.exp (U * B)
  have hR : 0 < R := by dsimp [R]; positivity
  have hB : 0 < B := by
    have hh : 0 ≤ Real.log ((n : ℝ) + 9) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [B]
    positivity
  have hM : 0 < M := Real.exp_pos _
  have hf0 : χ.completed 0 ≠ 0 := χ.completed_ne_zero_left 0 (by simp)
  obtain ⟨g, hg, he, hne⟩ := completed_disk_quotient_exists χ R
  refine ⟨g, hg, he, hne, ?_⟩
  intro z hz
  have hfM : ∀ w ∈ sphere (0 : ℂ) (3 * R), ‖χ.completed w‖ ≤ M := by
    intro w hw
    have hwn : ‖w‖ = 3 * R := by simpa using hw
    have hh := hf n w (by change ‖w‖ ≤ 3 * R; exact hwn.le)
    apply (Real.le_exp_log ‖χ.completed w‖).trans
    apply Real.exp_le_exp.mpr
    simpa only [B, mul_assoc] using hh
  have hb := finite_zero_quotient_normalized_log χ.completed g (completedDiskZeros χ R)
    R M hR hM hf0 (fun w hw => ((mem_completedDiskZeros χ R w).mp hw).1) hg he
    hfM z (ball_subset_closedBall hz) (hne z (ball_subset_closedBall hz))
  have hm := mul_le_mul_of_nonneg_right (hmass n) hl2
  dsimp only [M] at hb
  rw [Real.log_exp] at hb
  dsimp only [R, B] at hb
  nlinarith [neg_le_abs (Real.log ‖χ.completed 0‖)]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CompletedPartialFractionLimit
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The limit of actual completed-L logarithmic-derivative differences -/

namespace Ostmann

open Complex Filter Metric Set
open scoped Topology

/-- Subtracting at two fixed nonzero points cancels the constant logarithmic
part. This is the exact part of Hadamard factorization needed below. -/
theorem completed_partial_fraction_difference_tendsto (χ : PrimitiveComplexCharacter)
    (x y : ℂ) (hx : χ.completed x ≠ 0) (hy : χ.completed y ≠ 0) :
    Tendsto (fun n : ℕ => completedZeroPartialFraction χ ((n : ℝ) + 1) y -
      completedZeroPartialFraction χ ((n : ℝ) + 1) x) atTop
      (𝓝 (logDeriv χ.completed y - logDeriv χ.completed x)) := by
  obtain ⟨C, hC, hgrowth⟩ := completed_quotient_log_growth χ
  let D : ℝ := |Real.log ‖χ.completed 0‖| + 1
  let A : ℕ → ℝ := fun n => C * ((n : ℝ) + 9) * (1 + Real.log ((n : ℝ) + 9)) + D
  have hA (n : ℕ) : 0 < A n := by
    have hl : 0 ≤ Real.log ((n : ℝ) + 9) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [A, D]
    positivity
  have hlim : Tendsto (fun n : ℕ =>
      (64 * A n / (2 * ((n : ℝ) + 1)) ^ 2) * ‖y - x‖) atTop (𝓝 0) := by
    have hh := (logarithmic_disk_rate C 9 D (by norm_num)).const_mul (16 * ‖y - x‖)
    simp only [mul_zero] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    dsimp [A]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn]
    ring
  have hlarge := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * (‖x‖ + ‖y‖) + 1)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) ?_ hlim
  filter_upwards [hlarge] with n hn
  obtain ⟨g, hg, he, hne, hl⟩ := hgrowth n
  have hxsize : ‖x‖ ≤ (2 * ((n : ℝ) + 1)) / 4 := by linarith [norm_nonneg y]
  have hysize : ‖y‖ ≤ (2 * ((n : ℝ) + 1)) / 4 := by linarith [norm_nonneg x]
  have hh := logDeriv_disk_oscillation g (2 * ((n : ℝ) + 1)) (A n)
    (by positivity) (hA n) (fun z _ => hg z)
    (fun z hz => hne z (ball_subset_closedBall hz))
    (by simpa only [A, D, add_assoc] using hl) x y hxsize hysize
  have hx' := completed_logDeriv_remove_finite χ ((n : ℝ) + 1) g hg he x hx
  have hy' := completed_logDeriv_remove_finite χ ((n : ℝ) + 1) g hg he y hy
  have herr : (completedZeroPartialFraction χ ((n : ℝ) + 1) y -
      completedZeroPartialFraction χ ((n : ℝ) + 1) x) -
      (logDeriv χ.completed y - logDeriv χ.completed x) =
        -(logDeriv g y - logDeriv g x) := by
    rw [← hx', ← hy']
    ring
  rw [herr, norm_neg]
  exact hh

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FiniteInverseSquareDensity
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Inverse-square summability from a three-halves counting bound -/

namespace Ostmann

open scoped Classical BigOperators

/-- Sorting by height converts the counting bound into a convergent 4/3-series. -/
theorem finite_exp_three_halves_sum {ι : Type*} (S : Finset ι)
    (y : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hy : ∀ i ∈ S, 0 ≤ y i)
    (hc : ∀ t : ℝ, 0 ≤ t →
      ((S.filter (fun i => y i ≤ t)).card : ℝ) ≤ B * Real.exp ((3 / 2) * t)) :
    (∑ i ∈ S, Real.exp (-2 * y i)) ≤ B ^ (4 / 3 : ℝ) *
      ∑ j ∈ Finset.range S.card, ((j + 1 : ℕ) : ℝ) ^ (-4 / 3 : ℝ) := by
  revert hy hc
  refine Finset.strongInductionOn S ?_
  intro S ih hy hc
  by_cases hn : S.Nonempty
  · obtain ⟨i, hi, hmax⟩ := S.exists_max_image y hn
    have hf : S.filter (fun j => y j ≤ y i) = S := Finset.filter_eq_self.mpr hmax
    have hcard := hc (y i) (hy i hi)
    rw [hf] at hcard
    have hn0 : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hn
    have hm := mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg (-((3 / 2) * y i)))
    have he : Real.exp ((3 / 2) * y i) * Real.exp (-((3 / 2) * y i)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [mul_assoc, he, mul_one] at hm
    have hd : Real.exp (-((3 / 2) * y i)) ≤ B / S.card := by
      apply (le_div_iff₀ hn0).mpr
      simpa only [mul_comm] using hm
    have hpoint : Real.exp (-2 * y i) ≤ B ^ (4 / 3 : ℝ) * (S.card : ℝ) ^ (-4 / 3 : ℝ) := by
      have hh := Real.rpow_le_rpow (Real.exp_nonneg _) hd (by norm_num : (0 : ℝ) ≤ 4 / 3)
      rw [← Real.exp_mul, Real.div_rpow hB hn0.le, div_eq_mul_inv] at hh
      convert hh using 1
      · congr 1; ring
      · rw [show (-4 / 3 : ℝ) = -(4 / 3) by ring, Real.rpow_neg hn0.le]
        rfl
    have hrest := ih (S.erase i) (Finset.erase_ssubset hi)
      (fun j hj => hy j (Finset.mem_of_mem_erase hj))
      (fun t ht => (show (((S.erase i).filter (fun j => y j ≤ t)).card : ℝ) ≤
        (S.filter (fun j => y j ≤ t)).card from by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))).trans
          (hc t ht))
    have hsize : (S.erase i).card + 1 = S.card := Finset.card_erase_add_one hi
    rw [← Finset.sum_erase_add S (fun i => Real.exp (-2 * y i)) hi]
    rw [← hsize, Finset.sum_range_succ, mul_add]
    exact add_le_add hrest (by simpa only [hsize] using hpoint)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty, Finset.card_empty, Finset.range_zero, mul_zero, le_refl]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_InverseSquareZeroSum
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Convergence of inverse-square weights from the ordinary zero count -/

namespace Ostmann

open scoped Classical BigOperators

theorem zero_height_log_three_halves {ι : Type*} (S : Finset ι) (h : ι → ℝ)
    (Q K : ℝ) (hQ : 1 ≤ Q) (hK : 0 ≤ K) (hh : ∀ i ∈ S, 0 ≤ h i)
    (hcount : ∀ t : ℝ, 0 ≤ t →
      ((S.filter (fun i => h i ≤ t)).card : ℝ) ≤ K * (t + 1) * Real.log (Q * (t + 2))) :
    ∀ s : ℝ, 0 ≤ s →
      ((S.filter (fun i => Real.log (1 + h i) ≤ s)).card : ℝ) ≤
        (2 * K * (Real.log Q + 5)) * Real.exp ((3 / 2) * s) := by
  intro s hs
  have hQp : 0 < Q := by linarith
  have he : 1 ≤ Real.exp s := Real.one_le_exp hs
  have hhf : 1 ≤ Real.exp (s / 2) := Real.one_le_exp (by linarith)
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have hsub : S.filter (fun i => Real.log (1 + h i) ≤ s) ⊆
      S.filter (fun i => h i ≤ Real.exp s) := by
    intro i hi
    obtain ⟨hiS, hi⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_filter.mpr ⟨hiS, ?_⟩
    have hex := (Real.log_le_iff_le_exp (by linarith [hh i hiS] : 0 < 1 + h i)).mp hi
    linarith
  have hlog : Real.log (Q * (Real.exp s + 2)) ≤
      (Real.log Q + 5) * Real.exp (s / 2) := by
    rw [Real.log_mul hQp.ne' (by positivity : Real.exp s + 2 ≠ 0)]
    have hinside : Real.exp s + 2 ≤ 3 * Real.exp s := by linarith
    have hl := Real.log_le_log (by positivity : 0 < Real.exp s + 2) hinside
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hl
    have hl3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    have hs' := Real.add_one_le_exp (s / 2)
    have hq := mul_le_mul_of_nonneg_left hhf (by linarith : 0 ≤ Real.log Q + 3)
    nlinarith
  have hl0 : 0 ≤ Real.log (Q * (Real.exp s + 2)) := Real.log_nonneg (by nlinarith)
  calc
    _ ≤ ((S.filter (fun i => h i ≤ Real.exp s)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ K * (Real.exp s + 1) * Real.log (Q * (Real.exp s + 2)) :=
      hcount (Real.exp s) (Real.exp_nonneg _)
    _ ≤ (K * (2 * Real.exp s)) * ((Real.log Q + 5) * Real.exp (s / 2)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) hK
      · exact hlog
      · exact hl0
      · positivity
    _ = (2 * K * (Real.log Q + 5)) * Real.exp ((3 / 2) * s) := by
      rw [show (3 / 2 : ℝ) * s = s + s / 2 by ring, Real.exp_add]
      ring

/-- Only the ordinary O(T log T) count is needed, not a zero-free region. -/
theorem inverse_square_weights_summable {ι : Type*} (h : ι → ℝ)
    (Q K : ℝ) (hQ : 1 ≤ Q) (hK : 0 ≤ K) (hh : ∀ i, 0 ≤ h i)
    (hcount : ∀ (S : Finset ι) (t : ℝ), 0 ≤ t →
      ((S.filter (fun i => h i ≤ t)).card : ℝ) ≤ K * (t + 1) * Real.log (Q * (t + 2))) :
    Summable (fun i => ((1 + h i) ^ 2)⁻¹) := by
  let B := 2 * K * (Real.log Q + 5)
  let f : ℕ → ℝ := fun j => ((j + 1 : ℕ) : ℝ) ^ (-4 / 3 : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity [Real.log_nonneg hQ]
  have hf : Summable f := by
    have ht := (Real.summable_nat_rpow.mpr (by norm_num : (-4 / 3 : ℝ) < -1))
    simpa only [f, Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr ht
  have he (i : ι) : Real.exp (-2 * Real.log (1 + h i)) = ((1 + h i) ^ 2)⁻¹ := by
    rw [show -2 * Real.log (1 + h i) = -(Real.log (1 + h i) + Real.log (1 + h i)) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log (by linarith [hh i] : 0 < 1 + h i), pow_two]
  apply summable_of_sum_le (fun i => by positivity) (c := B ^ (4 / 3 : ℝ) * ∑' j, f j)
  intro S
  have hb := finite_exp_three_halves_sum S (fun i => Real.log (1 + h i)) B hB
    (fun i _ => Real.log_nonneg (by linarith [hh i]))
    (zero_height_log_three_halves S h Q K hQ hK (fun i _ => hh i) (hcount S))
  simp_rw [he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (hf.sum_le_tsum (Finset.range S.card) (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (Real.rpow_nonneg hB _))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterZeroInverseSquare
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Square-decaying sums over the actual character zeros -/

namespace Ostmann

open scoped Classical BigOperators

theorem character_zero_inverse_square_summable (χ : PrimitiveComplexCharacter) :
    Summable (fun i => ((1 + |((actualCharacterZeros χ).zeros i).im|) ^ 2)⁻¹) := by
  let Z := actualCharacterZeros χ
  let K : ℝ := 32 / Real.log (14 / 13)
  have hK : 0 ≤ K := div_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  apply inverse_square_weights_summable (fun i => |(Z.zeros i).im|) χ.modulus K hq hK
    (fun _ => abs_nonneg _)
  intro S t ht
  have hsub : S.filter (fun i => |(Z.zeros i).im| ≤ t) ⊆ Z.heightIndices t := by
    intro i hi
    exact (Z.mem_heightIndices t i).mpr (Finset.mem_filter.mp hi).2
  have hc := Z.count_bound_of_multiplicity (actualCharacterZeros_respectsMultiplicity χ) t ht
  rw [Z.count_zero_eq_card] at hc
  exact (show (((S.filter (fun i => |(Z.zeros i).im| ≤ t)).card : ℝ)) ≤
    (Z.heightIndices t).card from by exact_mod_cast Finset.card_le_card hsub).trans hc

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealCharacterZeroConvergence
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absolute convergence of the real-axis zero kernel -/

namespace Ostmann

theorem real_zero_kernel_square_bound (a y δ : ℝ) (hδ : 0 < δ)
    (ha : δ ≤ a) (ha2 : a ≤ 2) :
    realZeroKernel a y ≤ (8 + 4 * δ⁻¹) * ((1 + |y|) ^ 2)⁻¹ := by
  have ha0 : 0 < a := hδ.trans_le ha
  have hw : 0 < (1 + |y|) ^ 2 := sq_pos_of_pos (by positivity)
  by_cases hy : |y| ≤ 1
  · have hk := (realZeroKernel_le_inv (y := y) ha0).trans (inv_anti₀ hδ ha)
    have hwle : (1 + |y|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg y]
    have hwi : (1 / 4 : ℝ) ≤ ((1 + |y|) ^ 2)⁻¹ := by
      simpa using (inv_anti₀ hw hwle)
    have hm := mul_le_mul_of_nonneg_left hwi (by positivity : 0 ≤ 4 * δ⁻¹)
    have hn := mul_le_mul_of_nonneg_right (show 4 * δ⁻¹ ≤ 8 + 4 * δ⁻¹ by linarith)
      (inv_nonneg.mpr hw.le)
    nlinarith
  · have hy1 : 1 < |y| := lt_of_not_ge hy
    have hy2 : 0 < y ^ 2 := by nlinarith [sq_abs y]
    have hden : 0 < a ^ 2 + y ^ 2 := by positivity
    have hk : realZeroKernel a y ≤ 2 / y ^ 2 := by
      unfold realZeroKernel
      apply div_le_div₀ (by norm_num : (0 : ℝ) ≤ 2) ha2 hy2
      nlinarith [sq_nonneg a]
    have hwle : (1 + |y|) ^ 2 ≤ 4 * y ^ 2 := by nlinarith [sq_abs y]
    have hfrac : 2 / y ^ 2 ≤ 8 * ((1 + |y|) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ hy2 hw]
      linarith
    exact (hk.trans hfrac).trans (mul_le_mul_of_nonneg_right (by have := inv_pos.mpr hδ; linarith)
      (inv_nonneg.mpr hw.le))

/-- The actual faithful zero family supplies the convergence field of the
published real-character Hadamard expansion. -/
theorem real_character_zero_kernel_summable (χ : PrimitiveRealCharacter) (s : ℝ)
    (hs : 1 < s) (hs2 : s ≤ 2) :
    Summable (fun i => realZeroKernel (s - ((realCharacterActualZeros χ).zeros i).re)
      ((realCharacterActualZeros χ).zeros i).im) := by
  let Z := realCharacterActualZeros χ
  have hh := character_zero_inverse_square_summable χ.asComplex
  apply Summable.of_nonneg_of_le
    (fun i => realZeroKernel_nonneg (by linarith [(Z.in_strip i).2]))
    (fun i => real_zero_kernel_square_bound _ _ (s - 1) (by linarith)
      (by linarith [(Z.in_strip i).2]) (by linarith [(Z.in_strip i).1]))
    (hh.mul_left (8 + 4 * (s - 1)⁻¹))

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealZeroReflectionPermutation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reflection as an actual permutation of all zero multiplicity labels -/

namespace Ostmann

open scoped Classical

theorem PrimitiveRealCharacter.zero_reflection (χ : PrimitiveRealCharacter)
    (z : ℂ) (hz : z ∈ complexCharacterZeros χ.asComplex) :
    1 - z ∈ complexCharacterZeros χ.asComplex := by
  refine ⟨by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.2.1],
    by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.1], ?_⟩
  have hh := (characterZeroOrder_pos_iff χ.asComplex z).mpr hz.2.2
  rw [characterZeroOrder_eq_nat, Int.natCast_pos] at hh
  have hr := χ.zero_reflection_order z hz.1 hz.2.1
  apply (characterZeroOrder_pos_iff χ.asComplex (1 - z)).mp
  rw [characterZeroOrder_eq_nat, Int.natCast_pos]
  change 0 < analyticOrderNatAt χ.L (1 - z)
  rw [hr]
  exact hh

noncomputable def realZeroCopyReflection (χ : PrimitiveRealCharacter) :
    CharacterZeroCopy χ.asComplex ≃ CharacterZeroCopy χ.asComplex := by
  let f : CharacterZeroCopy χ.asComplex → CharacterZeroCopy χ.asComplex := fun c =>
    ⟨(1 - c.val.1, c.val.2), χ.zero_reflection c.val.1 c.property.1, by
      change c.val.2 < analyticOrderNatAt χ.L (1 - c.val.1)
      rw [χ.zero_reflection_order _ c.property.1.1 c.property.1.2.1]
      exact c.property.2⟩
  apply Function.Involutive.toPerm (f := f)
  intro c
  apply Subtype.ext
  apply Prod.ext
  · change 1 - (1 - c.val.1) = c.val.1
    ring
  · rfl

noncomputable def realZeroIndexReflection (χ : PrimitiveRealCharacter) : ℕ ≃ ℕ :=
  (faithfulCharacterZeroEquiv χ.asComplex).trans
    ((realZeroCopyReflection χ).trans (faithfulCharacterZeroEquiv χ.asComplex).symm)

theorem realZeroIndexReflection_zeros (χ : PrimitiveRealCharacter) (i : ℕ) :
    (realCharacterActualZeros χ).zeros (realZeroIndexReflection χ i) =
      1 - (realCharacterActualZeros χ).zeros i := by
  simp [realCharacterActualZeros, actualCharacterZeros, characterZeroEnumeration,
    realZeroIndexReflection, realZeroCopyReflection, Function.Involutive.toPerm]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_RealCompletedHadamard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The real-axis Hadamard identity from actual disk sums -/

namespace Ostmann

open Complex Filter
open scoped Topology BigOperators

noncomputable def realCharacterZeroSum (χ : PrimitiveRealCharacter) (s : ℝ) : ℝ :=
  ∑' i, realZeroKernel (s - ((realCharacterActualZeros χ).zeros i).re)
    ((realCharacterActualZeros χ).zeros i).im

theorem completed_partial_real_limit (χ : PrimitiveRealCharacter) (s : ℝ)
    (hsum : Summable (fun i => realZeroKernel (s - ((realCharacterActualZeros χ).zeros i).re)
      ((realCharacterActualZeros χ).zeros i).im)) :
    Tendsto (fun n : ℕ => (completedZeroPartialFraction χ.asComplex ((n : ℝ) + 1) (s : ℂ)).re)
      atTop (𝓝 (realCharacterZeroSum χ s)) := by
  let Z := realCharacterActualZeros χ
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hh := hsum.hasSum.comp (Z.tendsto_diskIndices.comp hn)
  unfold realCharacterZeroSum
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [completedZeroPartialFraction_index_sum χ.asComplex (faithfulCharacterZeroEquiv χ.asComplex),
    Complex.re_sum]
  exact Finset.sum_congr rfl (fun i _ => realZeroKernel_complex s _)

theorem real_zero_kernel_reflection (χ : PrimitiveRealCharacter) (s : ℝ) (i : ℕ) :
    realZeroKernel (1 - s - ((realCharacterActualZeros χ).zeros i).re)
        ((realCharacterActualZeros χ).zeros i).im =
      -realZeroKernel (s - ((realCharacterActualZeros χ).zeros (realZeroIndexReflection χ i)).re)
        ((realCharacterActualZeros χ).zeros (realZeroIndexReflection χ i)).im := by
  rw [realZeroIndexReflection_zeros]
  rw [← realZeroKernel_complex s]
  have he : (s : ℂ) - (1 - (realCharacterActualZeros χ).zeros i) =
      -(((1 - s : ℝ) : ℂ) - (realCharacterActualZeros χ).zeros i) := by push_cast; ring
  rw [he, inv_neg, Complex.neg_re, neg_neg, realZeroKernel_complex]

theorem real_zero_sum_reflection (χ : PrimitiveRealCharacter) (s : ℝ)
    (hs : 1 < s) (hs2 : s ≤ 2) :
    Summable (fun i => realZeroKernel (1 - s - ((realCharacterActualZeros χ).zeros i).re)
      ((realCharacterActualZeros χ).zeros i).im) ∧
      realCharacterZeroSum χ (1 - s) = -realCharacterZeroSum χ s := by
  have hp := real_character_zero_kernel_summable χ s hs hs2
  have hr := hp.comp_injective (realZeroIndexReflection χ).injective
  constructor
  · simpa only [real_zero_kernel_reflection, Function.comp_def] using hr.neg
  · unfold realCharacterZeroSum
    simp_rw [real_zero_kernel_reflection]
    rw [tsum_neg]
    congr 1
    exact (realZeroIndexReflection χ).tsum_eq
      (fun i => realZeroKernel (s - ((realCharacterActualZeros χ).zeros i).re)
        ((realCharacterActualZeros χ).zeros i).im)

/-- Reflection cancels the constant term in the canonical product. -/
theorem real_completed_hadamard_identity (χ : PrimitiveRealCharacter) (s : ℝ)
    (hs : 1 < s) (hs2 : s ≤ 2) :
    realCharacterZeroSum χ s = (logDeriv χ.asComplex.completed (s : ℂ)).re +
      (1 / 2) * Real.log χ.modulus := by
  have hp := completed_partial_real_limit χ s (real_character_zero_kernel_summable χ s hs hs2)
  obtain ⟨hn, heq⟩ := real_zero_sum_reflection χ s hs hs2
  have hm := completed_partial_real_limit χ (1 - s) hn
  have hc := completed_partial_fraction_difference_tendsto χ.asComplex
    (1 - (s : ℂ)) (s : ℂ)
    (χ.asComplex.completed_ne_zero_left _ (by simp; linarith))
    (χ.asComplex.completed_ne_zero_right _ (by simp; linarith))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  have hd := hp.sub hm
  have hlim : realCharacterZeroSum χ s - realCharacterZeroSum χ (1 - s) =
      (logDeriv χ.asComplex.completed (s : ℂ) - logDeriv χ.asComplex.completed (1 - (s : ℂ))).re := by
    apply tendsto_nhds_unique hd
    simpa only [Function.comp_def, Complex.sub_re, Complex.ofReal_sub, Complex.ofReal_one] using hr
  rw [heq, χ.completed_logDeriv_reflection (s : ℂ) (by simp; linarith)] at hlim
  simp only [Complex.sub_re, Complex.neg_re, Complex.log_re, Complex.norm_natCast] at hlim
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ActualRealZeroExpansion
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual real-character Hadamard expansion -/

namespace Ostmann

open Complex

noncomputable def actualRealZeroErrorConstant : ℝ := Classical.choose characterGamma_real_logDeriv_bound

/-- The exact zero-sum identity has only the bounded archimedean term left over. -/
theorem real_character_hadamard_error (χ : PrimitiveRealCharacter) (s : ℝ)
    (hs : 1 < s) (hs2 : s ≤ 2) :
    |realCharacterZeroSum χ s - χ.logDerivative s - (1 / 2) * Real.log χ.modulus| ≤
      actualRealZeroErrorConstant := by
  have he : realCharacterZeroSum χ s - χ.logDerivative s - (1 / 2) * Real.log χ.modulus =
      (logDeriv (DirichletCharacter.gammaFactor χ.complexCharacter) (s : ℂ)).re := by
    rw [real_completed_hadamard_identity χ s hs hs2,
      χ.asComplex.completed_logDeriv_eq_add (s : ℂ) (by simp; linarith)]
    rw [PrimitiveRealCharacter.asComplex_L]
    change (logDeriv χ.L (s : ℂ) +
      logDeriv (DirichletCharacter.gammaFactor χ.complexCharacter) (s : ℂ)).re +
      (1 / 2) * Real.log χ.modulus - χ.logDerivative s -
      (1 / 2) * Real.log χ.modulus = _
    simp only [Complex.add_re, PrimitiveRealCharacter.logDerivative, logDeriv_apply]
    ring
  rw [he]
  exact (abs_re_le_norm _).trans
    ((Classical.choose_spec characterGamma_real_logDeriv_bound).2 χ.asComplex s hs hs2)

/-- The Hadamard expansion fields of the real-zero input. -/
noncomputable def actualRealCharacterZeroExpansion (χ : PrimitiveRealCharacter) :
    RealCharacterZeroExpansion χ actualRealZeroErrorConstant where
  zeros := (realCharacterActualZeros χ).zeros
  in_strip := (realCharacterActualZeros χ).in_strip
  actual_zero := (realCharacterActualZeros χ).actual_zero
  summable := real_character_zero_kernel_summable χ
  hadamard := real_character_hadamard_error χ

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexCharacterConjugation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Conjugation and multiplicity for general primitive character zeros -/

namespace Ostmann

open Complex Filter Set
open scoped ComplexConjugate Topology

theorem iteratedDeriv_conjugation (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n (conj ∘ f ∘ conj) = conj ∘ iteratedDeriv n f ∘ conj := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iteratedDeriv_succ, ih, deriv_conj_conj]

theorem analyticOrderAt_conjugation (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z)
    (z : ℂ) (hfinite : analyticOrderAt f (conj z) ≠ ⊤) :
    analyticOrderAt (conj ∘ f ∘ conj) z = analyticOrderAt f (conj z) := by
  have hd : Differentiable ℂ (conj ∘ f ∘ conj) := by
    intro w
    simpa only [Complex.conj_conj] using (hf (conj w)).differentiableAt.conj_conj
  have hg := hd.analyticAt z
  have hn : analyticOrderAt f (conj z) = (analyticOrderNatAt f (conj z) : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt hfinite).symm
  rw [hn]
  apply (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hg).mpr
  have hh := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hf (conj z))).mp hn
  simp only [iteratedDeriv_conjugation, Function.comp_apply]
  constructor
  · intro k hk
    rw [hh.1 k hk, map_zero]
  · intro he
    apply hh.2
    have he' := congrArg conj he
    simpa only [Complex.conj_conj, map_zero] using he'

theorem PrimitiveComplexCharacter.inverse_L_conj_right (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 1 < s.re) : χ.inverse.L (conj s) = conj (χ.L s) := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  change DirichletCharacter.LFunction (χ.character⁻¹) (conj s) =
    conj (DirichletCharacter.LFunction χ.character s)
  rw [(χ.character⁻¹).LFunction_eq_LSeries (by simpa using hs), χ.character.LFunction_eq_LSeries hs]
  change (∑' n, LSeries.term _ (conj s) n) = conj (∑' n, LSeries.term _ s n)
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n; simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have ha : (n : ℂ).arg ≠ Real.pi := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) from rfl,
        Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact Real.pi_pos.ne
    rw [Complex.cpow_conj _ _ ha]
    simp only [map_div₀, map_natCast, ← MulChar.star_eq_inv, MulChar.star_apply, RCLike.star_def]

theorem PrimitiveComplexCharacter.inverse_L_eq_conjugate (χ : PrimitiveComplexCharacter) :
    χ.inverse.L = conj ∘ χ.L ∘ conj := by
  have hd : Differentiable ℂ (conj ∘ χ.L ∘ conj) := by
    intro z
    simpa only [Complex.conj_conj] using (χ.L_analytic (conj z)).differentiableAt.conj_conj
  have hg := hd.differentiableOn.analyticOnNhd isOpen_univ
  have hf : AnalyticOnNhd ℂ χ.inverse.L univ := fun z _ => χ.inverse.L_analytic z
  apply hf.eq_of_eventuallyEq hg (z₀ := (2 : ℂ))
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  simpa only [Function.comp_apply, Complex.conj_conj] using
    χ.inverse_L_conj_right (conj z) (by simpa using hz)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CompletedCharacterConjugation
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The completed functional equation with conjugation -/

namespace Ostmann

open Complex Filter Set
open scoped ComplexConjugate Topology

theorem gammaReal_conjugate (s : ℂ) : Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  have hpi : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_pos.ne
  simp only [Complex.Gammaℝ_def, map_mul]
  have hg : Complex.Gamma (conj s / 2) = conj (Complex.Gamma (s / 2)) := by
    simpa only [map_div₀, map_ofNat] using Complex.Gamma_conj (s / 2)
  rw [hg]
  have hh := Complex.cpow_conj (Real.pi : ℂ) (-s / 2) hpi
  simpa only [map_neg, map_div₀, map_ofNat, Complex.conj_ofReal] using
    congrArg (fun z : ℂ => z * conj (Complex.Gamma (s / 2))) hh

theorem character_even_inverse_iff {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (χ⁻¹).Even ↔ χ.Even := by
  change (χ⁻¹) (-1) = 1 ↔ χ (-1) = 1
  rw [← MulChar.star_eq_inv, MulChar.star_apply, RCLike.star_def]
  constructor
  · intro h
    have hh := congrArg conj h
    simpa only [Complex.conj_conj, map_one] using hh
  · intro h
    rw [h, map_one]

theorem PrimitiveComplexCharacter.gammaFactor_inverse_conj (χ : PrimitiveComplexCharacter) (s : ℂ) :
    DirichletCharacter.gammaFactor χ.inverse.character (conj s) =
      conj (DirichletCharacter.gammaFactor χ.character s) := by
  change DirichletCharacter.gammaFactor (χ.character⁻¹) (conj s) = _
  by_cases he : χ.character.Even
  · simp only [DirichletCharacter.gammaFactor, (character_even_inverse_iff χ.character).mpr he,
      he, ite_true, if_true, gammaReal_conjugate]
  · have hi : ¬(χ.character⁻¹).Even := fun h => he ((character_even_inverse_iff χ.character).mp h)
    simpa only [DirichletCharacter.gammaFactor, he, hi, ite_false, if_false, map_add, map_one] using
      gammaReal_conjugate (s + 1)

theorem PrimitiveComplexCharacter.gammaInverse_inverse_conj (χ : PrimitiveComplexCharacter) (s : ℂ) :
    χ.inverse.gammaInverse (conj s) = conj (χ.gammaInverse s) := by
  simp only [PrimitiveComplexCharacter.gammaInverse, χ.gammaFactor_inverse_conj, map_inv₀]

theorem PrimitiveComplexCharacter.completed_inverse_conj_right (χ : PrimitiveComplexCharacter)
    (s : ℂ) (hs : 0 < s.re) : χ.inverse.completed (conj s) = conj (χ.completed s) := by
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hscne : conj s ≠ 0 := by intro h; apply hsne; simpa using congrArg conj h
  apply mul_right_cancel₀ (χ.inverse.gammaInverse_ne_zero (conj s) (by simpa using hs))
  calc
    _ = χ.inverse.L (conj s) := (χ.inverse.L_eq_completed_mul (conj s) hscne).symm
    _ = conj (χ.L s) := by
      have he := congrFun χ.inverse_L_eq_conjugate (conj s)
      simpa only [Function.comp_apply, Complex.conj_conj] using he
    _ = _ := by
      rw [χ.L_eq_completed_mul s hsne, map_mul, χ.gammaInverse_inverse_conj]

theorem PrimitiveComplexCharacter.inverse_completed_eq_conjugate (χ : PrimitiveComplexCharacter) :
    χ.inverse.completed = conj ∘ χ.completed ∘ conj := by
  have hd : Differentiable ℂ (conj ∘ χ.completed ∘ conj) := by
    intro z
    simpa only [Complex.conj_conj] using (χ.completed_analytic (conj z)).differentiableAt.conj_conj
  have hg := hd.differentiableOn.analyticOnNhd isOpen_univ
  have hf : AnalyticOnNhd ℂ χ.inverse.completed univ := fun z _ => χ.inverse.completed_analytic z
  apply hf.eq_of_eventuallyEq hg (z₀ := (2 : ℂ))
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (0 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  simpa only [Function.comp_apply, Complex.conj_conj] using
    χ.completed_inverse_conj_right (conj z) (by simpa using hz)

theorem PrimitiveComplexCharacter.completed_logDeriv_self_reflection
    (χ : PrimitiveComplexCharacter) (s : ℂ) (hs : 1 ≤ s.re) :
    logDeriv χ.completed (1 - conj s) =
      -Complex.log (χ.modulus : ℂ) - conj (logDeriv χ.completed s) := by
  rw [χ.completed_logDeriv_reflection (conj s) (by simpa using hs),
    χ.inverse_completed_eq_conjugate, logDeriv_apply, deriv_conj_conj]
  simp only [Function.comp_apply, Complex.conj_conj, logDeriv_apply, map_div₀]

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ShiftedRealHadamard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real parts of the Hadamard identity off the real axis -/

namespace Ostmann

open Complex Filter
open scoped Topology BigOperators

theorem realZeroKernel_complex_sub (s ρ : ℂ) :
    ((s - ρ)⁻¹).re = realZeroKernel (s.re - ρ.re) (s.im - ρ.im) := by
  simp only [Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    realZeroKernel, pow_two]

theorem inverse_square_shift_bound (y t : ℝ) :
    ((1 + |t - y|) ^ 2)⁻¹ ≤ (1 + |t|) ^ 2 * ((1 + |y|) ^ 2)⁻¹ := by
  have htri : |y| ≤ |t| + |t - y| := by
    have hh := abs_add_le (t - y) (-t)
    have he : t - y + -t = -y := by ring
    rw [he, abs_neg, abs_neg] at hh
    linarith
  have hb : 1 + |y| ≤ (1 + |t|) * (1 + |t - y|) := by
    nlinarith [mul_nonneg (abs_nonneg t) (abs_nonneg (t - y))]
  have hs : (1 + |y|) ^ 2 ≤ (1 + |t|) ^ 2 * (1 + |t - y|) ^ 2 := by
    calc
      _ ≤ ((1 + |t|) * (1 + |t - y|)) ^ 2 := by gcongr
      _ = _ := by ring
  have hy : 0 < (1 + |y|) ^ 2 := by positivity
  have ht : 0 < (1 + |t - y|) ^ 2 := by positivity
  rw [← div_eq_mul_inv, ← one_div, div_le_div_iff₀ ht hy]
  simpa using hs

noncomputable def shiftedRealCharacterZeroSum (χ : PrimitiveRealCharacter) (s : ℂ) : ℝ :=
  ∑' i, ((s - (realCharacterActualZeros χ).zeros i)⁻¹).re

theorem shifted_real_zero_summable (χ : PrimitiveRealCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    Summable (fun i => ((s - (realCharacterActualZeros χ).zeros i)⁻¹).re) := by
  let Z := realCharacterActualZeros χ
  have hh := character_zero_inverse_square_summable χ.asComplex
  let C := 8 + 4 * (s.re - 1)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  apply Summable.of_nonneg_of_le
    (fun i => by rw [realZeroKernel_complex_sub]; exact realZeroKernel_nonneg (by linarith [(Z.in_strip i).2]))
    (fun i => ?_) (hh.mul_left (C * (1 + |s.im|) ^ 2))
  rw [realZeroKernel_complex_sub]
  calc
    _ ≤ C * ((1 + |s.im - (Z.zeros i).im|) ^ 2)⁻¹ :=
      real_zero_kernel_square_bound _ _ (s.re - 1) (by linarith)
        (by linarith [(Z.in_strip i).2]) (by linarith [(Z.in_strip i).1])
    _ ≤ C * ((1 + |s.im|) ^ 2 * ((1 + |(Z.zeros i).im|) ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left (inverse_square_shift_bound _ _) hC
    _ = _ := by dsimp [Z, realCharacterActualZeros]; ring

theorem shifted_completed_partial_real_limit (χ : PrimitiveRealCharacter) (s : ℂ)
    (hsum : Summable (fun i => ((s - (realCharacterActualZeros χ).zeros i)⁻¹).re)) :
    Tendsto (fun n : ℕ => (completedZeroPartialFraction χ.asComplex ((n : ℝ) + 1) s).re)
      atTop (𝓝 (shiftedRealCharacterZeroSum χ s)) := by
  let Z := realCharacterActualZeros χ
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hh := hsum.hasSum.comp (Z.tendsto_diskIndices.comp hn)
  unfold shiftedRealCharacterZeroSum
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [completedZeroPartialFraction_index_sum χ.asComplex (faithfulCharacterZeroEquiv χ.asComplex),
    Complex.re_sum]
  rfl

theorem shifted_real_zero_reflection (χ : PrimitiveRealCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    Summable (fun i => ((1 - s - (realCharacterActualZeros χ).zeros i)⁻¹).re) ∧
      shiftedRealCharacterZeroSum χ (1 - s) = -shiftedRealCharacterZeroSum χ s := by
  have he (i : ℕ) : ((1 - s - (realCharacterActualZeros χ).zeros i)⁻¹).re =
      -((s - (realCharacterActualZeros χ).zeros (realZeroIndexReflection χ i))⁻¹).re := by
    rw [realZeroIndexReflection_zeros]
    have ha : 1 - s - (realCharacterActualZeros χ).zeros i =
        -(s - (1 - (realCharacterActualZeros χ).zeros i)) := by ring
    rw [ha, inv_neg, Complex.neg_re]
  have hsum := shifted_real_zero_summable χ s hs hs2
  constructor
  · simpa only [he, Function.comp_def] using
      (hsum.comp_injective (realZeroIndexReflection χ).injective).neg
  · unfold shiftedRealCharacterZeroSum
    simp_rw [he]
    rw [tsum_neg]
    congr 1
    exact (realZeroIndexReflection χ).tsum_eq
      (fun i => ((s - (realCharacterActualZeros χ).zeros i)⁻¹).re)

/-- The shifted identity supplies the actual zero terms used in the
low-height zero-free-region argument. -/
theorem shifted_real_hadamard_identity (χ : PrimitiveRealCharacter) (s : ℂ)
    (hs : 1 < s.re) (hs2 : s.re ≤ 2) :
    shiftedRealCharacterZeroSum χ s = (logDeriv χ.asComplex.completed s).re +
      (1 / 2) * Real.log χ.modulus := by
  have hp := shifted_completed_partial_real_limit χ s (shifted_real_zero_summable χ s hs hs2)
  obtain ⟨hn, heq⟩ := shifted_real_zero_reflection χ s hs hs2
  have hm := shifted_completed_partial_real_limit χ (1 - s) hn
  have hc := completed_partial_fraction_difference_tendsto χ.asComplex (1 - s) s
    (χ.asComplex.completed_ne_zero_left _ (by simp; linarith))
    (χ.asComplex.completed_ne_zero_right _ hs.le)
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  have hlim : shiftedRealCharacterZeroSum χ s - shiftedRealCharacterZeroSum χ (1 - s) =
      (logDeriv χ.asComplex.completed s - logDeriv χ.asComplex.completed (1 - s)).re := by
    apply tendsto_nhds_unique (hp.sub hm)
    simpa only [Function.comp_def, Complex.sub_re] using hr
  rw [heq, χ.completed_logDeriv_reflection s hs.le] at hlim
  simp only [Complex.sub_re, Complex.neg_re, Complex.log_re, Complex.norm_natCast] at hlim
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ComplexCharacterHadamard
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual real-part Hadamard identity for complex characters -/

namespace Ostmann

open Complex Filter
open scoped Topology BigOperators ComplexConjugate

noncomputable def characterRealZeroSum (χ : PrimitiveComplexCharacter) (s : ℂ) : ℝ :=
  ∑' i, ((s - (actualCharacterZeros χ).zeros i)⁻¹).re

theorem character_completed_partial_real_limit (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hsum : Summable (fun i => ((s - (actualCharacterZeros χ).zeros i)⁻¹).re)) :
    Tendsto (fun n : ℕ => (completedZeroPartialFraction χ ((n : ℝ) + 1) s).re)
      atTop (𝓝 (characterRealZeroSum χ s)) := by
  let Z := actualCharacterZeros χ
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hh := hsum.hasSum.comp (Z.tendsto_diskIndices.comp hn)
  unfold characterRealZeroSum
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [completedZeroPartialFraction_index_sum χ (faithfulCharacterZeroEquiv χ), Complex.re_sum]
  rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LogarithmicGammaBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic Gamma bound needed in the full-height zero-free region

The positive-strip digamma series gives a concrete logarithmic bound.
-/

namespace Ostmann

open Complex

theorem gammaReal_logarithmic_bound : ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ,
    1 ≤ s.re → s.re ≤ 3 →
      ‖logDeriv Complex.Gammaℝ s‖ ≤ B * Real.log (|s.im| + 2) := by
  obtain ⟨C, hC, hb⟩ := Complex.exists_norm_digamma_div_two_le_log
    (a := 1) (b := 3) (by norm_num)
  let D := |Real.log Real.pi| / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨C + D + 1, by positivity, ?_⟩
  intro s hs hs'
  have hregular : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n hn
    have hh := congrArg Complex.re hn
    simp only [div_ofNat_re, neg_re, natCast_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hlog : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hlogpos : 0 < Real.log (|s.im| + 2) := hlog2.trans_le hlog
  have hDlog : |Real.log Real.pi| ≤ D * Real.log (|s.im| + 2) := by
    have hm := mul_le_mul_of_nonneg_left hlog hD
    dsimp [D] at hm
    rwa [div_mul_cancel₀ _ hlog2.ne'] at hm
  have hpi : ‖Complex.log (Real.pi : ℂ)‖ = |Real.log Real.pi| := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs]
  rw [gammaReal_logDeriv s hregular, norm_div, norm_ofNat]
  have hh := (norm_sub_le (Complex.digamma (s / 2)) (Complex.log (Real.pi : ℂ))).trans
    (add_le_add (hb s hs hs') (le_refl _))
  rw [hpi] at hh
  change ‖Complex.digamma (s / 2) - Complex.log (Real.pi : ℂ)‖ / 2 ≤ _
  nlinarith

theorem characterGamma_logarithmic_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 →
      ‖logDeriv (DirichletCharacter.gammaFactor χ.character) s‖ ≤
        B * Real.log (|s.im| + 2) := by
  obtain ⟨B, hB, hb⟩ := gammaReal_logarithmic_bound
  refine ⟨B, hB, ?_⟩
  intro χ s hs hs'
  by_cases he : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    exact hb s hs.le (by linarith)
  · rw [show DirichletCharacter.gammaFactor χ.character =
        Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    rw [logDeriv_comp (g := fun u : ℂ => u + 1) (x := s)
      (gammaReal_analyticAt_pos (s + 1) (by simp; linarith)).differentiableAt
      (differentiableAt_id.add_const (1 : ℂ))]
    simpa using hb (s + 1) (by simp; linarith) (by simp; linarith)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_CharacterHadamardBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic bounds from the actual character zero sum -/

namespace Ostmann

open Complex

 theorem character_real_zero_sum_nonneg (χ : PrimitiveComplexCharacter) (s : ℂ)
    (hs : 1 < s.re) : 0 ≤ characterRealZeroSum χ s := by
  apply tsum_nonneg
  intro i
  rw [realZeroKernel_complex_sub]
  exact realZeroKernel_nonneg (by linarith [((actualCharacterZeros χ).in_strip i).2])

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LowHeightArchimedean
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Gamma and zeta-pole errors in the low-height rectangle -/

namespace Ostmann

open Complex Set

 theorem gammaReal_logDeriv_rectangle_bound : ∃ C : ℝ, 0 < C ∧
    ∀ z : ℂ, 1 ≤ z.re → z.re ≤ 3 → |z.im| ≤ 2 →
      ‖logDeriv Complex.Gammaℝ z‖ ≤ C := by
  let K : Set ℂ := Icc (1 : ℝ) 3 ×ℂ Icc (-2 : ℝ) 2
  have hc : ContinuousOn (logDeriv Complex.Gammaℝ) K := by
    intro z hz
    have hzpos : 0 < z.re := by have := hz.1.1; linarith
    have ha := gammaReal_analyticAt_pos z hzpos
    exact (ha.deriv.div ha (Complex.Gammaℝ_ne_zero_of_re_pos hzpos)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_Icc.reProdIm isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨|C| + 1, by positivity, ?_⟩
  intro z hz hz' hi
  exact (hC z ⟨⟨hz, hz'⟩, abs_le.mp hi⟩).trans (by linarith [le_abs_self C])

theorem characterGamma_low_height_bound : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveComplexCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 → |s.im| ≤ 2 →
      ‖logDeriv (DirichletCharacter.gammaFactor χ.character) s‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := gammaReal_logDeriv_rectangle_bound
  refine ⟨C, hC, ?_⟩
  intro χ s hs hs' hi
  by_cases he : χ.character.Even
  · rw [show DirichletCharacter.gammaFactor χ.character = Complex.Gammaℝ from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    exact hb s hs.le (by linarith) hi
  · rw [show DirichletCharacter.gammaFactor χ.character =
        Complex.Gammaℝ ∘ (fun u : ℂ => u + 1) from
      funext (fun u => by simp [DirichletCharacter.gammaFactor, he])]
    rw [logDeriv_comp (g := fun u : ℂ => u + 1) (x := s)
      (gammaReal_analyticAt_pos (s + 1) (by simp; linarith)).differentiableAt
      (differentiableAt_id.add_const (1 : ℂ))]
    simpa using hb (s + 1) (by simp; linarith) (by simp; linarith) (by simpa using hi)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_LowHeightZeroBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual zero sums and bounded low-height errors -/

namespace Ostmann

open Complex
open scoped BigOperators

/-- Uniform upper error after replacing the completed logarithmic derivative
by the ordinary one in the actual shifted zero identity. -/
theorem exists_low_height_zero_sum_error : ∃ C : ℝ, 0 < C ∧
    ∀ (χ : PrimitiveRealCharacter) (s : ℂ), 1 < s.re → s.re ≤ 2 → |s.im| ≤ 2 →
      shiftedRealCharacterZeroSum χ s ≤ (logDeriv χ.L s).re +
        (1 / 2) * Real.log χ.modulus + C := by
  obtain ⟨C, hC, hb⟩ := characterGamma_low_height_bound
  refine ⟨C, hC, ?_⟩
  intro χ s hs hs2 hi
  rw [shifted_real_hadamard_identity χ s hs hs2,
    χ.asComplex.completed_logDeriv_eq_add s hs.le, PrimitiveRealCharacter.asComplex_L,
    Complex.add_re]
  have hh := (Complex.re_le_norm _).trans (hb χ.asComplex s hs hs2 hi)
  linarith

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_ImprimitiveEulerBound
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite Euler-factor cost of changing a character's level -/

namespace Ostmann

open Complex Filter
open scoped BigOperators Topology

noncomputable def imprimitiveEulerFactor {q : ℕ} (χ : DirichletCharacter ℂ q)
    (p : ℕ) (s : ℂ) : ℂ := 1 - χ p * (p : ℂ) ^ (-s)

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.Ostmann_ZeroDensity_FullHeightRegionComparison
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Comparing the conductor-height cutoffs with the published Page cutoff -/

namespace Ostmann

noncomputable def PrimitiveRealZero.asRealCharacter (e : PrimitiveRealZero) : PrimitiveRealCharacter where
  modulus := e.modulus
  positive := e.positive
  character := e.character
  primitive := e.primitive
  nontrivial := e.nontrivial

@[simp] theorem actualRealZero_asCharacter (χ : PrimitiveRealCharacter) (i : ℕ)
    (hi : ((realCharacterActualZeros χ).zeros i).im = 0) :
    ((actualRealCharacterZeroExpansion χ).realZero i hi).asRealCharacter = χ := rfl

end Ostmann

end OAI
end

section
-- module Solutions.OAIQ095_OS.PrimeGaps_EqualityPatterns
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

noncomputable instance finiteSetoidFintype (ι : Type*) [Fintype ι] : Fintype (Setoid ι) :=
  Fintype.ofInjective (fun r : Setoid ι => r.r) (fun _ _ h => Setoid.ext (by intro i j; exact Iff.of_eq (congrFun (congrFun h i) j)))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ095_OS.PrimeGaps_PatternMoments
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

@[simp] theorem append_ker_left {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.castAdd p) (Setoid.ker (Fin.append b c))=Setoid.ker b := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.castAdd p)=Fin.append b c (j.castAdd p) ↔ b i=b j
  simp only [Fin.append_left]

@[simp] theorem append_ker_right {n p : ℕ} {α : Type*}
    (b : Fin n → α) (c : Fin p → α) :
    Setoid.comap (Fin.natAdd n) (Setoid.ker (Fin.append b c))=Setoid.ker c := by
  apply Setoid.ext
  intro i j
  change Fin.append b c (i.natAdd n)=Fin.append b c (j.natAdd n) ↔ c i=c j
  simp only [Fin.append_right]

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ095_OS.PrimeGaps_DirichletGrowth
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

open Complex Filter Topology

open Complex Filter Topology Set MeasureTheory Asymptotics

noncomputable def discrepancyTail (A : ℝ → ℂ) (u : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi u, A t * (t:ℂ)^(-(s+1))

open Finset

noncomputable def seriesDiscrepancy (f : ℕ → ℂ) (c : ℂ) (t : ℝ) : ℂ :=
  (∑ n ∈ Icc 1 ⌊t⌋₊, f n) - c*t

noncomputable def regularSeries (f : ℕ → ℂ) (c : ℂ) (s : ℂ) : ℂ :=
  c+s*discrepancyTail (seriesDiscrepancy f c) 1 s

def positiveCoefficients (f : ℕ → ℂ) (n : ℕ) : ℂ := if n = 0 then 0 else f n

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ095_OS.PrimeGaps_TaylorBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

open Asymptotics

open Asymptotics

open Asymptotics

open scoped Classical

open scoped ContDiff

open Topology

open scoped Convolution ContDiff Pointwise

open scoped ComplexConjugate

open Filter Topology

open Complex Filter Topology

open Complex Filter Topology Set MeasureTheory Asymptotics

open Finset

open Complex Filter Topology Finset

noncomputable def signedTaylorCoeff (H : ℂ → ℂ) (n : ℕ) : ℝ :=
  (((-1:ℂ)^n)*(n.factorial:ℂ)⁻¹*iteratedDeriv n H 2).re

open Complex Filter Topology Finset Set MeasureTheory

noncomputable def zetaRegular : ℂ → ℂ :=
  regularSeries (positiveCoefficients (fun _ => 1)) 1

noncomputable def regularizedZetaProduct (P : ℂ → ℂ) (s : ℂ) : ℂ :=
  zetaRegular s*P s+dslope P 1 s

open Complex Finset ArithmeticFunction

open scoped ComplexOrder

def PrimePowerEq (p : ℕ) (f g : ArithmeticFunction ℂ) : Prop :=
  ∀ k : ℕ, f (p^k) = g (p^k)

noncomputable def biquadraticCoefficients {q r : ℕ}
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r) : ArithmeticFunction ℂ :=
  ArithmeticFunction.zeta * toArithmeticFunction (χ ·) * toArithmeticFunction (ψ ·) *
    (toArithmeticFunction (χ ·)).pmul (toArithmeticFunction (ψ ·))

end LargePrimeGaps

end OAI
end

section
-- module Solutions.OAIQ095_OS.PrimeGaps_SiegelBounds
attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LargePrimeGaps

section

open Complex Finset ArithmeticFunction

noncomputable def productCharacter {q r : ℕ} (χ : DirichletCharacter ℂ q)
    (ψ : DirichletCharacter ℂ r) : DirichletCharacter ℂ (q*r) :=
  χ.changeLevel (dvd_mul_right q r) * ψ.changeLevel (dvd_mul_left r q)

end

open Complex Filter Topology Set MeasureTheory Finset ArithmeticFunction

end LargePrimeGaps

end OAI
end


