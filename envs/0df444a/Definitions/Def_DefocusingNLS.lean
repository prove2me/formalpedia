-- Prove2me | Definitions.Def_DefocusingNLS
-- name    : DefocusingNLS
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:07.015482+00:00
-- url     : https://prove2.me/theorems/7b94600d-0248-466a-86a2-5d3f97ccd666
-- statement:
--   The frequency lattice is the integer span of the standard basis of twelve-dimensional real Euclidean space, identified with ℤ¹²; it is equipped with its discrete topology and lattice structure. For v ≥ 0, complexGaussian(v) is the probability distribution of X + iY, where X and Y are independent centered real Gaussians of variance v. The Fourier Gaussian law makes these complex variables independent over all lattice frequencies, with v = 1/2. FourierL2 is the complex ℓ² space on this lattice, with its Borel measurable structure. For real k and α, the Sobolev variance at frequency n is (1 + ‖n‖²)^(k − α). Multiplying each Gaussian coefficient by the square root of this variance and summing its single-coordinate ℓ² vectors defines the weighted Gaussian vector; the weighted Gaussian law is the pushforward of the Fourier Gaussian law under this map. A vector f in FourierL2 represents Sobolev Fourier coefficients aₙ = (1 + ‖n‖²)^(−k/2)f(n). On the torus (ℝ/2πℤ)¹², the character of n is the product of the one-dimensional Fourier characters with its integer coordinates, and the associated torus function is the sum of aₙ times these characters in the space of continuous complex-valued functions. These infinite-sum definitions impose no convergence hypotheses and use the formal convention that a nonsummable series has sum zero. Finally, the Sobolev product weight is (1 + ‖n‖²)^(k/2), while the product coefficient is the unweighted convolution ∑ₘ aₘbₙ₋ₘ of the Sobolev Fourier coefficients of two vectors.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DefocusingNLS.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DefocusingNLS.lean; bytes 16..3920
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! # Stable self-similar blowup on the twelve-dimensional torus

Theorem 1.1 and Corollary 1.2 of OpenAI, *Stable self-similar blowup for a
supercritical defocusing Schrödinger equation on the torus* (September 2026).
The Sobolev space is represented by its weighted square-summable Fourier
coefficients. The maximal flow is the union of classical interaction solutions.
-/

noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ComplexConjugate ContDiff

attribute [local instance 2000] instPolynormableSpace
  TopologicalSpace.PseudoMetrizableSpace.regularSpace

namespace DefocusingNLS

noncomputable def frequencyLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 12)) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 12) ℝ).toBasis)

instance : DiscreteTopology frequencyLattice := by
  unfold frequencyLattice
  infer_instance

instance : IsZLattice ℝ frequencyLattice := by
  unfold frequencyLattice
  infer_instance


noncomputable def complexGaussian (v : ℝ≥0) : Measure ℂ :=
  ((gaussianReal 0 v).prod (gaussianReal 0 v)).map
    Complex.equivRealProdCLM.symm

instance complexGaussian_isProbabilityMeasure (v : ℝ≥0) :
    IsProbabilityMeasure (complexGaussian v) := by
  unfold complexGaussian
  infer_instance


noncomputable def fourierGaussianLaw : Measure (frequencyLattice → ℂ) :=
  Measure.infinitePi (fun _ : frequencyLattice => complexGaussian (1 / 2))

noncomputable def sobolevVariance (k α : ℝ) (n : frequencyLattice) : ℝ :=
  (1 + ‖n‖ ^ 2) ^ (k - α)

noncomputable def weightedGaussianCoefficient (k α : ℝ)
    (g : frequencyLattice → ℂ) (n : frequencyLattice) : ℂ :=
  Real.sqrt (sobolevVariance k α n) • g n


abbrev FourierL2 := lp (fun _ : frequencyLattice => ℂ) (2 : ℝ≥0∞)

instance : MeasurableSpace FourierL2 := borel FourierL2
instance : BorelSpace FourierL2 := ⟨rfl⟩

noncomputable def weightedGaussianVector (k α : ℝ)
    (g : frequencyLattice → ℂ) : FourierL2 :=
  ∑' n, lp.single 2 n (weightedGaussianCoefficient k α g n)

noncomputable def sobolevFourierCoefficient (k : ℝ) (f : FourierL2)
    (n : frequencyLattice) : ℂ :=
  (1 + ‖n‖ ^ 2) ^ (-k / 2) • f n

noncomputable def weightedGaussianLaw (k α : ℝ) : Measure FourierL2 :=
  fourierGaussianLaw.map (weightedGaussianVector k α)


abbrev SchrodingerTorus := Fin 12 → AddCircle (2 * Real.pi)

instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

noncomputable def frequencyCoordinates (n : frequencyLattice) : Fin 12 → ℤ :=
  ((EuclideanSpace.basisFun (Fin 12) ℝ).toBasis.restrictScalars ℤ).repr n

noncomputable def torusCharacter (n : frequencyLattice) : C(SchrodingerTorus, ℂ) where
  toFun x := ∏ j : Fin 12, fourier (frequencyCoordinates n j) (x j)
  continuous_toFun := by fun_prop

noncomputable def sobolevTorusTerm (k : ℝ) (f : FourierL2) (n : frequencyLattice) :
    C(SchrodingerTorus, ℂ) :=
  sobolevFourierCoefficient k f n • torusCharacter n

noncomputable def sobolevTorusFunction (k : ℝ) (f : FourierL2) : C(SchrodingerTorus, ℂ) :=
  ∑' n, sobolevTorusTerm k f n


noncomputable def sobolevProductWeight (k : ℝ) (n : frequencyLattice) : ℝ :=
  (1 + ‖n‖ ^ 2) ^ (k / 2)


noncomputable def sobolevProductCoefficient (k : ℝ) (f g : FourierL2)
    (n : frequencyLattice) : ℂ :=
  ∑' m, sobolevFourierCoefficient k f m * sobolevFourierCoefficient k g (n - m)



end DefocusingNLS
end
end OAI


