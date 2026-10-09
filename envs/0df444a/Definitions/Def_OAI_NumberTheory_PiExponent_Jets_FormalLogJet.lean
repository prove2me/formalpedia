-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Jets_FormalLogJet
-- name    : OAI_NumberTheory_PiExponent_Jets_FormalLogJet
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T14:37:57.816046+00:00
-- url     : https://prove2.me/theorems/1c1891c5-a421-41c2-ae74-60eb1cde1271
-- title:
--   Formal logarithmic jet substitution for polynomial frames
-- statement:
--   For a commutative ring R, liftSeries embeds univariate power series into multivariate power series in m + 1 variables through the power-series map to constants and the finSucc equivalence; it sends constants to the corresponding multivariate constants. formalLog m is the lift of the complex formal power-series logarithm. For c : Fin m → ℂ, formalJet c is the ℂ-algebra homomorphism from FramePolynomial m to multivariate complex power series that sends X₀ to 1 + X₀ and sends Xᵢ₊₁ to C(c i) + Xᵢ₊₁ + formalLog m. The bundle proves these generator formulas and a general result that an algebra homomorphism intertwines two derivations on every polynomial when they agree on all polynomial variables.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/FormalLogJet.lean#L14-L98

import Definitions.Def_OAI_NumberTheory_PiExponent_Jets_FormalJetDerivatives
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrame
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Regular.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.AlgebraicGeometry.Artinian
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Rat
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.DirectSum.Finite
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Order.Minimal
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Noetherian.Nilpotent
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Trace.Defs
import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas



namespace OAI

noncomputable section
namespace PiExponent.FormalLogJet
open MvPowerSeries
open PiExponent.FormalJetDerivatives

variable {R : Type*} [CommRing R]

def liftSeries (m : ℕ) : PowerSeries R →+* MvPowerSeries (Fin (m + 1)) R :=
  (finSuccEquiv R m).symm.toRingHom.comp (PowerSeries.map MvPowerSeries.C)

@[simp] theorem coeff_liftSeries (m : ℕ) (f : PowerSeries R)
    (d : Fin (m + 1) →₀ ℕ) :
    coeff d (liftSeries m f) = if d.tail = 0 then PowerSeries.coeff (d 0) f else 0 := by
  have h := coeff_coeff_finSuccEquiv (liftSeries m f) (k := d 0) (x := d.tail)
  rw [Finsupp.cons_tail] at h
  rw [← h]
  simp [liftSeries, PowerSeries.coeff_map, coeff_C]

@[simp] theorem liftSeries_X (m : ℕ) : liftSeries (R := R) m PowerSeries.X = X 0 := by
  apply (finSuccEquiv R m).injective
  simp [liftSeries]

@[simp] theorem liftSeries_C (m : ℕ) (r : R) :
    liftSeries m (PowerSeries.C r) = C r := by
  apply (finSuccEquiv R m).injective
  simp [liftSeries]





def formalLog (m : ℕ) : MvPowerSeries (Fin (m+1)) ℂ :=
  liftSeries m (PowerSeries.log ℂ)







def formalJet {m : ℕ} (c : Fin m → ℂ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + X 0)
    (fun i => C (c i) + X i.succ + formalLog m))

@[simp] theorem formalJet_Y {m : ℕ} (c : Fin m → ℂ) :
    formalJet c (MvPolynomial.X (0 : Fin (m+1))) = 1 + X 0 := by
  simp [formalJet]

@[simp] theorem formalJet_X {m : ℕ} (c : Fin m → ℂ) (i : Fin m) :
    formalJet c (MvPolynomial.X i.succ) = C (c i) + X i.succ + formalLog m := by
  simp [formalJet]

theorem derivation_map_of_X {σ S : Type*} [CommRing S] [Algebra R S]
    (φ : MvPolynomial σ R →ₐ[R] S)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (δ : Derivation R S S)
    (hX : ∀ i, φ (D (MvPolynomial.X i)) = δ (φ (MvPolynomial.X i)))
    (p : MvPolynomial σ R) : φ (D p) = δ (φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hX]









end PiExponent.FormalLogJet

end

end OAI


