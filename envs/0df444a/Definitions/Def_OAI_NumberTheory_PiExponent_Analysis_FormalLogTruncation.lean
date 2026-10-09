-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation
-- name    : OAI_NumberTheory_PiExponent_Analysis_FormalLogTruncation
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-09T05:14:25.104758+00:00
-- url     : https://prove2.me/theorems/3eb1ecf4-c3d2-4bf7-bd1d-4634d53984f4
-- title:
--   Truncated formal logarithmic jets and weighted substitutions
-- statement:
--   Let R be a commutative ring and let m be a natural number. Given power series tail_i with zero constant coefficient, the declarations define the substitution of the multivariate power-series variables by X_0 and X_{i+1} + tail_i, together with its induced R-algebra endomorphism. They give the action of this map on the generators and on univariate series in X_0, prove that tails s and t with s_i + t_i = 0 induce inverse maps, and package the resulting algebra equivalence. For nonnegative rational weights, they establish finite-product closure for rational weighted ideals, preservation of weighted-ideal membership under substitutions whose variable images meet the corresponding weight bounds, membership of each coordinate variable at its own weight, and preservation under the stated shift-map bounds. Equality of the coefficient packets below a rational threshold is equivalent to the difference of the two series belonging to the corresponding rational weighted ideal. Over ℂ, logTail T is the formal logarithm minus its truncation at T; its constant coefficient and all coefficients of degree less than T vanish. The map truncatedFormalJet sends X_0 to 1 + X_0 and each remaining frame variable to c_i + X_{i+1} plus the lifted truncation of the formal logarithm at T_i.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/FormalLogTruncation.lean#L45-L306

import Definitions.Def_OAI_NumberTheory_PiExponent_Jets_FormalLogJet
import Definitions.Def_OAI_NumberTheory_PiExponent_Jets_JetGeometry
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

namespace PiExponent.FormalLogTruncation

open MvPowerSeries
open scoped BigOperators

variable {R : Type*} [CommRing R]



noncomputable def shiftVars {m : ℕ} (tail : Fin m → PowerSeries R) :
    Fin (m+1) → MvPowerSeries (Fin (m+1)) R :=
  Fin.cases (X 0) (fun i => X i.succ + (tail i).toMvPowerSeries 0)

theorem shiftVars_hasSubst {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) : HasSubst (shiftVars tail) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  cases i using Fin.cases with
  | zero => simp [shiftVars]
  | succ i =>
      simp only [shiftVars, Fin.cases_succ, map_add, constantCoeff_X,
        PowerSeries.toMvPowerSeries_apply, constantCoeff_rename, zero_add]
      exact ht i

noncomputable def shiftMap {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) :
    MvPowerSeries (Fin (m+1)) R →ₐ[R] MvPowerSeries (Fin (m+1)) R :=
  substAlgHom (shiftVars_hasSubst tail ht)

@[simp] theorem shiftMap_X_zero {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) :
    shiftMap tail ht (X 0) = X 0 := by
  rw [shiftMap, substAlgHom_X]
  rfl

@[simp] theorem shiftMap_X_succ {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (i : Fin m) :
    shiftMap tail ht (X i.succ) = X i.succ + (tail i).toMvPowerSeries 0 := by
  rw [shiftMap, substAlgHom_X]
  rfl

@[simp] theorem shiftMap_toMvPowerSeries {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f : PowerSeries R) :
    shiftMap tail ht (f.toMvPowerSeries (0 : Fin (m+1))) = f.toMvPowerSeries 0 := by
  rw [shiftMap, substAlgHom_apply, PowerSeries.subst_toMvPowerSeries (shiftVars_hasSubst tail ht)]
  change PowerSeries.subst (X (0 : Fin (m+1))) f = f.toMvPowerSeries 0
  exact PowerSeries.toMvPowerSeries_eq_subst.symm



@[simp] theorem shiftMap_apply {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f) :
    shiftMap tail ht f = subst (shiftVars tail) f := substAlgHom_apply _ _

theorem shiftMap_inverse {m : ℕ} (s t : Fin m → PowerSeries R)
    (hs : ∀ i, PowerSeries.constantCoeff (s i) = 0)
    (ht : ∀ i, PowerSeries.constantCoeff (t i) = 0)
    (hst : ∀ i, s i + t i = 0) (f : MvPowerSeries (Fin (m+1)) R) :
    shiftMap s hs (shiftMap t ht f) = f := by
  simp only [shiftMap_apply]
  rw [subst_comp_subst_apply (shiftVars_hasSubst t ht) (shiftVars_hasSubst s hs)]
  have hvars : (fun i => subst (shiftVars s) (shiftVars t i)) = X := by
    funext i
    rw [← shiftMap_apply s hs]
    cases i using Fin.cases with
    | zero => exact shiftMap_X_zero s hs
    | succ i =>
      change shiftMap s hs (X i.succ + (t i).toMvPowerSeries 0) = X i.succ
      rw [map_add, shiftMap_X_succ, shiftMap_toMvPowerSeries, add_assoc,
        ← map_add, hst i, map_zero, add_zero]
  rw [hvars]
  exact congrFun subst_self f

noncomputable def shiftEquiv {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) :
    MvPowerSeries (Fin (m+1)) R ≃ₐ[R] MvPowerSeries (Fin (m+1)) R := by
  let hn : ∀ i, PowerSeries.constantCoeff (-tail i) = 0 := by simp [ht]
  refine AlgEquiv.ofAlgHom (shiftMap tail ht) (shiftMap (fun i => -tail i) hn) ?_ ?_
  · apply AlgHom.ext
    intro f
    exact shiftMap_inverse tail (fun i => -tail i) ht hn (fun i => add_neg_cancel _) f
  · apply AlgHom.ext
    intro f
    exact shiftMap_inverse (fun i => -tail i) tail hn ht (fun i => neg_add_cancel _) f



open JetGeometry

theorem rationalWeightedIdeal_prod {σ ι : Type*} (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (s : Finset ι) (f : ι → MvPowerSeries σ R) (c : ι → ℚ)
    (hf : ∀ i ∈ s, f i ∈ rationalWeightedIdeal v hv (c i)) :
    ∏ i ∈ s, f i ∈ rationalWeightedIdeal v hv (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro d hd
    simp only [Finset.sum_empty] at hd
    exact False.elim ((not_lt_of_ge (rational_weight_nonneg v hv d)) hd)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact Ideal.mul_le.mp (rationalWeightedIdeal_mul_le v hv (c i) (∑j∈s,c j))
      _ (hf i (Finset.mem_insert_self _ _)) _
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem subst_mem_rationalWeightedIdeal {σ τ : Type*}
    (w : σ → ℚ) (v : τ → ℚ) (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (a : σ → MvPowerSeries τ R) (ha : HasSubst a)
    (hweight : ∀ i, a i ∈ rationalWeightedIdeal v hv (w i))
    (H : ℚ) (f : MvPowerSeries σ R) (hf : f ∈ rationalWeightedIdeal w hw H) :
    subst a f ∈ rationalWeightedIdeal v hv H := by
  classical
  intro d hd
  rw [coeff_subst ha]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : coeff e f = 0
  · rw [he, zero_smul]
  have hHe : H ≤ Finsupp.weight w e := le_of_not_gt (fun h => he (hf e h))
  have hprod : e.prod (fun i n => a i ^ n) ∈
      rationalWeightedIdeal v hv (Finsupp.weight w e) := by
    rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
    apply rationalWeightedIdeal_prod
    intro i hi
    have hp := Ideal.pow_mem_pow (hweight i) (e i)
    have hh := ideal_pow_le_rationalWeightedIdeal v hv
      (rationalWeightedIdeal v hv (w i)) (w i) le_rfl (e i) hp
    simpa only [nsmul_eq_mul] using hh
  rw [hprod d (hd.trans_le hHe), smul_zero]

theorem X_mem_rationalWeightedIdeal {σ : Type*} (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (i : σ) : (X i : MvPowerSeries σ R) ∈ rationalWeightedIdeal v hv (v i) := by
  classical
  intro d hd
  rw [coeff_X]
  split_ifs with he
  · subst d
    simp only [Finsupp.weight_single, one_nsmul] at hd
    exact False.elim (lt_irrefl _ hd)
  · rfl

theorem shiftMap_mem_rationalWeightedIdeal {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hweight : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ)) (H : ℚ)
    (f : MvPowerSeries (Fin (m+1)) R) (hf : f ∈ rationalWeightedIdeal v hv H) :
    shiftMap tail ht f ∈ rationalWeightedIdeal v hv H := by
  rw [shiftMap_apply]
  apply subst_mem_rationalWeightedIdeal v v hv hv _ (shiftVars_hasSubst tail ht) _ H f hf
  intro i
  cases i using Fin.cases with
  | zero => exact X_mem_rationalWeightedIdeal v hv 0
  | succ i => exact Ideal.add_mem _ (X_mem_rationalWeightedIdeal v hv i.succ) (hweight i)

theorem rationalCoefficientPacket_eq_iff {σ : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ) (f g : MvPowerSeries σ R) :
    rationalCoefficientPacket v H f = rationalCoefficientPacket v H g ↔
      f - g ∈ rationalWeightedIdeal v hv H := by
  constructor
  · intro h d hd
    exact sub_eq_zero.mpr (congrFun h ⟨d,hd⟩)
  · intro h
    funext d
    exact sub_eq_zero.mp (h d.val d.property)











noncomputable def logTail (T : ℕ) : PowerSeries ℂ :=
  PowerSeries.log ℂ - (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ)

@[simp] theorem logTail_constantCoeff (T : ℕ) : PowerSeries.constantCoeff (logTail T) = 0 := by
  simp [logTail, Polynomial.constantCoeff_coe, PowerSeries.coeff_trunc,
    PowerSeries.coeff_log]

theorem coeff_logTail_eq_zero (T n : ℕ) (hn : n < T) :
    PowerSeries.coeff n (logTail T) = 0 := by
  simp [logTail, Polynomial.coeff_coe, PowerSeries.coeff_trunc, hn]



noncomputable def truncatedFormalJet {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + X 0) (fun i =>
    C (c i) + X i.succ + FormalLogJet.liftSeries m
      (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ)))









end PiExponent.FormalLogTruncation

end OAI


