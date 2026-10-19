-- Prove2me | Definitions.Def_MIPRE_Background_QLD_PaddedLIDT
-- name    : MIPRE_Background_QLD_PaddedLIDT
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T08:51:30.353982+00:00
-- url     : https://prove2.me/theorems/abe40ad2-2129-4993-a5a8-ebbdac6200f9
-- title:
--   Definitions of PaddedLIDT: The global polynomial measurements: applying the seeded soundness theorem `lem:qld-global-pvm`
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.PaddedLIDT` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The global polynomial measurements: applying the seeded soundness theorem. `lem:qld-global-pvm`. By `lem:qld-global-success` (`padStrat_value`), the padded strategy `(extHat ψ, padStrat hprojA, padStrat hprojB)` wins the seeded low individual degree test at `(q, 4m, d, 1)` with probability at least `1 - δ_GS`, where `δ_GS = 5 m² δ_P(ε, md/q + 1/q) + 4 δ_Q(ε) + (md + 1)/q`. This file feeds it to `clSoundness_ldc_one_deltaCL_of_povm`, the seeded soundness theorem for POVM strategies, and reads the conclusion back in the form stages 4b and 4c consume. It is the one module of the Pauli basis…
--
--   **Definitions** (14): `MIPRE.QLD.GlobalPair` (**The output of `lem:qld-global-pvm`, as a structure**: the two projective low-degree measurements on the dilated registers, the two point…); `MIPRE.QLD.GlobalPair.toSimulPair` (**`lem:qld-simultaneous`**: the completed pair measurements of a `GlobalPair`, carried to the register shape of `SimulPair` by the…); `MIPRE.QLD.PadReg` (A party's register after the projective dilation of the padded strategy: the expanded register, the combining ancilla `F × F`, and the…); `MIPRE.QLD.ansZero` (The zero answer to the seeded test at `(q, 4m, d, 1)`: the ancilla vector of the projective dilation.); `MIPRE.QLD.deltaGS` (**`δ_GS`**, the error of `lem:qld-global-success`: the padded strategy's failure probability in the seeded test at `(q, 4m, d, 1)`.); `MIPRE.QLD.deltaLD` (**`δ_ld`**: the seeded soundness theorem's error at `(q, 4m, d, 1)` for a strategy of value `1 - δ_GS`.); `MIPRE.QLD.deltaProd` (**`Δ`**, the ordered-products bound of `lem:qld-global-products` for a `GlobalPair` of error `δ` on a strategy of failure `ε`: `2 δ + 2 κ`…); `MIPRE.QLD.deltaS` (**`δ_S`**, the error of `lem:qld-simultaneous`: the marginal estimate `2 √Δ + 2/q + δ_G`.); `MIPRE.QLD.deltaSep` (**`δ_G`**, the weight of the outcomes that are not of the separated form `α g_X(x) + β g_Z(z)`: `8 Δ`, from `lem:qld-global-separate` under…); `MIPRE.QLD.instDecidableEqPadReg` (Decidable equality on the dilated register.); `MIPRE.QLD.instFintypePadReg`; and -22 more.
--
--   **Embedded lemmas** (25): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `cons_sandComb_A`, `cons_sandComb_B`, `inconsistency_evalMarg_A_le`, `inconsistency_evalMarg_B_le`, `one_sub_two_eta_ge`, `products_XZ_A`, `products_XZ_B`, `products_ZX_A`, `products_ZX_B`, `sum_not_isGood_mass_A_le`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.PaddedLIDT` (`MIPRE/Background/QLD/PaddedLIDT.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 302 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/PaddedLIDT.lean; blueprint def:qld-physical-model, lem:qld-global-products, lem:qld-global-pvm, lem:qld-global-robustness, lem:qld-global-separate, lem:qld-simultaneous

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/PaddedLIDT.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Lean.Elab.Tactic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Module.Torsion.Pi
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Indicator
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Notation.Prod
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Real.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Embedding
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Quot
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SProd
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Restrict
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.ULift
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Pairwise
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.OuterMeasure.Defs
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Order.Basic
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Extr
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Trace.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.GDelta
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.UnitInterval
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Coefficients_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Parameters
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Weights
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Field
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Polynomial
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Measurement
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Strategy
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_DirectSum
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProj_Measurements
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Value
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_ProjectorONB
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Completion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_ProjectivizationChain_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_SourceScalars
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceCommutation_Averages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_EvaluationSpecialization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Bridges_Closeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Bridges_QSDD
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_ZeroBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_BridgeTheorems_DropBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooCompletion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_CommutingWithG_Complete
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_GHatFacts
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_StepLemmas_Split
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_TruncatedSums
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Weights
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_BernoulliTail
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_Core_FactBundles
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_MoveLemmas_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_StageA0M1
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_HalfSandwich
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_AdjacentStages_Chain_FinalMove
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_FromHToG_PaperBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_MatrixChernoff
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LineInterpolation_BadMass
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_HBConsistency
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_HAConsistency
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_DegreeZero
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_ErrorAndMass
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_NonglobalDecomposition
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_OverAllOutcomes_Final
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Final
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_Conversion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_LocalityPreservingRepair
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization_RestrictSome
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Orthonormalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Thresholds_Final
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_InputSdp
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_FiberBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Linearized
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Base
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_CanonicalPrimal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Witness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_Saturated
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteConicDuality
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_MatrixRealization_Canonical_StrongDuality_Separation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SdpMatrixBridge
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_AlgebraicIdentity
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransportSum
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_PolynomialSumBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperCompleteness_Bracketed
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Selection
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_Residual
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUDiagonalAndDefs_ScalarChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Raw
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep12_Selected
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Factored
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Selected
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUStep34AndTransfer_Variance
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_HelperSSC_PostDeleteA
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_AddInUPointConsistency
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_Results_SelfImprovementTop_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_SelfImprovement_Theorems_AddInUFullStatement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_MainError
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_SelfImprovementAssembly_AnswerSlice
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Base
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Axis
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_Diagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_RestrictedProbabilities_AnswerValued
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_StageDataConstructors
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_AvgSliceErrors_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_AnswerTheorems
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_InductionParameterBounds_SelfImprovement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Theorems_PastingAssembly_Successor
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_SchwartzZippelStep
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonProjective
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProjRoleAverage_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyBiProjUnsymmetrization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_SourceRoleRegister_Completion
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Main
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reduction
import Definitions.Def_MIPRE_Background_LIDT_BlockPoly
import Definitions.Def_MIPRE_Foundations_StrategyDilation
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Background_QLD_Win
import Definitions.Def_MIPRE_Background_QLD_Anticomm
import Definitions.Def_MIPRE_Background_QLD_WinMS
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_PhiNorm
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_IsometryData
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Assembly
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_JointDiag
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Blocks
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Main
import Definitions.Def_MIPRE_Background_QLD_Ortho
import Definitions.Def_MIPRE_Background_QLD_Consistency
import Definitions.Def_MIPRE_Background_QLD_Commutation
import Definitions.Def_MIPRE_Background_QLD_Expanded
import Definitions.Def_MIPRE_Background_QLD_Swap
import Definitions.Def_MIPRE_Background_QLD_Combined
import Definitions.Def_MIPRE_Background_QLD_Lines
import Definitions.Def_MIPRE_Foundations_Blocks
import Definitions.Def_MIPRE_Background_QLD_Padded
import Definitions.Def_MIPRE_Background_QLD_Product
import Definitions.Def_MIPRE_Background_QLD_Combine
import Definitions.Def_MIPRE_Background_QLD_Legalize
import Definitions.Def_MIPRE_Background_QLD_PaddedLines
import Definitions.Def_MIPRE_Background_QLD_PaddedStrategy
import Definitions.Def_MIPRE_Background_QLD_Dummy
import Definitions.Def_MIPRE_Background_QLD_Products
import Definitions.Def_MIPRE_Background_QLD_Linear
import Definitions.Def_MIPRE_Background_QLD_Separate
import Definitions.Def_MIPRE_Background_QLD_Simul
import Definitions.Def_MIPRE_Background_QLD_Complete
import Definitions.Def_MIPRE_Background_QLD_PaddedValue
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Registers
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_POVM_aOp_aOp_reindex
import Theorems.Thm_MIPRE_POVM_map_reindex
import Theorems.Thm_MIPRE_QLD_bornProb_extVec2_aOp_aOp
import Theorems.Thm_MIPRE_QLD_hatVec_unit
import Theorems.Thm_MIPRE_QLD_inconsistency_evalMarg_X_le
import Theorems.Thm_MIPRE_QLD_inconsistency_evalMarg_Z_le
import Theorems.Thm_MIPRE_QLD_inconsistency_evalPOVM_eq
import Theorems.Thm_MIPRE_QLD_isPVM_hatMats
import Theorems.Thm_MIPRE_QLD_isPVM_pairMeas
import Theorems.Thm_MIPRE_QLD_padPt_mats
import Theorems.Thm_MIPRE_QLD_sum_content_blocks
import Theorems.Thm_MIPRE_QLD_sum_content_hatComm_le
import Theorems.Thm_MIPRE_QLD_sum_content_hatComm_le_B
import Theorems.Thm_MIPRE_QLD_sum_not_isGood_mass_le
import Theorems.Thm_MIPRE_QLD_sum_snorm_sq_ordXZ_le
import Theorems.Thm_MIPRE_QLD_sum_snorm_sq_ordZX_le
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_bornProb_reindex
import Theorems.Thm_MIPRE_bornProb_swapVec
import Theorems.Thm_MIPRE_extVec2_unit
import Theorems.Thm_MIPRE_inconsistency_reindex
import Theorems.Thm_MIPRE_inconsistency_swapVec
import Theorems.Thm_MIPRE_isPVM_reindex_povm
import Theorems.Thm_MIPRE_normSq_stateVecB_extVec2_aOp
import Theorems.Thm_MIPRE_norm_stateVecB
import Theorems.Thm_MIPRE_posSemidef_of_proj
import Theorems.Thm_MIPRE_reindex_aOp_aOp
import Theorems.Thm_MIPRE_stateSqNorm_extVec2_aOp
import Theorems.Thm_MIPRE_sum_uniform_eq_one
import Theorems.Thm_MIPRE_swapVec_dotProduct

/-!
# The global polynomial measurements: applying the seeded soundness theorem

`lem:qld-global-pvm`. By `lem:qld-global-success` (`padStrat_value`), the padded strategy
`(extHat ψ, padStrat hprojA, padStrat hprojB)` wins the seeded low individual degree test at
`(q, 4m, d, 1)` with probability at least `1 - δ_GS`, where
`δ_GS = 5 m² δ_P(ε, md/q + 1/q) + 4 δ_Q(ε) + (md + 1)/q`. This file feeds it to
`clSoundness_ldc_one_deltaCL_of_povm`, the seeded soundness theorem for POVM strategies, and reads
the conclusion back in the form stages 4b and 4c consume. It is the one module of the Pauli basis
test's analysis that reaches the vendored MIPStarRE tree.

## What the theorem returns

The soundness theorem dilates the padded strategy projectively (`lem:naimark-dilation`), which
adjoins to each party one more ancilla, indexed by the test's answers and prepared in the zero
answer `ansZero`. The two low-degree measurements `GA`, `GB` it produces are projective on the
dilated registers `PadReg`, and its three consistency estimates hold on the twice-padded state
`padState ψ = extVec2 (extHat ψ) ansZero ansZero`, against the dilation's own point measurements.
Those compress to the padded strategy's (`padStrat_point_map_toValue`), whose operators are the
expanded sandwich combinations `ptComb (sand M̂^X M̂^Z) α β`, extended by the identity
(`padPt_mats`).

## Why no further dilation is needed

On a product state `extVec2 Ψ a₀ b₀` the Born probability of `X ⊗ E` depends on `E` only through
its compression by `|b₀⟩` (`bornProb_extVec2_ancCompress`). The dilation's point measurement and
the padded strategy's own point measurement extended by the identity on the answer ancilla have
the same compression, so every consistency estimate against the former is the same number against
the latter (`inconsistency_padState_aOp_right`). The final form, `exists_global_pvm_hat`,
therefore mentions no dilation: it is a pair of projective measurements `GA`, `GB` on the two
`PadReg` registers whose evaluated marginals are consistent, on `padState ψ`, with the *original*
strategy's expanded sandwich combinations, doubly extended; and every expectation of a doubly
extended operator on `padState ψ` is its expectation on `hatVec ψ`
(`bornProb_padState_aOp_aOp`), so the conclusions of stages 2 and 3 transfer.

## The error

`δ_ld = deltaLD q m d ε = deltaCL q (4m) d (deltaGS q m d ε)`: the soundness theorem's error at
`(q, 4m, d, 1)` for a strategy of value `1 - δ_GS`. It is of the blueprint's displayed form
`A (md)^A ((δ_GS)^b + q^{-b} + 2^{-bmd})`, since `(4md)^A = 4^A (md)^A` and
`2^{-4bmd} ≤ 2^{-bmd}`.

The recovered polynomials live on `F^{4m}`, while the point measurements read only the `2m + 2`
coordinates `xBlk`, `zBlk`, `alph`, `bet`. The Schwartz--Zippel argument that the polynomials
mostly do not read the remaining dummy coordinates is `MIPRE/Background/QLD/Dummy.lean`;
`exists_global_pvm_wIndep` is `lem:qld-global-dummy` for the measurements produced here.
-/

noncomputable section

namespace MIPRE

section CompressAOp

variable {A d E : Type*} [Fintype A] [Fintype d] [DecidableEq d] [Fintype E] [DecidableEq E]

end CompressAOp

end MIPRE

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LIDT MIPRE.LIDT.Adapter
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m]

/-- The zero answer to the seeded test at `(q, 4m, d, 1)`: the ancilla vector of the projective
dilation. -/
def ansZero : CL.Answer F (4 * m) d 1 := CL.Answer.values fun _ => 0

/-- A party's register after the projective dilation of the padded strategy: the expanded
register, the combining ancilla `F × F`, and the answer ancilla. -/
abbrev PadReg (F : Type*) (m d : ℕ) (dA : Type) :=
  ((dA × Anc F m) × (F × F)) × CL.Answer F (4 * m) d 1

variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- Decidable equality on the dilated register. The default synthesis size limit misses it on
the five-fold product, so the two halves are assembled by hand. -/
instance instDecidableEqPadReg : DecidableEq (PadReg F m d dA) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

instance instFintypePadReg : Fintype (PadReg F m d dA) := instFintypeProd _ _

/-- **The twice-padded state**: the expanded state with the combining ancillas in `|0, 0⟩` and the
answer ancillas in `|ansZero⟩`. -/
def padState (ψ : dA × dB → ℂ) : PadReg F m d dA × PadReg F m d dB → ℂ :=
  extVec2 (extHat (F := F) (m := m) ψ) ansZero ansZero

theorem padState_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (padState (F := F) (m := m) (d := d) ψ) ⬝ᵥ padState (F := F) (m := m) (d := d) ψ = 1 :=
  extVec2_unit (extVec2_unit (hatVec_unit hψ) _ _) _ _

omit [Algebra (ZMod 2) F] [NeZero m] in
/-- **Doubly extended operators have on the twice-padded state the expectation they have on the
expanded state**: the conclusions of stages 2 and 3 transfer to `padState ψ`. -/
theorem bornProb_padState_aOp_aOp (ψ : dA × dB → ℂ) (X : Matrix (dA × Anc F m) (dA × Anc F m) ℂ)
    (Y : Matrix (dB × Anc F m) (dB × Anc F m) ℂ) :
    bornProb (padState (F := F) (m := m) (d := d) ψ) (aOp (aOp X)) (aOp (aOp Y))
      = bornProb (hatVec (F := F) (m := m) ψ) X Y := by
  rw [padState, bornProb_extVec2_aOp_aOp, extHat, bornProb_extVec2_aOp_aOp]

/-- The padded point measurement, extended to the dilated register: the expanded sandwich
combination, doubly extended. -/
theorem padPt_aOp_mats {M : Question F m → POVM (Answer F m d) dA}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (u : Point F (4 * m)) (a : F) :
    ((((padPt hM u).aOp (E := CL.Answer F (4 * m) d 1)).mats a).val)
      = aOp (aOp (ptComb (sand (hatMats M .X (xBlk u)) (hatMats M .Z (zBlk u))) (alph u) (bet u)
          a)) := by
  rw [POVM.aOp_mats, padPt_mats]

/-! ## Replacing the dilation's measurements by their compressions' extensions -/

section Replace

variable {X : Type*} [Fintype X]

end Replace

/-! ## The errors -/

/-- **`δ_GS`**, the error of `lem:qld-global-success`: the padded strategy's failure probability
in the seeded test at `(q, 4m, d, 1)`. -/
def deltaGS (q m d : ℕ) (ε : ℝ) : ℝ :=
  5 * ((m : ℝ) * m * deltaPairs ε ((m * d : ℝ) / q + (q : ℝ)⁻¹)) + 4 * deltaQ ε
    + ((m : ℝ) * d + 1) / q

/-- **`δ_ld`**: the seeded soundness theorem's error at `(q, 4m, d, 1)` for a strategy of value
`1 - δ_GS`. -/
def deltaLD (q m d : ℕ) (ε : ℝ) : ℝ := deltaCL q (4 * m) d (deltaGS q m d ε)

/-! ## The lemma -/

section Global

variable (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ψ : dA × dB → ℂ} {ε : ℝ}

/-! ## The output of the lemma, as a structure -/

/-- **The output of `lem:qld-global-pvm`, as a structure**: the two projective low-degree
measurements on the dilated registers, the two point consistencies against the opposite party's
padded point measurements (extended by the identity), and their mutual consistency, all on the
twice-padded state and with error `δ`. Stages 4b and 4c are theorems about a `GlobalPair`. -/
structure GlobalPair (ψ : dA × dB → ℂ) (hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val))
    (hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)) (δ : ℝ) where
  /-- Alice's global measurement. -/
  GA : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
    (Matrix (PadReg F m d dA) (PadReg F m d dA) ℂ)
  /-- Bob's global measurement. -/
  GB : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := 4 * m) (d := d))
    (Matrix (PadReg F m d dB) (PadReg F m d dB) ℂ)
  /-- Alice's padded points against Bob's evaluated global measurement. -/
  consA : inconsistency (uniform (Point F (4 * m))) (padState (F := F) (m := m) (d := d) ψ)
    (fun u => (padPt hprojA u).aOp (E := CL.Answer F (4 * m) d 1)) (evalPOVM GB) ≤ δ
  /-- Alice's evaluated global measurement against Bob's padded points. -/
  consB : inconsistency (uniform (Point F (4 * m))) (padState (F := F) (m := m) (d := d) ψ)
    (evalPOVM GA) (fun u => (padPt hprojB u).aOp (E := CL.Answer F (4 * m) d 1)) ≤ δ
  /-- The two global measurements against each other. -/
  consAB : inconsistency (uniform Unit) (padState (F := F) (m := m) (d := d) ψ)
    (fun _ => GA.toPOVM ()) (fun _ => GB.toPOVM ()) ≤ δ

end Global

/-! ## The expanded point measurements on the dilated registers -/

section Lift

variable {d' : Type} [Fintype d'] [DecidableEq d']

/-- A party's expanded point measurement, doubly extended to the dilated register. -/
def liftOp (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) (a : F) :
    Matrix (PadReg F m d d') (PadReg F m d d') ℂ :=
  aOp (aOp (hatMats M W u a))

theorem isPVM_liftOp {M : Question F m → POVM (Answer F m d) d'}
    (hM : ∀ q, IsPVM fun a => (((M q).mats a).val)) (W : Bas) (u : Point F m) :
    IsPVM (liftOp M W u) :=
  (isPVM_hatMats hM W u).aOp.aOp

/-- The sandwich combination of the lifted measurements is the lifted padded point measurement. -/
theorem sandComb_liftOp (M : Question F m → POVM (Answer F m d) d') (u : Point F (4 * m)) (c : F) :
    sandComb (liftOp M .X) (liftOp M .Z) u c
      = aOp (aOp (ptComb (sand (hatMats M .X (xBlk u)) (hatMats M .Z (zBlk u))) (alph u) (bet u)
          c)) := by
  simp only [sandComb, ptComb, sand, liftOp, ← aOp_mul, ← aOp_sum]

theorem comm_liftOp (M : Question F m → POVM (Answer F m d) d') (x z : Point F m) (p : F × F) :
    comm (liftOp M .X x) (liftOp M .Z z) p = aOp (aOp (hatComm M x z p.1 p.2)) := by
  simp only [comm, liftOp, hatComm, ← aOp_mul, ← aOp_sub]

end Lift

/-! ## Norms on the twice-padded state -/

section Norms

variable (ψ : dA × dB → ℂ)

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem normSq_stateVecB_padState_aOp_aOp (C : Matrix (dB × Anc F m) (dB × Anc F m) ℂ) :
    ‖stateVecB (padState (F := F) (m := m) (d := d) ψ) (aOp (aOp C))‖ ^ 2
      = ‖stateVecB (hatVec (F := F) (m := m) ψ) C‖ ^ 2 := by
  rw [padState, normSq_stateVecB_extVec2_aOp, extHat, normSq_stateVecB_extVec2_aOp]

omit [Algebra (ZMod 2) F] [NeZero m] in
theorem stateSqNorm_padState_aOp_aOp (C : Matrix (dA × Anc F m) (dA × Anc F m) ℂ) :
    stateSqNorm (padState (F := F) (m := m) (d := d) ψ) (aOp (aOp C))
      = stateSqNorm (hatVec (F := F) (m := m) ψ) C := by
  rw [padState, stateSqNorm_extVec2_aOp, extHat, stateSqNorm_extVec2_aOp]

theorem swapVec_padState_unit (hψ : star ψ ⬝ᵥ ψ = 1) :
    star (swapVec (padState (F := F) (m := m) (d := d) ψ))
      ⬝ᵥ swapVec (padState (F := F) (m := m) (d := d) ψ) = 1 := by
  rw [swapVec_dotProduct]
  exact padState_unit hψ

end Norms

/-! ## The commutator weights of the two strategies, on the twice-padded state -/

section Comm

variable (hm : m ∣ Fintype.card F) {MA : Question F m → POVM (Answer F m d) dA}
  {MB : Question F m → POVM (Answer F m d) dB} {ψ : dA × dB → ℂ} {ε : ℝ}

/-- Bob's commutator weight, from `lem:qld-combined-points`. -/
theorem sum_comm_liftOp_B_le (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z) * ∑ p : F × F,
        ‖stateVecB (padState (F := F) (m := m) (d := d) ψ)
          (comm (liftOp MB .X x) (liftOp MB .Z z) p)‖ ^ 2
      ≤ 57676416 * ε := by
  have h := sum_content_hatComm_le_B (MA := MA) hψ hfail
  rw [sum_content_blocks (fun x z => ∑ p : F × F,
    ‖stateVecB (hatVec (F := F) (m := m) ψ) (hatComm MB x z p.1 p.2)‖ ^ 2)] at h
  simpa only [comm_liftOp, normSq_stateVecB_padState_aOp_aOp] using h

/-- Alice's commutator weight, read on the swapped padded state. -/
theorem sum_comm_liftOp_A_le (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ x, ∑ z, (uniform (Point F m) x * uniform (Point F m) z) * ∑ p : F × F,
        ‖stateVecB (swapVec (padState (F := F) (m := m) (d := d) ψ))
          (comm (liftOp MA .X x) (liftOp MA .Z z) p)‖ ^ 2
      ≤ 57676416 * ε := by
  have h := sum_content_hatComm_le (MB := MB) hψ hfail
  rw [sum_content_blocks (fun x z => ∑ p : F × F,
    stateSqNorm (hatVec (F := F) (m := m) ψ) (hatComm MA x z p.1 p.2))] at h
  have hn : ∀ (x z : Point F m) (p : F × F),
      ‖stateVecB (swapVec (padState (F := F) (m := m) (d := d) ψ))
        (comm (liftOp MA .X x) (liftOp MA .Z z) p)‖ ^ 2
      = stateSqNorm (hatVec (F := F) (m := m) ψ) (hatComm MA x z p.1 p.2) := by
    intro x z p
    rw [norm_stateVecB, swapVec_swapVec, comm_liftOp, ← stateSqNorm, stateSqNorm_padState_aOp_aOp]
  simpa only [hn] using h

end Comm

/-! ## Stage 4b, on a `GlobalPair` -/

namespace GlobalPair

variable {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ψ : dA × dB → ℂ} {hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val)}
  {hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)} {δ : ℝ}
  (P : GlobalPair ψ hprojA hprojB δ)

/-- Alice's global measurement is consistent with the sandwich combination of Bob's lifted
point measurements: the form `lem:qld-global-products` consumes. -/
theorem cons_sandComb_A (hψ : star ψ ⬝ᵥ ψ = 1) :
    1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, bornProb
      (padState (F := F) (m := m) (d := d) ψ) (P.GA.M () g)
      (sandComb (liftOp MB .X) (liftOp MB .Z) u (g.eval u)) := by
  have h := P.consB
  rw [inconsistency_evalPOVM_eq _ (sum_uniform_eq_one _) (padState_unit hψ)] at h
  have hmats : ∀ (u : Point F (4 * m)) (c : F),
      (((padPt hprojB u).aOp (E := CL.Answer F (4 * m) d 1)).mats c).val
        = sandComb (liftOp MB .X) (liftOp MB .Z) u c := fun u c => by
    rw [padPt_aOp_mats, sandComb_liftOp]
  simp only [hmats] at h
  linarith

/-- Bob's version, on the swapped padded state. -/
theorem cons_sandComb_B (hψ : star ψ ⬝ᵥ ψ = 1) :
    1 - δ ≤ ∑ u, uniform (Point F (4 * m)) u * ∑ g, bornProb
      (swapVec (padState (F := F) (m := m) (d := d) ψ)) (P.GB.M () g)
      (sandComb (liftOp MA .X) (liftOp MA .Z) u (g.eval u)) := by
  have h := P.consA
  rw [← inconsistency_swapVec,
    inconsistency_evalPOVM_eq _ (sum_uniform_eq_one _) (swapVec_padState_unit ψ hψ)] at h
  have hmats : ∀ (u : Point F (4 * m)) (c : F),
      (((padPt hprojA u).aOp (E := CL.Answer F (4 * m) d 1)).mats c).val
        = sandComb (liftOp MA .X) (liftOp MA .Z) u c := fun u c => by
    rw [padPt_aOp_mats, sandComb_liftOp]
  simp only [hmats] at h
  linarith

variable (hm : m ∣ Fintype.card F) {ε : ℝ}

/-- **`lem:qld-global-products`, Alice's measurement against Bob's `Z_b X_a`.** -/
theorem products_ZX_A (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm (padState (F := F) (m := m) (d := d) ψ)
        ((aOp (P.GA.M () g) : Matrix (PadReg F m d dA × PadReg F m d dB) _ ℂ)
          * bOp (1 - ordComb ordZX (liftOp MB .X) (liftOp MB .Z) u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * (57676416 * ε) :=
  sum_snorm_sq_ordZX_le (padState_unit hψ) P.GA (isPVM_liftOp hprojB .X) (isPVM_liftOp hprojB .Z)
    (P.cons_sandComb_A hψ) (sum_comm_liftOp_B_le hm hψ hfail)

/-- **`lem:qld-global-products`, Alice's measurement against Bob's `X_a Z_b`.** -/
theorem products_XZ_A (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm (padState (F := F) (m := m) (d := d) ψ)
        ((aOp (P.GA.M () g) : Matrix (PadReg F m d dA × PadReg F m d dB) _ ℂ)
          * bOp (1 - ordComb ordXZ (liftOp MB .X) (liftOp MB .Z) u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * (57676416 * ε) :=
  sum_snorm_sq_ordXZ_le (padState_unit hψ) P.GA (isPVM_liftOp hprojB .X) (isPVM_liftOp hprojB .Z)
    (P.cons_sandComb_A hψ) (sum_comm_liftOp_B_le hm hψ hfail)

/-- **`lem:qld-global-products`, Bob's measurement against Alice's `Z_b X_a`**, on the swapped
padded state. -/
theorem products_ZX_B (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm (swapVec (padState (F := F) (m := m) (d := d) ψ))
        ((aOp (P.GB.M () g) : Matrix (PadReg F m d dB × PadReg F m d dA) _ ℂ)
          * bOp (1 - ordComb ordZX (liftOp MA .X) (liftOp MA .Z) u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * (57676416 * ε) :=
  sum_snorm_sq_ordZX_le (swapVec_padState_unit ψ hψ) P.GB (isPVM_liftOp hprojA .X)
    (isPVM_liftOp hprojA .Z) (P.cons_sandComb_B hψ) (sum_comm_liftOp_A_le hm hψ hfail)

/-- **`lem:qld-global-products`, Bob's measurement against Alice's `X_a Z_b`.** -/
theorem products_XZ_B (hψ : star ψ ⬝ᵥ ψ = 1) (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    ∑ u, uniform (Point F (4 * m)) u * ∑ g, snorm (swapVec (padState (F := F) (m := m) (d := d) ψ))
        ((aOp (P.GB.M () g) : Matrix (PadReg F m d dB × PadReg F m d dA) _ ℂ)
          * bOp (1 - ordComb ordXZ (liftOp MA .X) (liftOp MA .Z) u (g.eval u))) ^ 2
      ≤ 2 * δ + 2 * (57676416 * ε) :=
  sum_snorm_sq_ordXZ_le (swapVec_padState_unit ψ hψ) P.GB (isPVM_liftOp hprojA .X)
    (isPVM_liftOp hprojA .Z) (P.cons_sandComb_B hψ) (sum_comm_liftOp_A_le hm hψ hfail)

/-- **`lem:qld-global-separate` for Alice's global measurement**: the outcomes that are not of the
form `α g_X(x) + β g_Z(z)` weigh at most `4Δ / (1 - 2η)`, where `Δ = 2δ + 2 · 57676416 ε` is the
bound of `lem:qld-global-products` for either order and `η = (2 + 2d + 8md)/q`. -/
theorem sum_not_isGood_mass_A_le (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    (1 - 2 * ((2 + 2 * d + 8 * m * d) / Fintype.card F))
        * ∑ g ∈ univ.filter (fun g => ¬ IsGood g),
          bornProb (padState (F := F) (m := m) (d := d) ψ) (P.GA.M () g) 1
      ≤ 4 * (2 * δ + 2 * (57676416 * ε)) := by
  have h := sum_not_isGood_mass_le hd _ P.GA (isPVM_liftOp hprojB .X) (isPVM_liftOp hprojB .Z)
    (P.products_XZ_A hm hψ hfail) (P.products_ZX_A hm hψ hfail)
  linarith

/-- **`lem:qld-global-separate` for Bob's global measurement.** -/
theorem sum_not_isGood_mass_B_le (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) :
    (1 - 2 * ((2 + 2 * d + 8 * m * d) / Fintype.card F))
        * ∑ g ∈ univ.filter (fun g => ¬ IsGood g),
          bornProb (padState (F := F) (m := m) (d := d) ψ) 1 (P.GB.M () g)
      ≤ 4 * (2 * δ + 2 * (57676416 * ε)) := by
  have h := sum_not_isGood_mass_le hd _ P.GB (isPVM_liftOp hprojA .X) (isPVM_liftOp hprojA .Z)
    (P.products_XZ_B hm hψ hfail) (P.products_ZX_B hm hψ hfail)
  simp only [bornProb_swapVec] at h
  linarith

/-! ## The errors of stage 4c -/

end GlobalPair

/-- **`Δ`**, the ordered-products bound of `lem:qld-global-products` for a `GlobalPair` of error
`δ` on a strategy of failure `ε`: `2 δ + 2 κ` with `κ = 57676416 ε`. -/
def deltaProd (δ ε : ℝ) : ℝ := 2 * δ + 2 * (57676416 * ε)

/-- **`δ_G`**, the weight of the outcomes that are not of the separated form
`α g_X(x) + β g_Z(z)`: `8 Δ`, from `lem:qld-global-separate` under `48 m d ≤ q`. -/
def deltaSep (δ ε : ℝ) : ℝ := 8 * deltaProd δ ε

/-- **`δ_S`**, the error of `lem:qld-simultaneous`: the marginal estimate
`2 √Δ + 2/q + δ_G`. -/
noncomputable def deltaS (q : ℕ) (δ ε : ℝ) : ℝ :=
  2 * Real.sqrt (deltaProd δ ε) + 2 / q + deltaSep δ ε

/-- The opposite party's expanded point measurement, doubly extended to the dilated register. -/
def liftPt {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) :
    POVM F (PadReg F m d d') :=
  ((hatPtPOVM M W u).aOp (E := F × F)).aOp (E := CL.Answer F (4 * m) d 1)

theorem liftPt_mats {d' : Type} [Fintype d'] [DecidableEq d']
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (u : Point F m) (a : F) :
    (((liftPt M W u).mats a).val) = liftOp M W u a := rfl

namespace GlobalPair

variable {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ψ : dA × dB → ℂ} {hprojA : ∀ q, IsPVM fun a => (((MA q).mats a).val)}
  {hprojB : ∀ q, IsPVM fun a => (((MB q).mats a).val)} {δ : ℝ}
  (P : GlobalPair ψ hprojA hprojB δ)

variable (hm : m ∣ Fintype.card F) {ε : ℝ}

omit [Algebra (ZMod 2) F] in
/-- Under `48 m d ≤ q` the factor `1 - 2η` of `lem:qld-global-separate` is at least `1/2`. -/
theorem one_sub_two_eta_ge (hd : 1 ≤ d) (hq : 48 * m * d ≤ Fintype.card F) :
    (1 : ℝ) / 2 ≤ 1 - 2 * ((2 + 2 * d + 8 * m * d) / Fintype.card F) := by
  have hm1 : (1 : ℝ) ≤ m := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hq0 : (0 : ℝ) < Fintype.card F := by
    exact_mod_cast Fintype.card_pos
  have hqc : (48 : ℝ) * m * d ≤ Fintype.card F := by exact_mod_cast hq
  have hkey : ((2 : ℝ) + 2 * d + 8 * m * d) / Fintype.card F ≤ 1 / 4 := by
    rw [div_le_iff₀ hq0]
    nlinarith
  linarith

include hm in
/-- **`lem:qld-global-separate`, solved for the weight**: under `48 m d ≤ q` the outcomes of
Alice's global measurement that are not of the separated form weigh at most `δ_G`. -/
theorem sum_not_isGood_mass_A_le' (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hq : 48 * m * d ≤ Fintype.card F) :
    ∑ g ∈ univ.filter (fun g => ¬ IsGood g),
      bornProb (padState (F := F) (m := m) (d := d) ψ) (P.GA.M () g) 1
      ≤ deltaSep δ ε := by
  have h := P.sum_not_isGood_mass_A_le hm hd hψ hfail
  have h2 := one_sub_two_eta_ge (F := F) (m := m) (d := d) hd hq
  have h0 : 0 ≤ ∑ g ∈ univ.filter (fun g => ¬ IsGood g),
      bornProb (padState (F := F) (m := m) (d := d) ψ) (P.GA.M () g) 1 :=
    Finset.sum_nonneg fun g _ => bornProb_nonneg _
      (posSemidef_of_proj (P.GA.selfAdjoint () g) (P.GA.projective () g)) Matrix.PosSemidef.one
  rw [deltaSep, deltaProd]
  nlinarith

include hm in
/-- **`lem:qld-global-separate`, solved for the weight**, for Bob's global measurement. -/
theorem sum_not_isGood_mass_B_le' (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hq : 48 * m * d ≤ Fintype.card F) :
    ∑ g ∈ univ.filter (fun g => ¬ IsGood g),
      bornProb (swapVec (padState (F := F) (m := m) (d := d) ψ)) (P.GB.M () g) 1
      ≤ deltaSep δ ε := by
  have h := P.sum_not_isGood_mass_B_le hm hd hψ hfail
  simp only [bornProb_swapVec]
  have h2 := one_sub_two_eta_ge (F := F) (m := m) (d := d) hd hq
  have h0 : 0 ≤ ∑ g ∈ univ.filter (fun g => ¬ IsGood g),
      bornProb (padState (F := F) (m := m) (d := d) ψ) 1 (P.GB.M () g) :=
    Finset.sum_nonneg fun g _ => bornProb_nonneg _ Matrix.PosSemidef.one
      (posSemidef_of_proj (P.GB.selfAdjoint () g) (P.GB.projective () g))
  rw [deltaSep, deltaProd]
  nlinarith

/-! ## The evaluated marginals of the completed pair measurement -/

include hm in
/-- **`lem:qld-global-sandwich` for Alice's completed pair measurement**: its evaluated `W`
marginal is consistent with Bob's expanded `(Point, W)` measurement, with error `δ_S`. -/
theorem inconsistency_evalMarg_A_le (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hq : 48 * m * d ≤ Fintype.card F)
    (W : Bas) :
    inconsistency (uniform (Point F m)) (padState (F := F) (m := m) (d := d) ψ)
        (fun u => evalMarg (pairMeas hd P.GA) W u) (fun u => liftPt MB W u)
      ≤ deltaS (Fintype.card F) δ ε := by
  have hbad := P.sum_not_isGood_mass_A_le' hm hd hψ hfail hq
  cases W with
  | X =>
      refine inconsistency_evalMarg_X_le hd (padState_unit hψ) P.GA (isPVM_liftOp hprojB .X)
        (isPVM_liftOp hprojB .Z) (fun u => liftPt MB .X u) (fun u a => liftPt_mats MB .X u a)
        ?_ hbad
      rw [deltaProd]
      exact P.products_ZX_A hm hψ hfail
  | Z =>
      refine inconsistency_evalMarg_Z_le hd (padState_unit hψ) P.GA (isPVM_liftOp hprojB .X)
        (isPVM_liftOp hprojB .Z) (fun u => liftPt MB .Z u) (fun u a => liftPt_mats MB .Z u a)
        ?_ hbad
      rw [deltaProd]
      exact P.products_XZ_A hm hψ hfail

include hm in
/-- **`lem:qld-global-sandwich` for Bob's completed pair measurement**, on the padded state with
the parties exchanged. -/
theorem inconsistency_evalMarg_B_le (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hq : 48 * m * d ≤ Fintype.card F)
    (W : Bas) :
    inconsistency (uniform (Point F m)) (padState (F := F) (m := m) (d := d) ψ)
        (fun u => liftPt MA W u) (fun u => evalMarg (pairMeas hd P.GB) W u)
      ≤ deltaS (Fintype.card F) δ ε := by
  have hbad := P.sum_not_isGood_mass_B_le' hm hd hψ hfail hq
  rw [← inconsistency_swapVec]
  cases W with
  | X =>
      refine inconsistency_evalMarg_X_le hd (swapVec_padState_unit ψ hψ) P.GB
        (isPVM_liftOp hprojA .X) (isPVM_liftOp hprojA .Z) (fun u => liftPt MA .X u)
        (fun u a => liftPt_mats MA .X u a) ?_ hbad
      rw [deltaProd]
      exact P.products_ZX_B hm hψ hfail
  | Z =>
      refine inconsistency_evalMarg_Z_le hd (swapVec_padState_unit ψ hψ) P.GB
        (isPVM_liftOp hprojA .X) (isPVM_liftOp hprojA .Z) (fun u => liftPt MA .Z u)
        (fun u a => liftPt_mats MA .Z u a) ?_ hbad
      rw [deltaProd]
      exact P.products_XZ_B hm hψ hfail

/-! ## The interface instance -/

include hm in
/-- **`lem:qld-simultaneous`**: the completed pair measurements of a `GlobalPair`, carried to the
register shape of `SimulPair` by the associativity reindexing, are a `SimulPair` of error
`δ_S = 2 √Δ + 2/q + δ_G`. -/
noncomputable def toSimulPair (hd : 1 ≤ d) (hψ : star ψ ⬝ᵥ ψ = 1)
    (hfail : 1 - povmValue (qldGame hm) ψ MA MB ≤ ε) (hq : 48 * m * d ≤ Fintype.card F) :
    SimulPair ψ MA MB (deltaS (Fintype.card F) δ ε) where
  EA := (F × F) × CL.Answer F (4 * m) d 1
  instFintypeEA := inferInstance
  instDecEqEA := inferInstance
  EB := (F × F) × CL.Answer F (4 * m) d 1
  instFintypeEB := inferInstance
  instDecEqEB := inferInstance
  Φ := reindexVec (Equiv.prodAssoc (dA × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
    (Equiv.prodAssoc (dB × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
    (padState (F := F) (m := m) (d := d) ψ)
  Φ_unit := reindexVec_unit _ _ (padState_unit hψ)
  Φ_reduced := fun X Y => by
    rw [← reindex_aOp_aOp (E := F × F) (E' := CL.Answer F (4 * m) d 1) X,
      ← reindex_aOp_aOp (E := F × F) (E' := CL.Answer F (4 * m) d 1) Y, bornProb_reindex,
      bornProb_padState_aOp_aOp]
  SA := (pairMeas hd P.GA).reindex
    (Equiv.prodAssoc (dA × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
  SA_proj := isPVM_reindex_povm _ (isPVM_pairMeas hd P.GA)
  SB := (pairMeas hd P.GB).reindex
    (Equiv.prodAssoc (dB × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))
  SB_proj := isPVM_reindex_povm _ (isPVM_pairMeas hd P.GB)
  consA := fun W => by
    have hmap : ∀ u : Point F m, evalMarg ((pairMeas hd P.GA).reindex
        (Equiv.prodAssoc (dA × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))) W u
        = (evalMarg (pairMeas hd P.GA) W u).reindex
          (Equiv.prodAssoc (dA × Anc F m) (F × F) (CL.Answer F (4 * m) d 1)) :=
      fun u => (POVM.map_reindex _ _ _).symm
    have hpt : ∀ u : Point F m,
        (hatPtPOVM MB W u).aOp (E := (F × F) × CL.Answer F (4 * m) d 1)
          = (liftPt MB W u).reindex
            (Equiv.prodAssoc (dB × Anc F m) (F × F) (CL.Answer F (4 * m) d 1)) :=
      fun u => (POVM.aOp_aOp_reindex _).symm
    simp only [hmap, hpt]
    rw [inconsistency_reindex]
    exact P.inconsistency_evalMarg_A_le hm hd hψ hfail hq W
  consB := fun W => by
    have hmap : ∀ u : Point F m, evalMarg ((pairMeas hd P.GB).reindex
        (Equiv.prodAssoc (dB × Anc F m) (F × F) (CL.Answer F (4 * m) d 1))) W u
        = (evalMarg (pairMeas hd P.GB) W u).reindex
          (Equiv.prodAssoc (dB × Anc F m) (F × F) (CL.Answer F (4 * m) d 1)) :=
      fun u => (POVM.map_reindex _ _ _).symm
    have hpt : ∀ u : Point F m,
        (hatPtPOVM MA W u).aOp (E := (F × F) × CL.Answer F (4 * m) d 1)
          = (liftPt MA W u).reindex
            (Equiv.prodAssoc (dA × Anc F m) (F × F) (CL.Answer F (4 * m) d 1)) :=
      fun u => (POVM.aOp_aOp_reindex _).symm
    simp only [hmap, hpt]
    rw [inconsistency_reindex]
    exact P.inconsistency_evalMarg_B_le hm hd hψ hfail hq W

end GlobalPair

/-! ## `lem:qld-simultaneous`, from the strategy -/

section Exists

variable (hm : m ∣ Fintype.card F) (hm4 : 4 * m ∣ Fintype.card F)
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ψ : dA × dB → ℂ} {ε : ℝ}

end Exists

end MIPRE.QLD

end


