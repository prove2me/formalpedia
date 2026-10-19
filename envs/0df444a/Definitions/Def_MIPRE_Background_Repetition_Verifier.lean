-- Prove2me | Definitions.Def_MIPRE_Background_Repetition_Verifier
-- name    : MIPRE_Background_Repetition_Verifier
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T15:59:15.191952+00:00
-- url     : https://prove2.me/theorems/a1d74092-703e-47b0-a4ae-44339192e8f4
-- title:
--   Parallel repetition of normal form verifiers: the repeated verifier and the stage instance
-- statement:
--   Let `V : Verifier ℓ` be an $\ell$-level normal form verifier, $\lambda, \tau, \beta, n \in \mathbb N$, with $k = 2^{\tau(|\lambda|+|n|)}$ repetitions and per-coordinate answer length $B = 2^{\beta(|\lambda|+|n|)}$ (`Repetition.reps`, `Repetition.parseBound`). The definitions of `MIPRE.Background.Repetition.Verifier` inhabit blueprint `thm:parallel-repetition`.
--
--   `MIPRE.repVerifier V lam tau beta : Verifier ℓ` pairs `repSampler V.sampler lam tau` with `repDecider V.sampler.prog V.decider.prog lam tau beta`. `MIPRE.questionsEquiv` splits its questions into $k$-tuples of those of $\mathcal V_n$; `MIPRE.midGame` is `(V.game n B).repeat k` reindexed along it (`MIPRE.Game.reindex`). `MIPRE.tupleEmbed k B T hT : (Fin k → Answers B) ↪ Answers T` (`hT : k * (4 * B + 2) + 1 ≤ T`) encodes answer tuples as self-delimiting strings. `MIPRE.sampC`, `sampM`, `sampE`, `decC`, `decM`, `decE` are successive `Exists.choose` of `repSampler_timeBound` and `repDecider_timeBound`; `MIPRE.repBound` and `MIPRE.repAnsBound` $= 5(X+1)^2$ bound the output's complexity. `MIPRE.repetition ℓ : Repetition ℓ` assembles these (`c := Repetition.repConst`, `deg := max sampE decE`, programs via `PolyTimeFun.smn`) with the guarantees `within_repVerifier`, `hasPerfectPCC_repVerifier` (value-1 PCC strategies transfer at bound $5(k+B+1)^2$) and `valStar_repVerifier_le`: for $\varepsilon > 0$ with $\mathrm{val}^*(\mathcal V_n) \leq 1 - \varepsilon$ at answer length $B$,
--
--   $$\mathrm{val}^*(\mathcal V^{\mathrm{rep}}_n) \;\leq\; \exp\!\Big(-\frac{c\,\varepsilon^{13}\,k}{B+1}\Big).$$
--
--   The eighteen embedded lemmas are the three guarantees and their inputs: `valStar_repVerifier` (the output's game is the repeated game), the constants' specifications and answer-bound arithmetic.
--
--   **Formalization Note** `MIPRE.repetition 7` is a `Repetition 7` (`Pipeline.Repetition`), the hypothesis `MIPRE.GapCompression.ofPipeline` consumes. Soundness rests, through `Repetition.repConst` and `quantumValue_repeat_le_soundBound`, on `MIPRE.Repetition.quantumValue_repeat_le`, which is `QuantumParallelRepetition.distributionUniformExponential` of the repository's read-only vendored copy of `QuantumParallelRepetition.lean` from openai/ten-proofs (commit `94bc0feb`, Apache 2.0), the Lean proof of exponential parallel repetition for two-player entangled games; its statements and proofs are upstream's, not this repository's, and the uploaded copy only replaces the wholesale `import Mathlib` by the Mathlib modules the proofs use.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Repetition/Verifier.lean; blueprint thm:parallel-repetition

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Repetition/Verifier.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Opposite
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Action.Pi
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Rat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.Unitary
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.MulAction
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Holder
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.FinEnum
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Perm
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
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.PEquiv
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.CoeSort
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Restrict
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.Subtype
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Basic
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Bounds.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Max
import Mathlib.Order.MinMax
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Hom.Esakia
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Separation.GDelta
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Topology.UniformSpace.Real
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Background_Repetition_Direct
import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Background_Repetition_Entangled
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Background_Repetition_Soundness
import Definitions.Def_MIPRE_Foundations_TensorFamily
import Definitions.Def_MIPRE_Background_Repetition_TensorPower
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain
import Definitions.Def_MIPRE_Foundations_Repeat_RepDecider
import Definitions.Def_MIPRE_Foundations_Repeat_DeciderCost
import Theorems.Thm_MIPRE_CL_block_ofBits
import Theorems.Thm_MIPRE_CL_clDist_famSum
import Theorems.Thm_MIPRE_CL_length_chunk
import Theorems.Thm_MIPRE_Cost_encode_injective
import Theorems.Thm_MIPRE_Repeat_length_toBitsPost_list_le
import Theorems.Thm_MIPRE_Repeat_repDecider_accepts_iff
import Theorems.Thm_MIPRE_Repeat_repDecider_accepts_length
import Theorems.Thm_MIPRE_Repeat_repDecider_rejectsLong
import Theorems.Thm_MIPRE_Repeat_repDecider_timeBound
import Theorems.Thm_MIPRE_Repeat_repSampler_timeBound
import Theorems.Thm_MIPRE_Repetition_quantumValue_repeat_le_soundBound
import Theorems.Thm_MIPRE_Repetition_repConst_pos
import Theorems.Thm_MIPRE_SyncStrategy_isPCC_relabel
import Theorems.Thm_MIPRE_SyncStrategy_value_relabel
import Theorems.Thm_MIPRE_exists_perfectPCC_repeat_doubled
import Theorems.Thm_MIPRE_quantumValue_eq_of_equiv

/-!
# Parallel repetition of normal form verifiers: the assembly

`MIPRE.repetition ℓ : Repetition ℓ` — blueprint `thm:parallel-repetition`, inhabited
(`planning/repetition-verifier.md`, R4). The output verifier `repVerifier V λ τ β` packages the
repeated sampler (`MIPRE.Repeat.repSampler`) and the repeated decider
(`MIPRE.Repeat.repDecider`). Its game at index `n`, with answers of length at most `T` for any
`T` past the length of an encoded `k`-tuple, is the `k`-fold direct repetition of `𝒱_n` at the
parse length `B`, up to two relabelings (`valStar_repVerifier`):

* the questions `𝔽₂^{k s}` are the `k`-tuples of questions `𝔽₂^s` (`CL.blockEquiv`), with the
  distribution matching because the repeated sampler's CL functions are direct sums
  (`CL.clDist_famSum`), and the decider reads the `i`-th block of a question where the repeated
  game reads the `i`-th coordinate (`toBits_block`);
* the answers of length at most `T` contain the encoded `k`-tuples of answers of length at most
  `B` (`tupleEmbed`), on which the repeated decider accepts exactly when every coordinate is
  accepted (`repDecider_accepts_iff`), and it accepts nothing else, so the extra answers do not
  change the value (`quantumValue_extendAnswers`) nor the PCC strategies (`SyncStrategy.extend`).

Completeness is then the tensor power (`exists_perfectPCC_repeat_doubled`), soundness is
`quantumValue_repeat_le_soundBound`, and the complexity clause is the two running-time theorems
`repSampler_timeBound` and `repDecider_timeBound` at `W = Repetition.arg`, the constants they
provide chosen once (`sampC`, `decC`, …) for the polynomial `bound`.
-/

namespace MIPRE

open Cost Cost.Data Cost.Prog CL Repeat Verifier

/-! ## The output verifier -/

/-- The output of the procedure on `𝒱` at `(λ, τ, β)`: the repeated sampler and decider. -/
noncomputable def repVerifier {ℓ : ℕ} (V : Verifier ℓ) (lam tau beta : ℕ) : Verifier ℓ where
  sampler := repSampler V.sampler lam tau
  decider := repDecider V.sampler.prog V.decider.prog lam tau beta
  accepts_length n x y a b h :=
    repDecider_accepts_length V.sampler V.decider lam tau beta n x y a b h

/-! ## Games reindexed along an equivalence of the questions -/

section Reindex

variable {X Y A B X' Y' : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Fintype X']
  [Fintype Y']

/-- The game `G` played through equivalences of the question alphabets. -/
def Game.reindex (G : Game X Y A B) (eX : X' ≃ X) (eY : Y' ≃ Y) : Game X' Y' A B where
  μ x y := G.μ (eX x) (eY y)
  μ_nonneg x y := G.μ_nonneg _ _
  μ_sum_one := by
    rw [← G.μ_sum_one]
    exact Fintype.sum_equiv eX _ _ fun x => Fintype.sum_equiv eY _ _ fun y => rfl
  D x y a b := G.D (eX x) (eY y) a b

theorem quantumValue_reindex (G : Game X Y A B) (eX : X' ≃ X) (eY : Y' ≃ Y) :
    quantumValue (G.reindex eX eY) = quantumValue G :=
  quantumValue_eq_of_equiv G (G.reindex eX eY) eX eY (Equiv.refl A) (Equiv.refl B)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)

end Reindex

/-! ## Blocks of a question -/

/-- The `i`-th block of a question of `𝔽₂^{k s}` is the `i`-th chunk of its bit string. -/
theorem toBits_block {k s : ℕ} (x : Fin (k * s) → 𝔽₂) (i : Fin k) :
    toBits (block finProdFinEquiv i x) = chunk s i (toBits x) := by
  have h := block_ofBits (k := k) (s := s) (toBits x) i
  rw [ofBits_toBits] at h
  rw [h, toBits_ofBits (length_chunk (by simp) i)]

/-! ## Encoded tuples of answers -/

/-- Encoded `k`-tuples of bit strings are determined by their coordinates. -/
theorem tuple_encode_injective {k : ℕ} {f g : Fin k → BitStr}
    (h : (list (List.ofFn fun i => encode (f i))).toBitsPost =
      (list (List.ofFn fun i => encode (g i))).toBitsPost) : f = g := by
  have h2 := congrArg parse h
  simp only [parse_toBitsPost] at h2
  have h3 := congrArg toList h2
  simp only [toList_list] at h3
  have h4 := List.ofFn_injective h3
  funext i
  exact encode_injective (congrFun h4 i)

/-- The `k`-tuples of answers of length at most `B`, as answers of length at most `T`, for
`T` past the length of an encoded tuple. -/
noncomputable def tupleEmbed (k B T : ℕ) (hT : k * (4 * B + 2) + 1 ≤ T) :
    (Fin k → Answers B) ↪ Answers T where
  toFun aa := ⟨(list (List.ofFn fun i => encode (aa i).1)).toBitsPost,
    (length_toBitsPost_list_le k B _ fun i => (aa i).2).trans hT⟩
  inj' aa bb h := by
    have := tuple_encode_injective (congrArg Subtype.val h)
    funext i
    exact Subtype.ext (congrFun this i)

theorem tupleEmbed_val (k B T : ℕ) (hT : k * (4 * B + 2) + 1 ≤ T) (aa : Fin k → Answers B) :
    (tupleEmbed k B T hT aa).1 = (list (List.ofFn fun i => encode (aa i).1)).toBitsPost := rfl

/-! ## The game of the output is the repeated game -/

section Game

variable {ℓ : ℕ} (V : Verifier ℓ) (lam tau beta n : ℕ)

/-- The questions of the output at index `n` are `k`-tuples of questions of `𝒱_n`. -/
noncomputable def questionsEquiv : (repVerifier V lam tau beta).Questions n ≃
    (Fin (Repetition.reps lam tau n) → V.Questions n) :=
  blockEquiv (finProdFinEquiv (m := Repetition.reps lam tau n) (n := V.sampler.dim n))

/-- The repeated game, on the output's questions. -/
noncomputable def midGame : Game ((repVerifier V lam tau beta).Questions n)
    ((repVerifier V lam tau beta).Questions n)
    (Fin (Repetition.reps lam tau n) → Answers (Repetition.parseBound lam beta n))
    (Fin (Repetition.reps lam tau n) → Answers (Repetition.parseBound lam beta n)) :=
  ((V.game n (Repetition.parseBound lam beta n)).repeat (Repetition.reps lam tau n)).reindex
    (questionsEquiv V lam tau beta n) (questionsEquiv V lam tau beta n)

theorem quantumValue_midGame : quantumValue (midGame V lam tau beta n) =
    quantumValue ((V.game n (Repetition.parseBound lam beta n)).repeat
      (Repetition.reps lam tau n)) :=
  quantumValue_reindex _ _ _

/-- The distribution of the output's game is that of the repeated game. -/
theorem game_μ_eq (T : ℕ) (x y : (repVerifier V lam tau beta).Questions n) :
    ((repVerifier V lam tau beta).game n T).μ x y = (midGame V lam tau beta n).μ x y := by
  show clDist (CLFun.famSum finProdFinEquiv ℓ fun _ => V.sampler.cl n .alice).eval
    (CLFun.famSum finProdFinEquiv ℓ fun _ => V.sampler.cl n .bob).eval x y =
    ∏ i, V.sampler.dist n (block finProdFinEquiv i x) (block finProdFinEquiv i y)
  exact clDist_famSum finProdFinEquiv _ _ x y

/-- The output's decider on encoded tuples: every coordinate accepted. -/
theorem game_D_tuple (T : ℕ) (hT : Repetition.reps lam tau n *
      (4 * Repetition.parseBound lam beta n + 2) + 1 ≤ T)
    (x y : (repVerifier V lam tau beta).Questions n)
    (aa bb : Fin (Repetition.reps lam tau n) → Answers (Repetition.parseBound lam beta n)) :
    ((repVerifier V lam tau beta).game n T).D x y (tupleEmbed _ _ T hT aa)
      (tupleEmbed _ _ T hT bb) = (midGame V lam tau beta n).D x y aa bb := by
  classical
  have key := repDecider_accepts_iff V.sampler V.decider lam tau beta n (toBits x) (toBits y)
    (tupleEmbed _ _ T hT aa).1 (tupleEmbed _ _ T hT bb).1
  simp only [Verifier.game, midGame, Game.reindex, Game.repeat, tupleEmbed_val, questionsEquiv,
    blockEquiv, Equiv.coe_fn_mk]
  apply decide_eq_decide.mpr
  refine key.trans ?_
  constructor
  · rintro ⟨-, -, aa', bb', ha, hb, hall⟩
    have ha' := tuple_encode_injective ha
    have hb' := tuple_encode_injective hb
    subst ha' hb'
    intro i
    have hx : toBits (block finProdFinEquiv i x) = chunk (V.sampler.dim n) i (toBits x) :=
      toBits_block x i
    have hy : toBits (block finProdFinEquiv i y) = chunk (V.sampler.dim n) i (toBits y) :=
      toBits_block y i
    exact decide_eq_true (by erw [hx, hy]; exact (hall i).2.2)
  · intro h
    refine ⟨(length_toBits x).trans rfl, (length_toBits y).trans rfl, fun i => (aa i).1,
      fun i => (bb i).1, rfl, rfl, fun i => ⟨(aa i).2, (bb i).2, ?_⟩⟩
    have hx : toBits (block finProdFinEquiv i x) = chunk (V.sampler.dim n) i (toBits x) :=
      toBits_block x i
    have hy : toBits (block finProdFinEquiv i y) = chunk (V.sampler.dim n) i (toBits y) :=
      toBits_block y i
    have := of_decide_eq_true (h i)
    erw [hx, hy] at this
    exact this

/-- The output's decider accepts only encoded tuples. -/
theorem game_D_range (T : ℕ) (hT : Repetition.reps lam tau n *
      (4 * Repetition.parseBound lam beta n + 2) + 1 ≤ T)
    (x y : (repVerifier V lam tau beta).Questions n) (a b : Answers T)
    (h : ((repVerifier V lam tau beta).game n T).D x y a b = true) :
    (∃ aa, tupleEmbed _ _ T hT aa = a) ∧ ∃ bb, tupleEmbed _ _ T hT bb = b := by
  classical
  simp only [Verifier.game] at h
  obtain ⟨-, -, aa, bb, ha, hb, hall⟩ :=
    (repDecider_accepts_iff V.sampler V.decider lam tau beta n _ _ _ _).mp (of_decide_eq_true h)
  exact ⟨⟨fun i => ⟨aa i, (hall i).1⟩, Subtype.ext ha.symm⟩,
    ⟨fun i => ⟨bb i, (hall i).2.1⟩, Subtype.ext hb.symm⟩⟩

/-- **The value of the output's game is that of the repeated game**, at any answer bound past
the length of an encoded tuple. -/
theorem valStar_repVerifier (T : ℕ) (hT : Repetition.reps lam tau n *
      (4 * Repetition.parseBound lam beta n + 2) + 1 ≤ T) :
    (repVerifier V lam tau beta).valStar n T =
      quantumValue ((V.game n (Repetition.parseBound lam beta n)).repeat
        (Repetition.reps lam tau n)) := by
  classical
  have : Nonempty (Fin (Repetition.reps lam tau n) → Answers (Repetition.parseBound lam beta n)) :=
    ⟨fun _ => ⟨[], by simp⟩⟩
  rw [← quantumValue_midGame]
  exact quantumValue_extendAnswers (midGame V lam tau beta n) _ (tupleEmbed _ _ T hT)
    (tupleEmbed _ _ T hT) (game_μ_eq V lam tau beta n T) (game_D_tuple V lam tau beta n T hT)
    (game_D_range V lam tau beta n T hT)

/-- **Completeness**: a value-`1` PCC strategy for `𝒱_n` at the parse length gives one for the
output's game, the tensor power relabeled and extended to the output's answers. -/
theorem hasPerfectPCC_repVerifier (T : ℕ) (hT : Repetition.reps lam tau n *
      (4 * Repetition.parseBound lam beta n + 2) + 1 ≤ T)
    (h : V.HasPerfectPCC n (Repetition.parseBound lam beta n)) :
    (repVerifier V lam tau beta).HasPerfectPCC n T := by
  classical
  obtain ⟨S, hS, hv⟩ := exists_perfectPCC_repeat_doubled (Repetition.reps lam tau n) h
  let eX : Bool × (repVerifier V lam tau beta).Questions n ≃
      Bool × (Fin (Repetition.reps lam tau n) → V.Questions n) :=
    Equiv.prodCongr (Equiv.refl Bool) (questionsEquiv V lam tau beta n)
  have hμ₂ : ∀ p q, (midGame V lam tau beta n).doubled.μ p q =
      ((V.game n (Repetition.parseBound lam beta n)).repeat
        (Repetition.reps lam tau n)).doubled.μ (eX p) (eX q) := by
    rintro ⟨t, x⟩ ⟨u, y⟩; rfl
  have hD₂ : ∀ p q a b, (midGame V lam tau beta n).doubled.D p q a b =
      ((V.game n (Repetition.parseBound lam beta n)).repeat
        (Repetition.reps lam tau n)).doubled.D (eX p) (eX q) ((Equiv.refl _) a)
        ((Equiv.refl _) b) := by
    rintro ⟨t, x⟩ ⟨u, y⟩ a b; rfl
  have hμ₃ : ∀ p q, ((repVerifier V lam tau beta).game n T).doubled.μ p q =
      (midGame V lam tau beta n).doubled.μ p q := by
    rintro ⟨t, x⟩ ⟨u, y⟩
    simp only [Game.doubled, game_μ_eq]
  have hD₃ : ∀ p q a b, ((repVerifier V lam tau beta).game n T).doubled.D p q
      (tupleEmbed _ _ T hT a) (tupleEmbed _ _ T hT b) = (midGame V lam tau beta n).doubled.D p q a b := by
    rintro ⟨t, x⟩ ⟨u, y⟩ a b
    simp only [Game.doubled, game_D_tuple]
  let S₂ := S.relabel (midGame V lam tau beta n).doubled eX (Equiv.refl _)
  let S₃ := S₂.extend ((repVerifier V lam tau beta).game n T).doubled (tupleEmbed _ _ T hT)
  refine ⟨S₃, SyncStrategy.isPCC_extend (SyncStrategy.isPCC_relabel hS _ _ _ hμ₂) _ _ hμ₃, ?_⟩
  show S₃.value = 1
  rw [SyncStrategy.value_extend _ _ _ hμ₃ hD₃, SyncStrategy.value_relabel _ _ _ _ hμ₂ hD₂, hv]

/-- **Soundness**: `val*(𝒱_n) ≤ 1 - ε` at the parse length gives the direct repetition bound
for the output's game. -/
theorem valStar_repVerifier_le (T : ℕ) (hT : Repetition.reps lam tau n *
      (4 * Repetition.parseBound lam beta n + 2) + 1 ≤ T) {ε : ℝ} (hε : 0 < ε)
    (h : V.valStar n (Repetition.parseBound lam beta n) ≤ 1 - ε) :
    (repVerifier V lam tau beta).valStar n T ≤ Repetition.soundBound Repetition.repConst ε
      (Repetition.reps lam tau n) (Repetition.parseBound lam beta n) := by
  rw [valStar_repVerifier V lam tau beta n T hT]
  exact Repetition.quantumValue_repeat_le_soundBound _ hε h (Nat.two_pow_pos _)

end Game

/-! ## The constants of the running-time bounds -/

/-- The constants of `repSampler_timeBound`, chosen once. -/
noncomputable def sampC : ℕ := repSampler_timeBound.choose
noncomputable def sampM : ℕ := repSampler_timeBound.choose_spec.choose
noncomputable def sampE : ℕ := repSampler_timeBound.choose_spec.choose_spec.choose

theorem sampC_spec {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
    (hW : SampDom S lam tau n R W) (hS : S.TimeBoundAt n R.S R.k) :
    (repSampler S lam tau).TimeBoundAt n (sampC * (W + 1) ^ sampM) (sampE * (R.k + 1)) :=
  repSampler_timeBound.choose_spec.choose_spec.choose_spec S lam tau n R W hW hS

/-- The constants of `repDecider_timeBound`, chosen once. -/
noncomputable def decC : ℕ := repDecider_timeBound.choose
noncomputable def decM : ℕ := repDecider_timeBound.choose_spec.choose
noncomputable def decE : ℕ := repDecider_timeBound.choose_spec.choose_spec.choose

theorem decC_spec {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider) (lam tau beta n : ℕ) (R : Budget)
    (W : ℕ) (hW : DecDom S D lam tau beta n R W) (hS : S.TimeBoundAt n R.S R.k)
    (hD : D.TimeBoundAt n R.D R.k) :
    (repDecider S.prog D.prog lam tau beta).TimeBoundAt n (decC * (W + 1) ^ decM)
      (decE * (R.k + 1)) :=
  repDecider_timeBound.choose_spec.choose_spec.choose_spec S D lam tau beta n R W hW hS hD

/-- The polynomial bounding the running times and the dimension of the output. -/
noncomputable def repBound : Polynomial ℕ :=
  Polynomial.C (sampC + decC + 1) * (Polynomial.X + 1) ^ (max sampM decM + 2)

theorem repBound_eval (W : ℕ) :
    repBound.eval W = (sampC + decC + 1) * (W + 1) ^ (max sampM decM + 2) := by
  simp [repBound]

/-- The polynomial bounding the answers the output accepts, in `k(n) + B(n)`. -/
noncomputable def repAnsBound : Polynomial ℕ := Polynomial.C 5 * (Polynomial.X + 1) ^ 2

theorem repAnsBound_eval (A : ℕ) : repAnsBound.eval A = 5 * (A + 1) ^ 2 := by
  simp [repAnsBound]

theorem ans_ineq (k B : ℕ) : k * (4 * B + 2) + 1 ≤ 5 * (k + B + 1) ^ 2 := by nlinarith

/-- The encoded tuples fit in the answer bound. -/
theorem ansArg_bound (lam tau beta n : ℕ) :
    Repetition.reps lam tau n * (4 * Repetition.parseBound lam beta n + 2) + 1 ≤
      repAnsBound.eval (Repetition.ansArg lam tau beta n) := by
  rw [repAnsBound_eval]
  exact ans_ineq _ _

/-! ## The complexity clause -/

/-- **The complexity clause**: within `repBound` at `Repetition.arg`, at degree
`max sampE decE (R.k + 1)`, with answers within `repAnsBound` at `k(n) + B(n)`. -/
theorem within_repVerifier {ℓ : ℕ} (V : Verifier ℓ) (lam tau beta n : ℕ) (R : Budget)
    (hV : V.Within n R) :
    (repVerifier V lam tau beta).Within n
      ⟨repBound.eval (Repetition.arg lam tau beta n R V.size),
        repBound.eval (Repetition.arg lam tau beta n R V.size),
        repBound.eval (Repetition.arg lam tau beta n R V.size), max sampE decE * (R.k + 1),
        repAnsBound.eval (Repetition.ansArg lam tau beta n)⟩ := by
  have hW : Repetition.arg lam tau beta n R V.size = Repetition.reps lam tau n +
      Repetition.parseBound lam beta n + R.S + R.d + R.D + R.B + V.size + lam + tau + beta + n +
      10 ^ R.k := rfl
  have hsize : esize V.sampler.prog ≤ V.size := le_max_left _ _
  have hsizeD : esize V.decider.prog ≤ V.size := le_max_right _ _
  have hdim := hV.sampler_dim
  have h10 : 1 ≤ 10 ^ R.k := Nat.one_le_pow _ _ (by norm_num)
  rw [repBound_eval]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hSD : SampDom V.sampler lam tau n R (Repetition.arg lam tau beta n R V.size) :=
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    exact (sampC_spec V.sampler lam tau n R _ hSD hV.sampler_time).mono
      (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))
      (Nat.mul_le_mul_right _ (le_max_left _ _))
  · show Repetition.reps lam tau n * V.sampler.dim n ≤ _
    calc Repetition.reps lam tau n * V.sampler.dim n ≤
          Repetition.arg lam tau beta n R V.size * Repetition.arg lam tau beta n R V.size :=
          Nat.mul_le_mul (by omega) (by omega)
      _ ≤ (Repetition.arg lam tau beta n R V.size + 1) ^ 2 := by
          rw [← sq]; exact Nat.pow_le_pow_left (Nat.le_succ _) 2
      _ ≤ (Repetition.arg lam tau beta n R V.size + 1) ^ (max sampM decM + 2) :=
          Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ (sampC + decC + 1) * (Repetition.arg lam tau beta n R V.size + 1) ^
            (max sampM decM + 2) := Nat.le_mul_of_pos_left _ (by omega)
  · have hDD : DecDom V.sampler V.decider lam tau beta n R
        (Repetition.arg lam tau beta n R V.size) :=
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩
    exact (decC_spec V.sampler V.decider lam tau beta n R _ hDD hV.sampler_time
      hV.decider_time).mono
      (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega)))
      (Nat.mul_le_mul_right _ (le_max_right _ _))
  · intro x y a b hab h
    have hab' : repAnsBound.eval (Repetition.ansArg lam tau beta n) < a.length ∨
      repAnsBound.eval (Repetition.ansArg lam tau beta n) < b.length := hab
    have := repDecider_rejectsLong V.sampler V.decider lam tau beta n x y a b _
      (ansArg_bound lam tau beta n) h
    omega

/-! ## The theorem -/

/-- **Parallel repetition of normal form verifiers** (blueprint `thm:parallel-repetition`),
inhabited: the repeated sampler and decider, their programs as polynomial-time functions of
the inputs through the s-m-n map, the complexity clause `within_repVerifier`, completeness
`hasPerfectPCC_repVerifier` and soundness `valStar_repVerifier_le`. -/
noncomputable def repetition (ℓ : ℕ) : Repetition ℓ where
  c := Repetition.repConst
  c_pos := Repetition.repConst_pos
  bound := repBound
  ansBound := repAnsBound
  deg := max sampE decE
  sampler S lam tau := repSampler S lam tau
  samplerProg := (PolyTimeFun.smn (Prog × ℕ × ℕ)).comp
    ((PolyTimeFun.const (repSampCore selfUniversal.univ)).pair (PolyTimeFun.id _))
  samplerProg_eq _ _ _ := rfl
  compute := (PolyTimeFun.smn ((Prog × Prog) × ℕ × ℕ × ℕ)).comp
    ((PolyTimeFun.const (repDecCore selfUniversal.univ)).pair (PolyTimeFun.id _))
  output V lam tau beta := repVerifier V lam tau beta
  output_sampler _ _ _ _ := rfl
  output_decider _ _ _ _ := rfl
  within V lam tau beta n R hV := within_repVerifier V lam tau beta n R hV
  completeness V lam tau beta n h :=
    hasPerfectPCC_repVerifier V lam tau beta n _ (ansArg_bound lam tau beta n) h
  soundness V lam tau beta n _ hε _ h :=
    valStar_repVerifier_le V lam tau beta n _ (ansArg_bound lam tau beta n) hε h

end MIPRE


