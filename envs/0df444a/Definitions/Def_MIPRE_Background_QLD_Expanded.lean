-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Expanded
-- name    : MIPRE_Background_QLD_Expanded
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:44:57.309267+00:00
-- url     : https://prove2.me/theorems/f18b1758-c1f1-4b1a-8cb4-1903f3844556
-- title:
--   Definitions of Expanded: The expansion stage: the hatted point observables Blueprint `lem:qld-expanded-points`, the commutation half
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Expanded` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The expansion stage: the hatted point observables. Blueprint `lem:qld-expanded-points`, the commutation half. The expansion adjoins `|EPR_q>^{(x) M}` to each player and replaces the point observable by ``` W-hat^r(u) = W^r(u) (x) tau^W(r . ind_m(u)) , ``` the strategy's own observable tensored with a generalized Pauli on the ancilla. The point of doing so is a **single exact cancellation**: * the strategy's two observables commute up to the sign `(-1)^{gamma(omega)}` (`signed_commutation`), at `O(eps)`; * the two ancilla Pauli observables commute up to the *same* sign, **exactly** --- that is…
--
--   **Definitions** (18): `MIPRE.QLD.Anc` (The ancilla register: `(C^q)^{(x) M}` with `M = 2^m`, indexed by `F_q^M` --- that is, by the functions the low-degree encoding of…); `MIPRE.QLD.abaseOf` (The base point of the axis-parallel line a content presents on the `W` side.); `MIPRE.QLD.ancVec` (The ancilla vector the expansion attaches to a point question: `r_W .); `MIPRE.QLD.dbaseOf` (The base point of the diagonal line a content presents on the `W` side.); `MIPRE.QLD.ddirOf` (The direction of the diagonal line a content presents.); `MIPRE.QLD.hatLinePOVM` (**The hatted line measurement** `M̂^{(Line,W),ℓ}_f = ∑_{f' + f'' = f} M^{(Line,W),ℓ}_{f'} ⊗ τ^{W,ℓ}_{f''}`: the product of the strategy's…); `MIPRE.QLD.hatObs` (**The hatted point observable** `W-hat^r(u) = W^r(u) (x) tau^W(r .); `MIPRE.QLD.hatPOVM` (**The hatted point measurement**: the product of the strategy's point measurement with the ancilla's syndrome measurement, coarse-grained…); `MIPRE.QLD.hatVec` (**The expanded state** on the registers `A A' | B A''`: the strategy's state with a maximally entangled pair adjoined, one half to each…); `MIPRE.QLD.lineAnsPOVM` (The strategy's line measurement at a content, read as a polynomial of degree at most `n` --- the same definition for either player.); `MIPRE.QLD.lineCoeffs` (**The restriction of a multivariate polynomial to the line** `t ↦ u₀ + t w`, as a polynomial of degree at most `n` given by its…); and -4 more.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `isWeylFamily_weylOf`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Expanded` (`MIPRE/Background/QLD/Expanded.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 53 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Expanded.lean; blueprint lem:qld-expanded-commutation, lem:qld-expanded-consistency, lem:qld-expanded-lines

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Expanded.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.Algebra.Ring.Subsemiring.Defs
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
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
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
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
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Pairwise
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
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
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
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
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
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
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
import Theorems.Thm_MIPRE_POVM_map_map
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_le_condFail
import Theorems.Thm_MIPRE_xSqNorm_sum_le_two_mul
import Theorems.Thm_MIPRE_Weyl_isPVM_synOf
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wX
import Theorems.Thm_MIPRE_Weyl_isWeylFamily_wZ

/-!
# The expansion stage: the hatted point observables

Blueprint `lem:qld-expanded-points`, the commutation half. The expansion adjoins
`|EPR_q>^{(x) M}` to each player and replaces the point observable by

```
  W-hat^r(u) = W^r(u) (x) tau^W(r . ind_m(u)) ,
```

the strategy's own observable tensored with a generalized Pauli on the ancilla. The point of
doing so is a **single exact cancellation**:

* the strategy's two observables commute up to the sign `(-1)^{gamma(omega)}`
  (`signed_commutation`), at `O(eps)`;
* the two ancilla Pauli observables commute up to the *same* sign, **exactly** --- that is the
  twisted commutation relation of `def:generalized-pauli`, and the sign is the same because
  `gamma(omega)` *is* the form `tr(r_X ind(u_X) . r_Z ind(u_Z))` (`gam_eq_trDot`).

So the hatted observables commute up to nothing at all: the two signs multiply to one, and what
is left is the strategy's error with no sign in it. Without the ancillas the two bases would only
commute up to an error carrying `(-1)^gamma`, which does not improve with `eps`.

## What makes it cheap

Three facts, none of them about the Pauli test. The ancilla operator that survives the
cancellation is *unitary*, so it is invisible to the state-norm
(`norm_stateVec_kron_unitary`); what is left has an **inert** ancilla, so it has the same norm on
the expanded state as on the original one (`norm_stateVec_expVec_kron_one`); and the ancilla state
is a unit vector (`epr_unit`). The expansion therefore costs exactly the constant of
`lem:qld-obs-commutation` and nothing more.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.Weyl MIPRE.LowDegree MIPRE.LIDT
open scoped Kronecker ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

set_option linter.unusedSectionVars false

section Expansion

/-! ## The ancilla -/

/-- The ancilla register: `(C^q)^{(x) M}` with `M = 2^m`, indexed by `F_q^M` --- that is, by the
functions the low-degree encoding of `def:ld-encoding` already uses. -/
abbrev Anc (F : Type*) (m : ℕ) := (Fin m → Bool) → F

/-- The Weyl family of a basis. -/
def weylOf : Bas → Anc F m → Matrix (Anc F m) (Anc F m) ℂ
  | .X => wX
  | .Z => wZ

/-- The ancilla vector the expansion attaches to a point question: `r_W . ind_m(u_W)`. -/
def ancVec (ω : Omega F m) (W : Bas) : Anc F m := ω.r W • indVec (ω.pt W)

/-! ## The hatted observables and the expanded state -/

/-- **The hatted point observable** `W-hat^r(u) = W^r(u) (x) tau^W(r . ind_m(u))`. -/
def hatObs (hm : m ∣ Fintype.card F) (MA : Question F m → POVM (Answer F m d) dA) (W : Bas)
    (c : Content F m) : Matrix (dA × Anc F m) (dA × Anc F m) ℂ :=
  ptObs hm MA W c ⊗ₖ weylOf W (ancVec c.omega W)

/-- **The expanded state** on the registers `A A' | B A''`: the strategy's state with a
maximally entangled pair adjoined, one half to each party. -/
def hatVec (ψ : dA × dB → ℂ) : (dA × Anc F m) × (dB × Anc F m) → ℂ :=
  expVec ψ (epr (F := F) (n := Fin m → Bool))

/-! ## The cancellation -/

/-! ## The hatted measurements, and their self-consistency

The other item of `lem:qld-expanded-points`. The hatted measurement is the **convolution** of the
strategy's point measurement with the ancilla's syndrome measurement: the product measurement,
coarse-grained by addition of the two field elements. Its self-consistency across the
re-bipartitioned parties comes from three things, and nothing else:

* item 1 of `lem:qld-win` for the strategy's factor;
* **perfect** self-consistency of the syndrome projectors across the two ancilla halves, which is
  the EPR stabilizer relation of `def:weyl-epr`;
* data processing for the convolution --- taken at the **Born level**, because the
  state-dependent distance has no data-processing inequality (NW19's own remark gives a
  counterexample; the paper's `fact:data-processing` is the consistency form).

So the whole estimate runs through Born probabilities and is converted to the distance exactly
once, at the end, by `xSqNorm_sum_le_two_mul`.
-/

theorem isWeylFamily_weylOf (W : Bas) : IsWeylFamily (weylOf (F := F) (m := m) W) := by
  cases W
  exacts [isWeylFamily_wX, isWeylFamily_wZ]

/-- **The ancilla's basis measurement, coarse-grained by an arbitrary label.** Measuring all `M`
qudits in the basis `W` gives an outcome `h`; this measurement reports `φ h` instead. At
`φ h = ⟨h, ind_m(u)⟩` it is the syndrome measurement of a point question, and at ``the restriction
of `g_h` to a line'' it is the line measurement of the expansion stage. -/
def synOfPOVM {C : Type*} [Fintype C] [DecidableEq C] (W : Bas) (φ : Anc F m → C) :
    POVM C (Anc F m) :=
  (isPVM_synOf (w := weylOf W) (isWeylFamily_weylOf W) φ).toPOVM

/-- The syndrome measurement of the ancilla at a point question, as a POVM. -/
def synPOVM (W : Bas) (u : Point F m) : POVM F (Anc F m) :=
  synOfPOVM W fun h => dotF h (indVec u)

/-! ### The hatted measurement -/

/-- The point measurement read as a field element --- the same definition for either player. -/
def ptValPOVM {d' : Type} [Fintype d'] [DecidableEq d'] (hm : m ∣ Fintype.card F)
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (c : Content F m) : POVM F d' :=
  (M (c.question hm (.point W))).map rdVal

/-- **The hatted point measurement**: the product of the strategy's point measurement with the
ancilla's syndrome measurement, coarse-grained by adding the two field elements. That convolution
is the paper's `M-hat^{(Point,W),u}_a = sum_{a' + a'' = a} M_{a'} (x) tau^{W,u}_{a''}`. -/
def hatPOVM {d' : Type} [Fintype d'] [DecidableEq d'] (hm : m ∣ Fintype.card F)
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (c : Content F m) :
    POVM F (d' × Anc F m) :=
  ((ptValPOVM hm M W c).kron (synPOVM W (c.omega.pt W))).map fun p => p.1 + p.2

/-! ## The line measurements

`lem:qld-expanded-lines`, the paper's `lem:qld-comm-line-cons`. The construction is the line
analogue of the hatted point measurement: the strategy's line measurement, convolved with an
ancilla measurement that reports **the restriction of the encoding to the line** rather than its
value at a point.

Three things make it work, and all three are exact.

* `synLinePOVM_map_eval`: relabelling a line outcome of the ancilla by its value at a point of
  the line *is* the ancilla's point measurement there. Both are coarse-grainings of the same
  eigenbasis measurement (`synOf`), and the labels agree because evaluating the restriction of
  `g_h` along the line is evaluating `g_h` at the point (`eval_lineCoeffs`). The paper gets the
  same effect from "the exact consistency between the `tau^{W,line}` and `tau^{W,u}`
  measurements"; here the two families are literally the same family, relabelled.
* `isPVM_hatLinePOVM`: the convolution is **projective**, from two closure properties of
  projective measurements --- products and coarse-grainings (`isPVM_povm_kron`,
  `isPVM_povm_map`). The paper checks the same thing by hand.
* The ancilla's agreement probability is again exactly `1`
  (`sum_bornProb_epr_synOfPOVM`), so the expansion costs nothing here either.

As in the point case the whole estimate runs on Born probabilities and is converted to the
state-dependent distance once, at the end. That is what lets the paper's two forms of
line-against-point consistency --- comparing outcomes, and comparing the evaluation --- come out
of a *single* inequality: the coarse-graining that relates them is free at the Born level, and
`fact:data-processing` is never needed for `~=`.
-/

section Lines

/-! ### Restriction to a line, in coefficients -/

/-- **The restriction of a multivariate polynomial to the line** `t ↦ u₀ + t w`, as a polynomial
of degree at most `n` given by its coefficients. -/
def lineCoeffs (n : ℕ) (u₀ w : Point F m) (p : MvPolynomial (Fin m) F) : LinePoly F n :=
  fun i => (MIPRE.LowDegree.lineRestrict u₀ w p).coeff (i : ℕ)

/-- A polynomial of degree at most `k`, read as one of degree at most `n`: pad the coefficient
vector with zeros. An axis-parallel line answer has degree at most `d` and has to be added to an
ancilla restriction of degree at most `m`, so the two live in `LinePoly F (m d)` together. -/
def padLine {k : ℕ} (n : ℕ) (f : LinePoly F k) : LinePoly F n :=
  fun i => if h : (i : ℕ) < k + 1 then f ⟨i, h⟩ else 0

/-- A line answer read as a polynomial of degree at most `n`, whichever of the two line formats it
has; anything else reads as zero, which the format check makes unreachable. -/
def rdLine (n : ℕ) : Answer F m d → LinePoly F n
  | .apoly f => padLine n f
  | .dpoly f => padLine n f
  | _ => 0

/-! ### The ancilla's line measurement -/

/-- **The ancilla's line measurement** `τ^{W,ℓ}`: measure all `M` qudits in the basis `W`, and
report the restriction to the line of the low-degree encoding of the outcome. -/
def synLinePOVM (n : ℕ) (W : Bas) (u₀ w : Point F m) : POVM (LinePoly F n) (Anc F m) :=
  synOfPOVM W fun h => lineCoeffs n u₀ w (ldEnc h)

/-! ### The hatted line measurement -/

/-- The strategy's line measurement at a content, read as a polynomial of degree at most `n` ---
the same definition for either player. -/
def lineAnsPOVM {d' : Type} [Fintype d'] [DecidableEq d'] (n : ℕ) (hm : m ∣ Fintype.card F)
    (M : Question F m → POVM (Answer F m d) d') (ty : Ty) (c : Content F m) :
    POVM (LinePoly F n) d' :=
  (M (c.question hm ty)).map (rdLine n)

/-- **The hatted line measurement** `M̂^{(Line,W),ℓ}_f = ∑_{f' + f'' = f} M^{(Line,W),ℓ}_{f'} ⊗
τ^{W,ℓ}_{f''}`: the product of the strategy's line measurement with the ancilla's, coarse-grained
by adding the two polynomials. -/
def hatLinePOVM {d' : Type} [Fintype d'] [DecidableEq d'] (n : ℕ) (hm : m ∣ Fintype.card F)
    (M : Question F m → POVM (Answer F m d) d') (W : Bas) (ty : Ty)
    (base dir : Content F m → Point F m) (c : Content F m) :
    POVM (LinePoly F n) (d' × Anc F m) :=
  ((lineAnsPOVM n hm M ty c).kron (synLinePOVM n W (base c) (dir c))).map fun p => p.1 + p.2

/-! ### Self-consistency of the hatted line measurement -/

/-! ### Consistency with the expanded point measurements -/

/-! ### The two line types of the Pauli basis test -/

/-- The base point of the axis-parallel line a content presents on the `W` side. -/
def abaseOf (hm : m ∣ Fintype.card F) (W : Bas) (c : Content F m) : Point F m :=
  MIPRE.LIDT.CL.rep (dirOf hm c) (c.pt W)

/-- The direction of the diagonal line a content presents. -/
def ddirOf (hm : m ∣ Fintype.card F) (c : Content F m) : Point F m :=
  MIPRE.LIDT.CL.zeroBelow (MIPRE.LIDT.CL.chi hm c.s) c.v

/-- The base point of the diagonal line a content presents on the `W` side. -/
def dbaseOf (hm : m ∣ Fintype.card F) (W : Bas) (c : Content F m) : Point F m :=
  MIPRE.LIDT.CL.rep (ddirOf hm c) (c.pt W)

/-! ### `lem:qld-expanded-lines` -/

end Lines

end Expansion

end MIPRE.QLD

end


