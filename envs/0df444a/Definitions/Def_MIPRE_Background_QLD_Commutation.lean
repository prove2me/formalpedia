-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Commutation
-- name    : MIPRE_Background_QLD_Commutation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:02:11.121977+00:00
-- url     : https://prove2.me/theorems/c23ac924-3e6e-41d8-99ae-005945182815
-- title:
--   Definitions of Commutation: Signed commutation of the point observables, on the anticommuting tuples Blueprint `lem:qld-obs-commutation`, the…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Commutation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Signed commutation of the point observables, on the anticommuting tuples. Blueprint `lem:qld-obs-commutation`, the anticommuting case. On a tuple `omega` with `gamma(omega) = 1` the two point observables **anticommute** on the state: ``` X^{r_X}(u_X) Z^{r_Z}(u_Z) (x) Id ~ - Z^{r_Z}(u_Z) X^{r_X}(u_X) (x) Id . ``` Three inputs, all already proved: * **item 7** of `lem:qld-win` (`item_ms_consistency_X`, `item_ms_consistency_Z`): each point probe agrees with one of the two distinguished `Variable` bits on the *other* side. At the level of observables that is `X (x) Id ~ Id (x) V_1` and `Z (x) Id…
--
--   **Definitions** (11): `MIPRE.QLD.acommWeight` (The weight the items of `lem:qld-win` carry on the anticommuting tuples: uniform over all contents, supported on `acommSet`.); `MIPRE.QLD.chainQty` (The per-content quantity `chain_pair_point` bounds.); `MIPRE.QLD.commWeight` (The weight the items carry on the commuting tuples.); `MIPRE.QLD.incQty` (The inconsistency of the two players' joint `Pair` measurements at one content.); `MIPRE.QLD.pairPOVM` (Alice's **joint** `Pair` measurement: both bits at once, which is the product outcome set the commutation analysis needs.); `MIPRE.QLD.pairPOVMB` (Bob's **joint** `Pair` measurement.); `MIPRE.QLD.ptObs` (**Alice's point observable**: the `±1`-observable of the trace probe of the `(Point, W)` answer against the content's own `r_W`.); `MIPRE.QLD.ptObsB` (Bob's point observable.); `MIPRE.QLD.ptPOVM` (Alice's point-probe measurement, of which `ptObs` is the observable.); `MIPRE.QLD.ptPOVMB` (Bob's point-probe measurement.); `MIPRE.QLD.varObs` (**Bob's variable observable**: the `±1`-observable of the bit a `Variable_j` answer reports.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Commutation` (`MIPRE/Background/QLD/Commutation.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 47 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Commutation.lean; blueprint lem:qld-obs-commutation-acomm, lem:qld-obs-commutation-comm

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Commutation.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
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
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_le_condFail

/-!
# Signed commutation of the point observables, on the anticommuting tuples

Blueprint `lem:qld-obs-commutation`, the anticommuting case. On a tuple `omega` with
`gamma(omega) = 1` the two point observables **anticommute** on the state:

```
X^{r_X}(u_X) Z^{r_Z}(u_Z) (x) Id  ~  - Z^{r_Z}(u_Z) X^{r_X}(u_X) (x) Id .
```

Three inputs, all already proved:

* **item 7** of `lem:qld-win` (`item_ms_consistency_X`, `item_ms_consistency_Z`): each point
  probe agrees with one of the two distinguished `Variable` bits on the *other* side. At the
  level of observables that is `X (x) Id ~ Id (x) V_1` and `Z (x) Id ~ Id (x) V_5`, at `344 eps`
  each --- item 7 at the two-outcome probe, then `xStateDist_obsOf_le`;
* **item 6** (`item_magicSquare`): those two `Variable` observables anticommute on the state, at
  `16049664 eps`;
* the **order reversal** `norm_stateVec_anticomm_le`, which is what carries an anticommutation
  from Bob's side to Alice's --- and is where the sign comes from.

## Why this case costs `eps` and not `sqrt(eps)`

The blueprint states `lem:qld-obs-commutation` at `O(sqrt(eps))`, and that is what the
*commuting* case costs: it needs the `Pair` measurement to be projective, which a general POVM
strategy's is not, so it goes through `cor:ortho-from-consistency` and pays a square root. The
anticommuting case does not: every input is already a squared-norm bound linear in `eps`, and the
only inequalities used are the triangle inequality and `(u+v+w)^2 <= 3(u^2+v^2+w^2)`. So the
constant here is honest and there is no square root --- `48157248 eps`, from
`12 * 344 + 12 * 344 + 3 * 16049664`.

That asymmetry is worth recording rather than rounding away: when the commuting case is
formalized the two halves will not combine into a single `O(sqrt(eps))` by adding constants, and
the square root will be attributable to exactly one of them.
-/

noncomputable section

namespace MIPRE.QLD

open Finset Matrix MIPRE MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

-- Every statement below mentions both players' spaces and the field, and the estimates are
-- inherited from `Win.lean` and `WinMS.lean`, whose variable blocks are the same. Omitting the
-- unused ones declaration by declaration would be a dozen `omit` lines with no consumer.
set_option linter.unusedSectionVars false

/-! ## The two observables -/

/-- **Alice's point observable**: the `±1`-observable of the trace probe of the `(Point, W)`
answer against the content's own `r_W`. This is the blueprint's `W^{r_W}(u_W)`. -/
def ptObs (hm : m ∣ Fintype.card F) (MA : Question F m → POVM (Answer F m d) dA) (W : Bas)
    (c : Content F m) : Matrix dA dA ℂ :=
  obs2 ((MA (c.question hm (.point W))).map (rdProbeAt W c))

/-- **Bob's variable observable**: the `±1`-observable of the bit a `Variable_j` answer
reports. -/
def varObs (hm : m ∣ Fintype.card F) (MB : Question F m → POVM (Answer F m d) dB)
    (j : Fin layout.s) (c : Content F m) : Matrix dB dB ℂ :=
  obs2 ((MB (c.question hm (.var j))).map rdBit)

/-! ## The weight: uniform on the anticommuting tuples -/

/-- The weight the items of `lem:qld-win` carry on the anticommuting tuples: uniform over all
contents, supported on `acommSet`. It is not a probability distribution --- its total mass is the
fraction of tuples that anticommute --- which is exactly how the items are stated. -/
def acommWeight (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] (m : ℕ)
    [NeZero m] : Content F m → ℝ :=
  fun c => if c ∈ acommSet then (Fintype.card (Content F m) : ℝ)⁻¹ else 0

/-! ## Item 7 at the level of observables

Item 7 is a POVM-level agreement: the point probe and the `Variable` bit take the same value. The
observable form is `xStateDist_obsOf_le` at the weighting `sgn`, whose cost is the number of
outcomes of the probe --- two --- so `172 eps` becomes `344 eps`. Exactly the step
`pts_obs_consistency` makes for item 1, with the weight supported on the anticommuting tuples. -/

section Items

variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

end Items

/-! ## Item 6's anticommutator, in terms of the variable observables

`item_magicSquare` states the bound for `MS.anti (msPOVM MB omega)`, the anticommutator of the
*conditional Magic Square strategy*'s two observables. Those are the same operators as
`varObs`: the conditional strategy at a `Variable` question is the Pauli test's measurement at
the corresponding question, with its answer relabelled to the bit it reports, and relabelling
along the injection `Sum.inr` does not change a coarse-grained POVM element. -/

section Anti

variable {MB : Question F m → POVM (Answer F m d) dB}

end Anti

/-! ## The lemma -/

section Main

variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

end Main

/-! ## The commuting case

The other half of `lem:qld-obs-commutation`. Here the two point observables **commute**, and the
route is the paper's: chain items 5, 4 and 1 so that each point probe is cross-party close to a
*marginal* of the `Pair` measurement on the other side, replace that measurement by a projective
one (`cor:ortho-from-consistency`), and apply the commutation analysis.

Two departures from the paper's bookkeeping, both forced by which side things live on.

**The analysis is run on Bob's observables and transferred back.** `commutation_analysis` wants the
two commuting families on one side and the joint projective measurement on the *other*, and
`exists_projective_of_consistent` produces a projective measurement on **Alice's** factor. So the
analysis is applied to *Bob's* point measurements against Alice's projectivized `Pair`
measurement, and the conclusion is carried to Alice's observables by the order-reversal rule
(`norm_stateVec_comm_le`) with `pts_obs_consistency`. The alternative --- a Bob-side orthonormali-
zation corollary --- would duplicate the whole of `Ortho.lean` through the swap.

**The chain is run in the mirrored orientation.** Every rule of `fig:decider_pauli` is stated in
both orientations, so items 5 and 1 are available with the players exchanged; item 4 is used as it
stands. The chain is
`A^{Pair}_{[beta_W = o]} ~ B^{Pair}_{[beta_W = o]} ~ A^{(Pair,W)}_o ~ B^{(Point,W)}_{probe = o}`,
three links at `172 eps` each, so `1548 eps` after one three-term triangle inequality.
-/

section Commuting

variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

/-- Alice's **joint** `Pair` measurement: both bits at once, which is the product outcome set the
commutation analysis needs. -/
def pairPOVM (hm : m ∣ Fintype.card F) (MA : Question F m → POVM (Answer F m d) dA)
    (c : Content F m) : POVM (ZMod 2 × ZMod 2) dA :=
  (MA (c.question hm .pair)).map fun a => (rdBitPair .X a, rdBitPair .Z a)

/-- Alice's point-probe measurement, of which `ptObs` is the observable. -/
def ptPOVM (hm : m ∣ Fintype.card F) (MA : Question F m → POVM (Answer F m d) dA) (W : Bas)
    (c : Content F m) : POVM (ZMod 2) dA :=
  (MA (c.question hm (.point W))).map (rdProbeAt W c)

/-- Bob's **joint** `Pair` measurement. -/
def pairPOVMB (hm : m ∣ Fintype.card F) (MB : Question F m → POVM (Answer F m d) dB)
    (c : Content F m) : POVM (ZMod 2 × ZMod 2) dB :=
  (MB (c.question hm .pair)).map fun a => (rdBitPair .X a, rdBitPair .Z a)

/-- Bob's point-probe measurement. -/
def ptPOVMB (hm : m ∣ Fintype.card F) (MB : Question F m → POVM (Answer F m d) dB) (W : Bas)
    (c : Content F m) : POVM (ZMod 2) dB :=
  (MB (c.question hm (.point W))).map (rdProbeAt W c)

/-- Bob's point observable. -/
def ptObsB (hm : m ∣ Fintype.card F) (MB : Question F m → POVM (Answer F m d) dB) (W : Bas)
    (c : Content F m) : Matrix dB dB ℂ :=
  obs2 (ptPOVMB hm MB W c)

/-! ### The three links -/

/-! ### The three averaged inputs -/

/-- The per-content quantity `chain_pair_point` bounds. -/
def chainQty (hm : m ∣ Fintype.card F) (ψ : dA × dB → ℂ)
    (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    (W : Bas) (c : Content F m) : ℝ :=
  ∑ o : ZMod 2, xSqNorm ψ ((((MA (c.question hm .pair)).map (rdBitPair W)).mats o).val)
    (((ptPOVMB hm MB W c).mats o).val)

/-- The inconsistency of the two players' joint `Pair` measurements at one content. -/
def incQty (hm : m ∣ Fintype.card F) (ψ : dA × dB → ℂ)
    (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    (c : Content F m) : ℝ :=
  pairInconsistency ψ (pairPOVM hm MA c) (pairPOVMB hm MB c)

/-- The weight the items carry on the commuting tuples. -/
def commWeight (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] (m : ℕ)
    [NeZero m] : Content F m → ℝ :=
  fun c => if c ∈ commSet then (Fintype.card (Content F m) : ℝ)⁻¹ else 0

/-! ### The per-content bound

The three inputs meet here. `chainQty` is what the chain bounds, `incQty` what
`cor:ortho-from-consistency` consumes, and the `eta` is the slack that corollary's hypothesis
asks for; it is sent to zero when the bound is averaged. -/

/-! ### Both halves

`lem:qld-obs-commutation` as the paper states it: one average over *all* contents, with the sign
`(-1)^{gamma(omega)}` inside. The two halves are the two branches of that sign, and the type graph's
content distribution is uniform, so the statement is the sum of the two restricted ones. -/

end Commuting

end MIPRE.QLD

end


