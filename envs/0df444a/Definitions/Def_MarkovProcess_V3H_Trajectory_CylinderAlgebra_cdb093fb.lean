-- Prove2me | Definitions.Def_MarkovProcess_V3H_Trajectory_CylinderAlgebra_cdb093fb
-- name    : MarkovProcess_V3H_Trajectory_CylinderAlgebra_cdb093fb
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T08:18:14.149539+00:00
-- url     : https://prove2.me/theorems/32e049e5-d09c-4f78-bd1f-550291e0436f
-- title:
--   MarkovProcess: MarkovProcess_V3H_Trajectory_CylinderAlgebra_cdb093fb
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteProductStoneWeierstrass_f57e156f
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Path_Basic_736b8012
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Cylinder test functions on continuous-path space

A *cylinder* functional of a continuous path reads the path at finitely many times and applies a
bounded continuous function to the values there.  These functionals form an algebra, they
separate points of path space (two distinct continuous paths differ at some time, and functions
vanishing at infinity separate the two values), and therefore, by Stone--Weierstrass, they are
uniformly dense on every compact set of paths.

The approximation is stated in the form that a tightness argument consumes: given a bounded
continuous functional `F` and a compact set of paths `K`, there is a *bounded* cylinder functional
that is uniformly `eps`-close to `F` on `K` and whose norm exceeds `‖F‖` by at most `eps`.  The
norm control matters, because the approximation error off `K` is paid for by the total mass
outside `K` times the sum of the two norms; without it the argument would be circular.

Main results:

* `MarkovProcess.ContinuousPath.IsBoundedCylinder`, the cylinder property, closed under sums,
  products and constants;
* `MarkovProcess.ContinuousPath.coordinateSubalgebra`, the generated algebra of test functions,
  with `coordinateSubalgebra_separatesPoints` and
  `isBoundedCylinder_of_mem_coordinateSubalgebra`;
* `MarkovProcess.ContinuousPath.exists_boundedCylinder_approx`, the Stone--Weierstrass
  approximation with norm control.

Nothing here mentions a probability law, and no continuity in a starting point is asserted.
-/

open scoped BoundedContinuousFunction NNReal ZeroAtInfty

namespace MarkovProcess

namespace ContinuousPath

section Cylinder

variable {alpha : Type*} [TopologicalSpace alpha]

/-- A functional of a continuous path that reads finitely many times and applies a bounded
continuous function to the values read. -/
def IsBoundedCylinder (G : ContinuousPath alpha → ℝ) : Prop :=
  ∃ (I : Finset ℝ≥0) (g : (I → alpha) →ᵇ ℝ),
    ∀ omega, G omega = g (finsetEvaluation I omega)

/-- Restriction of a family of states indexed by a finite set of times to a smaller set. -/
def finsetRestrict {I J : Finset ℝ≥0} (hIJ : I ⊆ J) : C(J → alpha, I → alpha) :=
  ⟨fun path i ↦ path ⟨(i : ℝ≥0), hIJ i.2⟩,
    continuous_pi fun i ↦ continuous_apply (⟨(i : ℝ≥0), hIJ i.2⟩ : J)⟩

@[simp]
theorem p2m_embedded_099d1679a309679e {I J : Finset ℝ≥0} (hIJ : I ⊆ J)
    (omega : ContinuousPath alpha) :
    finsetRestrict (alpha := alpha) hIJ (finsetEvaluation J omega) = finsetEvaluation I omega :=
  rfl









variable (alpha) in
/-- The algebra of real test functions on path space generated by the coordinate pullbacks of
functions vanishing at infinity on the state space. -/
def coordinateSubalgebra : Subalgebra ℝ C(ContinuousPath alpha, ℝ) :=
  Algebra.adjoin ℝ {G | ∃ (t : ℝ≥0) (f : C₀(alpha, ℝ)),
    G = (f : C(alpha, ℝ)).comp ⟨fun omega ↦ omega t, continuous_eval t⟩}





end Cylinder

section Approximation

variable {alpha : Type*} [MetricSpace alpha] [LocallyCompactSpace alpha]



end Approximation

end ContinuousPath

end MarkovProcess


