-- Prove2me | Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
-- name    : MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:38:19.306982+00:00
-- url     : https://prove2.me/theorems/29ee2510-18eb-4e3e-b98e-48e55cc46df3
-- title:
--   MarkovProcess: MarkovProcess_V3H_FiniteTime_KernelEquivariance_10113825
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Kernel_KolmogorovMoments_9b991370
import Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Rescaled conjugation of finite-time kernels

A sub-Markov kernel semigroup `P'` on a state space `beta` is the *rescaled conjugate* of `P` on
`alpha` when it is obtained from `P` by conjugating the state with a homeomorphism `e : alpha ≃ₜ beta`
and speeding time up by a positive factor `c`, that is `P' t x = ((P (c * t)) (e.symm x)).map e`.

This file transfers the finite-dimensional laws across such a relation.  The main result is
`SubMarkovKernelSemigroup.IsRescaledConjugate.finiteTimeKernel_eq`, which computes every
finite-time kernel of `P'` from the finite-time kernel of `P` at the rescaled times.  Supporting
API: the time-scaling operation `FiniteOrderedTimes.rescale`, the coordinatewise state map
`FiniteOrderedTimes.mapPath`, and two composition-product lemmas, `comap_compProd_prodMkLeft` and
`map_compProd_prodMkLeft_conjugate`, which have no direct Mathlib counterpart.

Nothing here mentions path space; the path-space equivariance statement is in
`MarkovProcess/Trajectory/Equivariance.lean`.  When the state map is an isometry, the intrinsic
Kolmogorov moment criterion also transfers, with the constant multiplied by `c ^ q`
(`IsRescaledConjugate.hasKolmogorovMoments`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory

namespace MarkovProcess

namespace FiniteOrderedTimes

/-- Multiply every time of a finite ordered family by a fixed positive factor.  Positivity of the
factor is what keeps the family strictly increasing. -/
def rescale {n : ℕ} (c : NNReal) (hc : 0 < c) (times : FiniteOrderedTimes n) :
    FiniteOrderedTimes n :=
  OrderEmbedding.ofStrictMono (fun i ↦ c * times i) fun _ _ hij ↦
    mul_lt_mul_of_pos_left (times.strictMono hij) hc



/-- Rescaling by the factor one does not change a finite ordered time family. -/
@[simp]
theorem p2m_embedded_4f4df4a623a409dc {n : ℕ} (times : FiniteOrderedTimes n) :
    times.rescale 1 one_pos = times := by
  apply DFunLike.ext _ _
  intro i
  exact one_mul (times i)





/-- Apply a map of the state space to every coordinate of a coordinate path. -/
def mapPath {ι alpha beta : Type*} (e : alpha → beta) (path : ι → alpha) : ι → beta :=
  fun i ↦ e (path i)

/-- A path mapped coordinatewise, evaluated. -/
@[simp]
theorem p2m_embedded_b02ebc87ee0ef12b {ι alpha beta : Type*} (e : alpha → beta) (path : ι → alpha) (i : ι) :
    mapPath e path i = e (path i) :=
  rfl







end FiniteOrderedTimes

namespace SubMarkovKernelSemigroup



section CompProd

variable {X X' Y Y' Z Z' : Type*} [MeasurableSpace X] [MeasurableSpace X'] [MeasurableSpace Y]
  [MeasurableSpace Y'] [MeasurableSpace Z] [MeasurableSpace Z']





end CompProd

section RescaledConjugate

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [TopologicalSpace beta] [MeasurableSpace beta] [BorelSpace beta]

/-- `P'` is the *rescaled conjugate* of `P` by the homeomorphism `e` and the time factor `c`:
started at `x`, the state of `P'` at time `t` is the image under `e` of the state of `P` at the
sped-up time `c * t` started at `e.symm x`. -/
def IsRescaledConjugate (P : SubMarkovKernelSemigroup alpha) (P' : SubMarkovKernelSemigroup beta)
    (e : alpha ≃ₜ beta)
    (c : NNReal) : Prop :=
  ∀ t x, P' t x = ((P (c * t)) (e.symm x)).map e

namespace IsRescaledConjugate

variable {P : SubMarkovKernelSemigroup alpha} {P' : SubMarkovKernelSemigroup beta} {e : alpha ≃ₜ beta}
  {c : NNReal}









end IsRescaledConjugate

section Moments

variable {alpha beta : Type*} [PseudoEMetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  [PseudoEMetricSpace beta] [MeasurableSpace beta] [BorelSpace beta]
variable {P : SubMarkovKernelSemigroup alpha} {P' : SubMarkovKernelSemigroup beta} {e : alpha ≃ₜ beta}
  {c : NNReal}



end Moments

end RescaledConjugate

end SubMarkovKernelSemigroup

end MarkovProcess


