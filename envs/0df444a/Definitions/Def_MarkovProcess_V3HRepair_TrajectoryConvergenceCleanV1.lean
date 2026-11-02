-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_TrajectoryConvergenceCleanV1
-- name    : MarkovProcess_V3HRepair_TrajectoryConvergenceCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T13:14:30.08519+00:00
-- url     : https://prove2.me/theorems/6167034a-e1c6-4c66-95fc-f4fe05ee8363
-- title:
--   Verified MarkovProcess source repair: TrajectoryConvergenceCleanV1
-- statement:
--   Verified Lean 4 helper declarations for the MarkovProcess TrajectoryConvergenceCleanV1 module, preserving the pinned mathematical source and import dependencies.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.TrajectoryConvergenceCleanV1 source SHA-256 fc17dd019e34f74dae34601944025605ad48c7d9c9d39cb389dfe262cef6d74f. Only repaired-module import paths were converted to published Definitions.Def_MarkovProcess_V3HRepair_* names. Additional transparent proof aliases are appended after the source declarations for original frozen theorem targets a047c191-61da-442d-b280-f2652f3abbee, b65d1164-d2f7-4443-9590-78bbb71ad144; these add no mathematical assumptions.

import Definitions.Def_MarkovProcess_V3HRepair_FinsetEvaluationMeasurabilityCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_FellerMomentUniquenessCleanV1
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_V3HRepair_FiniteSetConvergenceCleanV1
import Definitions.Def_MarkovProcess_V3H_Main_4d46965d
import Definitions.Def_MarkovProcess_V3H_Parameterized_ContinuousProcessProperties_61cc1965

/-!
# Convergence of the finite-dimensional distributions of Feller processes

Let `P i` be conservative Feller kernel semigroups and `Q` one more such semigroup, with
continuous-path processes `continuousProcess (P i)` and `continuousProcess Q`.  If the `C₀`
semigroups converge strongly -- by `Semigroup/TrotterKato.lean` this follows from convergence of
their resolvents at one
positive shift -- then the finite-dimensional distributions of the processes converge weakly from
every starting point: for every finite set `I` of times and every bounded continuous functional
of the coordinates at those times, the expectations converge.

The route is the identification of the finite-dimensional distributions with the finite-set
kernels (`continuousProcess_map_finiteEvaluation`), where the statement is
`Feller/FiniteSetConvergence.lean`.

Main results: `tendsto_integral_finsetEvaluation_continuousProcess`,
`tendsto_integral_eval_continuousProcess`.

Convergence of the finite-dimensional distributions is not convergence on path space, which needs
in addition a tightness estimate for the family of laws; that is not asserted here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped BoundedContinuousFunction NNReal ZeroAtInfty

namespace MarkovProcess.SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]
  [LocallyCompactSpace alpha]
variable {iota : Type*} {l : Filter iota}
variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}

/-- **Weak convergence of the finite-dimensional distributions of the processes.**  Strong
convergence of the `C₀` semigroups makes the joint law of the coordinates at any finite set of
times converge weakly, from every starting point. -/
theorem tendsto_integral_finsetEvaluation_continuousProcess
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hPK : ∀ i, (P i).KolmogorovRegular (hPc i))
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative) (hQK : Q.KolmogorovRegular hQc)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    (I : Finset NNReal) (f : (I → alpha) →ᵇ ℝ) (x : alpha) :
    Tendsto (fun i ↦ ∫ omega, f (ContinuousPath.finsetEvaluation I omega)
        ∂(continuousProcess (P i) (hPc i) x)) l
      (nhds (∫ omega, f (ContinuousPath.finsetEvaluation I omega)
        ∂(continuousProcess Q hQc x))) := by
  have hrewrite : ∀ (R : SubMarkovKernelSemigroup alpha) (hRc : R.IsConservative)
      (hRF : R.IsFellerKernelSemigroup) (hRK : R.KolmogorovRegular hRc),
      ∫ omega, f (ContinuousPath.finsetEvaluation I omega)
          ∂(continuousProcess R hRc x) = ∫ path, f path ∂finiteSetKernel R I x := by
    intro R hRc hRF hRK
    have hmap : ((continuousProcess R hRc) x).map (ContinuousPath.finsetEvaluation I) =
        finiteSetKernel R I x := by
      rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I),
        hRF.continuousProcess_map_finiteEvaluation R hRc hRK I]
    rw [← hmap, integral_map (ContinuousPath.measurable_finsetEvaluation I).aemeasurable
      f.continuous.aestronglyMeasurable]
  have hsteps : ∀ i : iota, ∫ omega, f (ContinuousPath.finsetEvaluation I omega)
      ∂(continuousProcess (P i) (hPc i) x) = ∫ path, f path ∂finiteSetKernel (P i) I x :=
    fun i ↦ hrewrite (P i) (hPc i) (hP i) (hPK i)
  rw [hrewrite Q hQc hQ hQK]
  simp only [hsteps]
  exact tendsto_integral_boundedContinuous_finiteSetKernel hP hPc hQ hQc hconv I f x

/-- Convergence of the one-time laws: for a bounded continuous function on the state space and a
nonnegative time, the expectations of its value along the path converge. -/
theorem tendsto_integral_eval_continuousProcess
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hPK : ∀ i, (P i).KolmogorovRegular (hPc i))
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative) (hQK : Q.KolmogorovRegular hQc)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    (t : NNReal) (g : alpha →ᵇ ℝ) (x : alpha) :
    Tendsto (fun i ↦ ∫ omega, g (omega t) ∂(continuousProcess (P i) (hPc i) x)) l
      (nhds (∫ omega, g (omega t) ∂(continuousProcess Q hQc x))) := by
  have hmem : t ∈ ({t} : Finset NNReal) := Finset.mem_singleton_self t
  exact tendsto_integral_finsetEvaluation_continuousProcess hP hPc hPK hQ hQc hQK hconv {t}
    (g.compContinuous ⟨fun path ↦ path ⟨t, hmem⟩, continuous_apply _⟩) x

end

end MarkovProcess.SubMarkovKernelSemigroup

#print axioms MarkovProcess.SubMarkovKernelSemigroup.tendsto_integral_finsetEvaluation_continuousProcess
#print axioms MarkovProcess.SubMarkovKernelSemigroup.tendsto_integral_eval_continuousProcess

noncomputable def MarkovProcess.V3HRepairProof_a047c19161da442db280f2652f3abbee :=
  @MarkovProcess.SubMarkovKernelSemigroup.tendsto_integral_eval_continuousProcess

noncomputable def MarkovProcess.V3HRepairProof_b65d1164d2f74443959078bbb71ad144 :=
  @MarkovProcess.SubMarkovKernelSemigroup.tendsto_integral_finsetEvaluation_continuousProcess


