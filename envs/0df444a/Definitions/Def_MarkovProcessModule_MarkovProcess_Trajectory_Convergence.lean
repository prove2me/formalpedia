-- Prove2me | Definitions.Def_MarkovProcessModule_MarkovProcess_Trajectory_Convergence
-- name    : MarkovProcessModule_MarkovProcess_Trajectory_Convergence
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T21:53:35.620134+00:00
-- url     : https://prove2.me/theorems/741f8981-0a46-4864-88b7-da714aea1ed2
-- title:
--   MarkovProcess.Trajectory.Convergence
-- statement:
--   # Convergence of the finite-dimensional distributions of Feller processes
--
--   Let `P i` be conservative Feller kernel semigroups and `Q` one more such semigroup, with
--   continuous-path processes `continuousProcess (P i)` and `continuousProcess Q`.  If the `C₀`
--   semigroups converge strongly -- by `Semigroup/TrotterKato.lean` this follows from convergence of
--   their resolvents at one
--   positive shift -- then the finite-dimensional distributions of the processes converge weakly from
--   every starting point: for every finite set `I` of times and every bounded continuous functional
--   of the coordinates at those times, the expectations converge.
--
--   The route is the identification of the finite-dimensional distributions with the finite-set
--   kernels (`continuousProcess_map_finiteEvaluation`), where the statement is
--   `Feller/FiniteSetConvergence.lean`.
--
--   Main results: `tendsto_integral_finsetEvaluation_continuousProcess`,
--   `tendsto_integral_eval_continuousProcess`.
--
--   Convergence of the finite-dimensional distributions is not convergence on path space, which needs
--   in addition a tightness estimate for the family of laws; that is not asserted here.
--
--   Complete pinned Lean module MarkovProcess.Trajectory.Convergence by Scott Armstrong (Apache-2.0). Contains the original definitions, instances, theorems and proofs in their original declaration order. Only local MarkovProcess import directives have been rewritten for Prove2Me; source mathematical declarations are unchanged. The bundle must pass Prove2Me's remote compiler before it can be used as a dependency.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Trajectory/Convergence.lean

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcessModule_MarkovProcess_Feller_FiniteSetConvergence
import Definitions.Def_MarkovProcessModule_MarkovProcess_MainSupport
import Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_existsUnique_continuousProcess_of_hasKolmogorovMoments
import Definitions.Def_MarkovProcessModule_MarkovProcess_Parameterized_ContinuousProcessProperties

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


