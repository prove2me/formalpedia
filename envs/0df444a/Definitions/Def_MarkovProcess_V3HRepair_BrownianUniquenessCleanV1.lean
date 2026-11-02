-- Prove2me | Definitions.Def_MarkovProcess_V3HRepair_BrownianUniquenessCleanV1
-- name    : MarkovProcess_V3HRepair_BrownianUniquenessCleanV1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-01T10:03:18.005165+00:00
-- url     : https://prove2.me/theorems/d78e5d15-dba7-4c9b-aaf8-a4396741c995
-- title:
--   Verified MarkovProcess source repair: BrownianUniquenessCleanV1
-- statement:
--   Dense-time finite evaluation marginals uniquely determine continuous-path kernels, including the continuous Markov process law.
-- source:
--   Scott Armstrong, MarkovProcess (Apache-2.0), pinned upstream commit 1f8060caa137731fa08029592019eeaf9d997fe5; locally verified module V3HRepaired.BrownianUniquenessCleanV1 SHA-256 3d06fc9366593426912d27d02ba869356fa1631a06d9772843516c8f1f49ce92. Only repaired import paths were translated to the published Definitions.Def_MarkovProcess_V3HRepair_* module names.

import Mathlib
import Definitions.Def_MarkovProcess_V3H_Examples_HeatSemigroup_43feba3c
import Definitions.Def_MarkovProcess_V3H_Feller_Resolvent_4f8c89b8
import Definitions.Def_MarkovProcess_V3H_Trajectory_Dynkin_eb6ae7c0
import Definitions.Def_MarkovProcess_V3HRepair_KernelFiniteRestrictionIdentificationCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_KernelDenseRestrictionInjectiveCleanV1
import Definitions.Def_MarkovProcess_V3HRepair_KernelDenseRestriction
import Definitions.Def_MarkovProcess_V3HRepair_ContinuousFiniteDenseTimeSet


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Identifying continuous-path kernels from dense-time restrictions

Restriction to the fixed dense time carrier is injective on kernels whose target is continuous-path
space.  A measurable left inverse is obtained from the total continuous-extension map.  This is a
deterministic property of continuous paths; it makes no stochastic-process, Markov, or regularity
claim.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace Kernel

noncomputable section

variable {alpha beta : Type*} [TopologicalSpace alpha] [T2Space alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [MeasurableSpace beta]

variable [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]





/-- Equality of continuous-path kernels is equivalent to equality after restriction to the fixed
dense time carrier. -/
theorem map_denseRestriction_eq_iff {kappa eta : Kernel beta (ContinuousPath alpha)} :
    kappa.map ContinuousPath.denseRestriction = eta.map ContinuousPath.denseRestriction ↔
      kappa = eta := by
  constructor
  · intro h
    exact map_denseRestriction_injective (alpha := alpha) (beta := beta) h
  · exact fun h ↦ congrArg
      (fun z : Kernel beta (ContinuousPath alpha) ↦
        z.map ContinuousPath.denseRestriction) h

end
end Kernel
end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The continuous-path Markov process of a Feller semigroup

This is the entry point of the library: for a conservative sub-Markov kernel semigroup `P` on a
nonempty, locally compact Polish state space it names the continuous-path process
`continuousProcess P hP`, restates under quotable names the properties proved for that process
elsewhere in the library, and proves that it is the unique Markov kernel into continuous paths
with the finite-dimensional distributions of `P`.

Every statement carries the Kolmogorov regularity hypothesis `P.KolmogorovRegular hP`, which is
what gives the dense-time trajectory of `P` a continuous modification.  The shift and restart
statements carry in addition the Feller hypothesis `P.IsFellerKernelSemigroup`; the uniqueness
statements carry neither Feller continuity nor local compactness.

Nothing here asserts a Hunt-process property, and no statement covers a stopping time that can be
infinite.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess

section FinsetEvaluation

namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha]



end ContinuousPath

end FinsetEvaluation

namespace Kernel

noncomputable section DenseFiniteEvaluation

variable {alpha beta : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [MeasurableSpace beta]



section Identification

variable [T2Space alpha] [StandardBorelSpace (ContinuousPath alpha)]
  [MeasurableSpace.CountablySeparated (DenseTime → alpha)]

/-- A finite kernel into continuous-path space is determined by its evaluations at the finite
sets of physical times carried by rational labels. -/
theorem eq_of_map_denseFiniteEvaluation_eq
    (kappa eta : Kernel beta (ContinuousPath alpha)) [IsFiniteKernel kappa]
    (h : ∀ I : Finset DenseTime,
      kappa.map (ContinuousPath.finsetEvaluation
          (SubMarkovKernelSemigroup.denseTimePhysicalSet I)) =
        eta.map (ContinuousPath.finsetEvaluation
          (SubMarkovKernelSemigroup.denseTimePhysicalSet I))) :
    kappa = eta := by
  rw [← map_denseRestriction_eq_iff (alpha := alpha) (beta := beta)]
  apply eq_of_map_finiteRestriction_eq
  intro I
  rw [map_denseRestriction_map_restrict kappa I, map_denseRestriction_map_restrict eta I, h I]

end Identification

end DenseFiniteEvaluation

end Kernel

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)













/-- Every finite rational-time marginal of the continuous-path process is the finite-set kernel of
`P` at the corresponding physical times. -/
theorem IsConservative.continuousProcess_map_finiteEvaluation_denseTime
    (hK : P.KolmogorovRegular hP) (I : Finset DenseTime) :
    (continuousProcess P hP).map
        (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I)) =
      finiteSetKernel P (denseTimePhysicalSet I) :=
  continuousPathTrajectory_map_finiteDenseTimeSet P hP _ hK I





variable [LocallyCompactSpace alpha]









variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]







omit [LocallyCompactSpace alpha] in
/-- Uniqueness from rational times: a finite kernel into continuous paths whose evaluations at
the finite sets of physical times carried by rational labels are the finite-set kernels of `P` is
the continuous-path process of `P`.  Neither Feller continuity nor local compactness is used. -/
theorem IsConservative.eq_continuousProcess_of_map_finiteEvaluation_denseTime
    (hK : P.KolmogorovRegular hP) (Q : Kernel alpha (ContinuousPath alpha)) [IsFiniteKernel Q]
    (hQ : ∀ I : Finset DenseTime,
      Q.map (ContinuousPath.finsetEvaluation (denseTimePhysicalSet I)) =
        finiteSetKernel P (denseTimePhysicalSet I)) :
    Q = continuousProcess P hP :=
  Kernel.eq_of_map_denseFiniteEvaluation_eq Q _ fun I ↦
    (hQ I).trans (continuousProcess_map_finiteEvaluation_denseTime P hP hK I).symm

omit [LocallyCompactSpace alpha] in
/-- Uniqueness: a finite kernel into continuous paths with the finite-dimensional distributions of
`P` is the continuous-path process of `P`.  Only rational times are read off the hypothesis, so
neither Feller continuity nor local compactness is used. -/
theorem IsConservative.eq_continuousProcess_of_map_finiteEvaluation
    (hK : P.KolmogorovRegular hP) (Q : Kernel alpha (ContinuousPath alpha)) [IsFiniteKernel Q]
    (hQ : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I) :
    Q = continuousProcess P hP :=
  IsConservative.eq_continuousProcess_of_map_finiteEvaluation_denseTime P hP hK Q fun I ↦
    hQ (denseTimePhysicalSet I)










end


end SubMarkovKernelSemigroup

end MarkovProcess


/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The one-dimensional heat semigroup and its continuous-path process

The transition semigroup on the real line whose kernel at time `t` is the Gaussian law with mean
the starting point and variance `t`.  It is conservative, Feller, and satisfies the Kolmogorov
moment criterion with exponents `p = 4`, `q = 2` and the fourth moment of the standard Gaussian as
constant, so the existence-and-uniqueness theorem of `MarkovProcess.Main` applies to it.  The
process it produces is named `brownianMotion`.

Main results:

* `heatSemigroup`, `heatSemigroup_apply`: the semigroup and its Gaussian transition measures.
* `isConservative_heatSemigroup`: no mass is lost.
* `kernelIntegral_heatSemigroup`: the scaling representation of the transition operator.
* `isFellerKernelSemigroup_heatSemigroup`: the Feller property.
* `heatResolvent`: its positive contractive `C₀` resolvent.
* `heatExhaustion`: the explicit exhaustion `x ↦ 1 / (1 + |x|)`.
* `hasKolmogorovMoments_heatSemigroup`: the intrinsic Kolmogorov moment bound.
* `existsUnique_continuousProcess_heatSemigroup`: the main theorem, applied.
* `brownianMotion`, `brownianMotion_map_eval`, `brownianMotion_map_finsetEvaluation`: the
  continuous-path process and its finite-dimensional distributions.

Only one space dimension is treated: the multidimensional heat semigroup is not constructed here.
Nothing in this file asserts independence of increments; that is proved in
`MarkovProcess.Examples.BrownianMotion`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal ZeroAtInfty

namespace MarkovProcess

noncomputable section

section Gaussian





end Gaussian

section Definition





















end Definition

section Feller





















end Feller

section OnePointExhaustion













end OnePointExhaustion

section Moments











end Moments

section Process

/-- The heat semigroup is Kolmogorov regular, by its moment bound. -/
theorem kolmogorovRegular_heatSemigroup :
    heatSemigroup.KolmogorovRegular isConservative_heatSemigroup :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    isConservative_heatSemigroup p2m_embedded_d699d49b7a4121f2













end Process

end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The one-dimensional heat semigroup and its continuous-path process

The transition semigroup on the real line whose kernel at time `t` is the Gaussian law with mean
the starting point and variance `t`.  It is conservative, Feller, and satisfies the Kolmogorov
moment criterion with exponents `p = 4`, `q = 2` and the fourth moment of the standard Gaussian as
constant, so the existence-and-uniqueness theorem of `MarkovProcess.Main` applies to it.  The
process it produces is named `brownianMotion`.

Main results:

* `heatSemigroup`, `heatSemigroup_apply`: the semigroup and its Gaussian transition measures.
* `isConservative_heatSemigroup`: no mass is lost.
* `kernelIntegral_heatSemigroup`: the scaling representation of the transition operator.
* `isFellerKernelSemigroup_heatSemigroup`: the Feller property.
* `heatResolvent`: its positive contractive `C₀` resolvent.
* `heatExhaustion`: the explicit exhaustion `x ↦ 1 / (1 + |x|)`.
* `hasKolmogorovMoments_heatSemigroup`: the intrinsic Kolmogorov moment bound.
* `existsUnique_continuousProcess_heatSemigroup`: the main theorem, applied.
* `brownianMotion`, `brownianMotion_map_eval`, `brownianMotion_map_finsetEvaluation`: the
  continuous-path process and its finite-dimensional distributions.

Only one space dimension is treated: the multidimensional heat semigroup is not constructed here.
Nothing in this file asserts independence of increments; that is proved in
`MarkovProcess.Examples.BrownianMotion`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal ZeroAtInfty





















namespace MarkovProcess

end MarkovProcess
open MarkovProcess
theorem solution (Q : Kernel ℝ (ContinuousPath ℝ))
    [IsFiniteKernel Q]
    (hQ : ∀ I : Finset NNReal,
      Q.map (ContinuousPath.finsetEvaluation I) =
        SubMarkovKernelSemigroup.finiteSetKernel heatSemigroup I) :
    Q = brownianMotion :=
  SubMarkovKernelSemigroup.IsConservative.eq_continuousProcess_of_map_finiteEvaluation
    heatSemigroup isConservative_heatSemigroup kolmogorovRegular_heatSemigroup Q hQ

#print axioms solution


