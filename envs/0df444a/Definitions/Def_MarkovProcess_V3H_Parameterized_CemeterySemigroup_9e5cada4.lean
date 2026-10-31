-- Prove2me | Definitions.Def_MarkovProcess_V3H_Parameterized_CemeterySemigroup_9e5cada4
-- name    : MarkovProcess_V3H_Parameterized_CemeterySemigroup_9e5cada4
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:34:59.763727+00:00
-- url     : https://prove2.me/theorems/a5b0feab-1b51-4e29-9527-3fe05e896965
-- title:
--   MarkovProcess: MarkovProcess_V3H_Parameterized_CemeterySemigroup_9e5cada4
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeteryExtension_b0b7bd17
import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeterySemigroup_149c26e5
import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Parameterized_Semigroup_5f8b28ce
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized cemetery-extension semigroups

This file extends a jointly measurable family of sub-Markov semigroups by one absorbing
cemetery state.  The construction is jointly measurable in the parameter, time, and state.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

variable {Theta alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]

/-- The jointly measurable conservative cemetery extension of a parameterized sub-Markov
kernel semigroup. -/
def cemeterySemigroup (P : ParameterizedSubMarkovKernelSemigroup Theta alpha) :
    ParameterizedSubMarkovKernelSemigroup Theta (Cemetery alpha) where
  kernel theta t := Kernel.cemeteryExtension (P theta t)
  measurable_kernel := by
    let e : Theta × (NNReal × Cemetery alpha) ≃ᵐ
        ((Theta × NNReal) × alpha) ⊕ ((Theta × NNReal) × Unit) :=
      (MeasurableEquiv.prodAssoc :
        ((Theta × NNReal) × Cemetery alpha) ≃ᵐ Theta × (NNReal × Cemetery alpha)).symm.trans
        (MeasurableEquiv.prodSumDistrib (Theta × NNReal) alpha Unit)
    apply e.symm.measurable_comp_iff.1
    apply measurable_fun_sum
    · have hkernel : Measurable fun q : (Theta × NNReal) × alpha ↦
          P q.1.1 q.1.2 q.2 :=
        P.measurable_kernel.comp
          (MeasurableEquiv.prodAssoc :
            ((Theta × NNReal) × alpha) ≃ᵐ Theta × (NNReal × alpha)).measurable
      exact
        (((Measure.measurable_map Cemetery.alive measurable_inl).comp hkernel).add
          ((measurable_const.sub
              ((Measure.measurable_coe MeasurableSet.univ).comp hkernel)).smul_measure
            (Measure.dirac Cemetery.delta)))
    · exact measurable_const
  kernel_zero theta := by
    rw [P.zero, Kernel.cemeteryExtension_id]
  kernel_add theta s t := by
    rw [P.add]
    exact Kernel.cemeteryExtension_comp (P theta t) (P theta s)
      (P.isSubMarkovKernel theta t) (P.isSubMarkovKernel theta s)
  isSubMarkovKernel theta t := by
    let : IsMarkovKernel (Kernel.cemeteryExtension (P theta t)) :=
      Kernel.isMarkovKernel_cemeteryExtension (P theta t) (P.isSubMarkovKernel theta t)
    exact IsSubMarkovKernel.of_isMarkovKernel _

variable (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)



/-- A fixed-parameter slice of the parameterized extension is exactly the ordinary cemetery
extension of that parameter slice. -/
theorem toSubMarkovKernelSemigroup_cemeterySemigroup (theta : Theta) :
    P.cemeterySemigroup.toSubMarkovKernelSemigroup theta =
      (P.toSubMarkovKernelSemigroup theta).cemeterySemigroup := by
  apply SubMarkovKernelSemigroup.ext
  intro t
  rfl

/-- Every fixed-parameter slice of the cemetery extension is conservative. -/
theorem isConservative_cemeterySemigroup (theta : Theta) :
    (P.cemeterySemigroup.toSubMarkovKernelSemigroup theta).IsConservative := by
  rw [P.toSubMarkovKernelSemigroup_cemeterySemigroup theta]
  exact (P.toSubMarkovKernelSemigroup theta).isConservative_cemeterySemigroup

end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


