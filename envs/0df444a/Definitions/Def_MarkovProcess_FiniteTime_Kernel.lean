-- Prove2me | Definitions.Def_MarkovProcess_FiniteTime_Kernel
-- name    : MarkovProcess_FiniteTime_Kernel
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:46:39.972243+00:00
-- url     : https://prove2.me/theorems/80ceb56f-3e9e-49bf-aa34-504479a34419
-- title:
--   MarkovProcess definitions: FiniteTime.Kernel
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.FiniteTime.Kernel`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/Kernel.lean#L1-L124

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# Finite-time kernels on strictly ordered time families

A conservative sub-Markov kernel semigroup determines probability kernels on finite coordinate
spaces.  The construction itself does not use a conservativity witness: it recursively samples the
first observation and then the relative tail.  Conservativity is used only to prove that the
resulting kernels are Markov kernels.

This file constructs finite-dimensional kernels only.  It makes no path-space, projectivity,
conservativity, or stochastic-process existence claim beyond the explicitly stated results.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess

/-- Prepending one coordinate to a finite coordinate path is measurable. -/
theorem measurable_finCons {α : Type*} [MeasurableSpace α] {n : ℕ} :
    Measurable (fun z : α × (Fin n → α) ↦
      @Fin.cons n (fun _ : Fin (n + 1) ↦ α) z.1 z.2) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simpa only [Fin.cons_zero] using (measurable_fst : Measurable (Prod.fst : α × (Fin n → α) → α))
  · simpa only [Fin.cons_succ] using!
      (measurable_pi_apply j).comp (measurable_snd : Measurable (Prod.snd : α × (Fin n → α) → _))

namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]

/-- The finite-time kernel obtained by recursively sampling a strictly ordered family of times. -/
noncomputable def finiteTimeKernel (P : SubMarkovKernelSemigroup α) :
    {n : ℕ} → FiniteOrderedTimes n → Kernel α (Fin n → α)
  | 0, _ => Kernel.const α (Measure.dirac (FiniteOrderedTimes.emptyPath α))
  | n + 1, times =>
      Kernel.mapOfMeasurable
        (P (times 0) ⊗ₖ Kernel.prodMkLeft α (finiteTimeKernel P times.relativeTail))
        (fun z ↦ @Fin.cons n (fun _ : Fin (n + 1) ↦ α) z.1 z.2) measurable_finCons

/-- At the empty time family, the finite-time kernel is the constant Dirac mass at the empty
path. -/
@[simp]
theorem finiteTimeKernel_zero (P : SubMarkovKernelSemigroup α)
    (times : FiniteOrderedTimes 0) :
    finiteTimeKernel P times =
      Kernel.const α (Measure.dirac (FiniteOrderedTimes.emptyPath α)) :=
  rfl

/-- The successor finite-time kernel first samples at the first time, then samples the relative
tail from that state. -/
@[simp]
theorem finiteTimeKernel_succ (P : SubMarkovKernelSemigroup α) {n : ℕ}
    (times : FiniteOrderedTimes (n + 1)) :
    finiteTimeKernel P times =
      Kernel.mapOfMeasurable
        (P (times 0) ⊗ₖ Kernel.prodMkLeft α (finiteTimeKernel P times.relativeTail))
        (fun z ↦ @Fin.cons n (fun _ : Fin (n + 1) ↦ α) z.1 z.2)
        measurable_finCons :=
  rfl

/-- Under conservativity, every finite-time kernel is a Markov kernel. -/
theorem IsConservative.isMarkovKernel_finiteTimeKernel
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative) {n : ℕ}
    (times : FiniteOrderedTimes n) : IsMarkovKernel (finiteTimeKernel P times) := by
  induction n with
  | zero =>
      rw [finiteTimeKernel_zero]
      infer_instance
  | succ n ih =>
      let : IsMarkovKernel (P (times 0)) := hP.isMarkovKernel (times 0)
      let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) := ih times.relativeTail
      rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
      exact Kernel.IsMarkovKernel.map _ measurable_finCons

/-- The finite-time law at a starting state. -/
noncomputable def finiteTimeLaw (P : SubMarkovKernelSemigroup α) {n : ℕ}
    (times : FiniteOrderedTimes n) (x : α) : Measure (Fin n → α) :=
  finiteTimeKernel P times x





end SubMarkovKernelSemigroup

end MarkovProcess


