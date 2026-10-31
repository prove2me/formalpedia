-- Prove2me | Definitions.Def_MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
-- name    : MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:32:10.31823+00:00
-- url     : https://prove2.me/theorems/6ef1f9d3-d4a4-46c1-a257-f63d60fa5ef0
-- title:
--   MarkovProcess: MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Definitions.Def_MarkovProcess_V3H_Kernel_KernelSemigroup_26332261
import Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

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

/-- Under conservativity, every finite-time law is a probability measure. -/
theorem IsConservative.isProbabilityMeasure_finiteTimeLaw
    (P : SubMarkovKernelSemigroup α) (hP : P.IsConservative) {n : ℕ}
    (times : FiniteOrderedTimes n) (x : α) : IsProbabilityMeasure (finiteTimeLaw P times x) := by
  let : IsMarkovKernel (finiteTimeKernel P times) :=
    hP.isMarkovKernel_finiteTimeKernel P times
  exact IsMarkovKernel.isProbabilityMeasure x

/-- The unique coordinate of a singleton finite-time kernel has transition kernel `P` at that
time. -/
@[simp]
theorem p2m_embedded_5bab9ee57d353238 (P : SubMarkovKernelSemigroup α)
    (times : FiniteOrderedTimes 1) :
    (finiteTimeKernel P times).map (fun path ↦ path 0) = P (times 0) := by
  let : IsFiniteKernel (P (times 0)) := (P.isSubMarkovKernel (times 0)).isFiniteKernel
  let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) :=
    by rw [finiteTimeKernel_zero]; infer_instance
  rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map]
  rw [← Kernel.map_comp_right]
  · have hcomp :
        ((fun path : Fin 1 → α ↦ path 0) ∘
          fun z : α × (Fin 0 → α) ↦
            @Fin.cons 0 (fun _ : Fin 1 ↦ α) z.1 z.2) = Prod.fst := by
        funext z
        rfl
    rw [hcomp, ← Kernel.fst_eq]
    exact Kernel.fst_compProd _ _
  · exact measurable_finCons
  · exact measurable_pi_apply 0

end SubMarkovKernelSemigroup

end MarkovProcess


