-- Prove2me | Definitions.Def_Spectral_PVM_Integral
-- name    : Spectral_PVM_Integral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:54:39.016364+00:00
-- url     : https://prove2.me/theorems/b79165a8-fab6-4b26-b02c-30a9629b9368
-- title:
--   Integral
-- statement:
--   Definitions and structural lemmas for Integral, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/PVM/Integral.lean

import Definitions.Def_Spectral_PVM_Basic
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Topology.UniformSpace.Dini
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
noncomputable def PVM.simpleIntegral (E_pvm : PVM E)
    (f : SimpleFunc ℝ ℂ) : E →L[ℂ] E :=
  ∑ z ∈ f.range, z • E_pvm.proj (f ⁻¹' {z})
noncomputable def nearestError (e : ℕ → ℂ) : ℕ → ℂ → ℝ
  | 0 => fun z => dist (e 0) z
  | n + 1 => fun z => min (dist (e (n + 1)) z) (nearestError e n z)
theorem bound_nonneg {f : ℝ → ℂ} {C : ℝ} (hbdd : ∀ t, ‖f t‖ ≤ C) : 0 ≤ C :=
  (norm_nonneg (f 0)).trans (hbdd 0)
noncomputable def boundedApprox (f : ℝ → ℂ) (hf : Measurable f)
    (C : ℝ) (hbdd : ∀ t, ‖f t‖ ≤ C) (n : ℕ) : SimpleFunc ℝ ℂ :=
  SimpleFunc.approxOn f hf (Metric.closedBall 0 C) 0
    (Metric.mem_closedBall.mpr (by rw [dist_self]; exact bound_nonneg hbdd)) n
noncomputable def PVM.integral (E_pvm : PVM E)
    (f : ℝ → ℂ) (hf : Measurable f) (hbdd : ∃ C, ∀ t, ‖f t‖ ≤ C) :
    E →L[ℂ] E :=
  Filter.limUnder Filter.atTop (fun n => E_pvm.simpleIntegral
    (boundedApprox f hf (Classical.choose hbdd) (Classical.choose_spec hbdd) n))


