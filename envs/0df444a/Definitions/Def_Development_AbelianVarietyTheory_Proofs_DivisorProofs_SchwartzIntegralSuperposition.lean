-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzIntegralSuperposition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:22.842903+00:00
-- url     : https://prove2.me/theorems/5e418142-d30f-4e1e-91ce-ea823a167d7a
-- title:
--   Schwartz Integral Superposition
-- statement:
--   Definitions and structural lemmas for Schwartz Integral Superposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzIntegralSuperposition.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
namespace GlobalTheory
namespace SchwartzIntegralExchange
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
noncomputable def wtFun (k n : ℕ) (w : SchwartzMap E ℂ) :
    BoundedContinuousFunction E (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x)
    ((continuous_norm.pow k).smul ((w.smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)))
    (SchwartzMap.seminorm ℂ k n w)
    (fun x => by
      rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      exact SchwartzMap.le_seminorm ℂ k n w x)
theorem wtFun_apply (k n : ℕ) (w : SchwartzMap E ℂ) (x : E) :
    wtFun k n w x = (‖x‖ ^ k : ℝ) • iteratedFDeriv ℝ n w x := rfl
theorem norm_wtFun_le (k n : ℕ) (w : SchwartzMap E ℂ) :
    ‖wtFun k n w‖ ≤ SchwartzMap.seminorm ℂ k n w :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (apply_nonneg _ _) _
noncomputable def wt (k n : ℕ) : SchwartzMap E ℂ →L[ℂ]
    BoundedContinuousFunction E (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (wtFun k n)
    (fun f g => by
      ext1 x
      have hf : ContDiffAt ℝ n f x := ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      have hg : ContDiffAt ℝ n g x := ((g.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      rw [BoundedContinuousFunction.add_apply, wtFun_apply, wtFun_apply, wtFun_apply, ← smul_add,
        ← iteratedFDeriv_add_apply hf hg]
      rfl)
    (fun a f => by
      ext1 x
      have hf : ContDiffAt ℝ n f x := ((f.smooth ⊤).of_le (by exact_mod_cast le_top)).contDiffAt
      rw [BoundedContinuousFunction.smul_apply, wtFun_apply, wtFun_apply, RingHom.id_apply,
        smul_comm a, ← iteratedFDeriv_const_smul_apply hf]
      rfl)
    ⟨{(k, n)}, 1, zero_le_one, fun f => by
      simpa using norm_wtFun_le k n f⟩
variable {P : Type} [TopologicalSpace P] [SecondCountableTopology P] [MeasurableSpace P]
  [OpensMeasurableSpace P] {ν : Measure P} {Φ : P → SchwartzMap E ℂ} {c : P → ℂ}
end SchwartzIntegralExchange
end GlobalTheory


