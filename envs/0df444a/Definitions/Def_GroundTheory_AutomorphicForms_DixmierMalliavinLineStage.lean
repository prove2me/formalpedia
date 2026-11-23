-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
-- name    : GroundTheory_AutomorphicForms_DixmierMalliavinLineStage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:16:19.021804+00:00
-- url     : https://prove2.me/theorems/90689814-af17-44ef-93bc-ca9f69baa8aa
-- title:
--   Dixmier Malliavin Line Stage
-- statement:
--   Definitions and structural lemmas for Dixmier Malliavin Line Stage, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinLineStage.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise
set_option linter.unusedSectionVars false
noncomputable section
namespace LineKernel
def coef (a : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, p => if p = 0 then 1 else 0
  | n + 1, 0 => coef a n 0
  | n + 1, p + 1 => coef a n (p + 1) + coef a n p / a n
def sc (a : ℕ → ℝ) (n p : ℕ) : ℂ := (-1) ^ p * (coef a n p : ℂ)
def opT (a : ℕ → ℝ) (n : ℕ) (F : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑ p ∈ Finset.range (n + 1), sc a n p * iteratedDeriv p F u
def Kc (a r : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => kern (a 0) (r 0)
  | n + 1 => Kc a r n ⋆[mul ℝ ℝ] kern (a (n + 1)) (r (n + 1))
def Rs (r : ℕ → ℝ) (n : ℕ) : ℝ := ∑ j ∈ Finset.range (n + 1), 2 * r j
def KC (a r : ℕ → ℝ) (n : ℕ) : ℝ → ℂ := fun t => (Kc a r n t : ℂ)
def kC (a r : ℕ → ℝ) (j : ℕ) : ℝ → ℂ := fun t => (kern (a j) (r j) t : ℂ)
def ηC (a r : ℕ → ℝ) (j : ℕ) : ℝ → ℂ := fun t => (rem (a j) (r j) t : ℂ)
def ρ (a r : ℕ → ℝ) : ℕ → ℝ → ℂ
  | 0 => ηC a r 0
  | n + 1 => fun u => ∑ p ∈ Finset.range (n + 2),
      (coef a (n + 1) p : ℂ) * iteratedDeriv p (KC a r n ⋆[mul ℂ ℂ] ηC a r (n + 1)) u
section Kernels
variable {a r : ℕ → ℝ} (ha : ∀ j, 0 < a j) (hr : ∀ j, 0 < r j)
include ha hr
end Kernels
end LineKernel
end
end GroundTheory.Automorphic


