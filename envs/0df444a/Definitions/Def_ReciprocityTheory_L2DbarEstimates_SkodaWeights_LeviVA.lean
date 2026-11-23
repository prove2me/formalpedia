-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
-- name    : ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:02.499846+00:00
-- url     : https://prove2.me/theorems/c3f18d81-14f7-40dc-b03d-afee7ae80b5c
-- title:
--   Levi VA
-- statement:
--   Definitions and structural lemmas for Levi VA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/LeviVA.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_SkodaWeightStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology Matrix
namespace ReciprocityTheory.L2DbarEstimates.H
open ReciprocityTheory.L2DbarEstimates
def LeviChainStatement : Prop :=
  ∀ (n : ℕ) (k : ℝ → ℝ) (v : V n → ℝ) (x : V n) (ξ : Fin n → ℂ),
    ContDiffAt ℝ 2 v x → ContDiffAt ℝ 2 k (v x) →
    leviV n (fun y => ((k (v y) : ℝ) : ℂ)) x ξ =
      ((deriv k (v x) : ℝ) : ℂ) * leviV n (fun y => ((v y : ℝ) : ℂ)) x ξ +
      ((deriv (deriv k) (v x) : ℝ) : ℂ) *
        ((Complex.normSq (∑ j, wd n j (fun y => ((v y : ℝ) : ℂ)) x * ξ j) : ℝ) : ℂ)
variable {n : ℕ}
noncomputable def wJac (n p : ℕ) (g : Fin p → V n → ℂ) (x : V n) : Matrix (Fin p) (Fin n) ℂ :=
  fun i k => wd n k (g i) x
def LeviLogNormSqStatement : Prop :=
  ∀ (n p : ℕ) (g : Fin p → V n → ℂ) (x : V n) (ξ : Fin n → ℂ),
    (∀ i, ContDiffAt ℂ 2 (g i) x) → (fun i => g i x) ≠ 0 →
    leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((sqNorm (projPerp (fun i => g i x) *ᵥ (wJac n p g x *ᵥ ξ)) / sqNorm (fun i => g i x) : ℝ) : ℂ)
end ReciprocityTheory.L2DbarEstimates.H


