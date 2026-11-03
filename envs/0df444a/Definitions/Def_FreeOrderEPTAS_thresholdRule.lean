-- Prove2me | Definitions.Def_FreeOrderEPTAS_thresholdRule
-- name    : FreeOrderEPTAS_thresholdRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:02.126902+00:00
-- url     : https://prove2.me/theorems/05283d91-c6fe-4eef-897a-5517e5a885cc
-- title:
--   The threshold stopping rule
-- statement:
--   The stopping rule behind the dynamic program of p.17: on the permutation $\sigma$, stop at time $t$ if and only if
--   $$X_{\sigma(t)}\ge R_{t+1}.$$
--   It is the rule that attains $V(\sigma)$. See the milestone `value_eq_recursion`.
--
--   **Formalization Note** The decision reads the last observed value, and measurability is proved in the definition.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, p.17, the dynamic program

import Mathlib
import Definitions.Def_FreeOrderEPTAS_StoppingRule
import Definitions.Def_FreeOrderEPTAS_R

namespace FreeOrderEPTAS

/-- The optimal rule behind the dynamic program of p.17 (arXiv:2007.13121v3): stop at time `t` iff
the value just observed is at least the continuation value `R_{t+1}`. -/
noncomputable def thresholdRule {n : ℕ} (I : Instance n) (σ : Equiv.Perm (Fin n)) :
    StoppingRule n where
  stop t obs := decide (R I σ (t.val + 1) ≤ obs (Fin.last t.val))
  measurable_stop t := by
    refine measurable_to_bool ?_
    have : (fun obs : Fin (t.val + 1) → ℝ => decide (R I σ (t.val + 1) ≤ obs (Fin.last t.val))) ⁻¹'
        {true} = {obs | R I σ (t.val + 1) ≤ obs (Fin.last t.val)} := by
      ext obs; simp
    rw [this]
    exact measurableSet_le measurable_const (measurable_pi_apply _)

end FreeOrderEPTAS


