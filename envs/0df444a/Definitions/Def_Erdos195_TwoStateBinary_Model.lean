-- Prove2me | Definitions.Def_Erdos195_TwoStateBinary_Model
-- name    : Erdos195_TwoStateBinary_Model
-- status  : Definition
-- author  : @xwh
-- created : 2026-10-23T09:37:20.708833+00:00
-- url     : https://prove2.me/theorems/6bd956ab-e884-407e-89bc-c7a55aa5785e
-- title:
--   Two-state binary digit transport with arbitrary integer state coefficients
-- statement:
--   Let $S=\{0,1\}$ be a two-element state set, $a:S\to\mathbb Z$ arbitrary integer coefficients, and $\delta_0,\delta_1:S\to S$ arbitrary transitions. Define integer-valued maps $G_s$ on nonnegative integers by
--   $$G_s(0)=0,\qquad G_s(2n)=2G_{\delta_0(s)}(n),\qquad G_s(2n+1)=2G_{\delta_1(s)}(n)+a_s.$$
--   The exact terminating recursion reads binary digits from the least significant end; the next coefficient may depend on the lower digit prefix through the state. No oddness, reachability, boundedness, injectivity, surjectivity or progression-avoidance assumption is built into the definition. This is the minimal interface for one two-state construction-family obstruction in the Erdős195 investigation.
-- source:
--   Independent research definition, exact recurrence from the kernel-checked two-state transport investigation of public Erdős195 mission49a38d9f-e723-48b5-9209-130dea45c67b. Contextual actual permutation: Ho https://arxiv.org/abs/2609.12780v1. The new state transport and obstruction are not attributed to that paper; the actual-Ho application is a separately checked companion.

import Mathlib

namespace Erdos195.NonlinearStateResearch

/-- A coefficient may depend on the already-read lower binary prefix. -/
def stateValue (a : Bool → ℤ) (δ₀ δ₁ : Bool → Bool) (s : Bool) (n : ℕ) : ℤ :=
  if hn : n = 0 then 0 else
    if n % 2 = 0 then 2 * stateValue a δ₀ δ₁ (δ₀ s) (n / 2)
    else 2 * stateValue a δ₀ δ₁ (δ₁ s) (n / 2) + a s
termination_by n
decreasing_by all_goals omega

end Erdos195.NonlinearStateResearch


