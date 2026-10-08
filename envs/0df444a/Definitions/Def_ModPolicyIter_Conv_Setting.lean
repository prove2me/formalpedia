-- Prove2me | Definitions.Def_ModPolicyIter_Conv_Setting
-- name    : ModPolicyIter_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T13:33:00.324739+00:00
-- url     : https://prove2.me/theorems/878bb66d-ae26-44f5-ae15-e78aa57a5d86
-- title:
--   §3–§4, pp. 1128–1130 — the truncated Neumann series A^k, the recursion (4), U^k and V_B
-- statement:
--   The objects of modified policy iteration, §3–§4 of Puterman and Shin, built on the model of §2 (transition operators $P_i$, rewards $c_i$, discount $\lambda\in[0,1)$, the space $V$ and the operator $B$).
--
--   1. The **truncated Neumann series** of order $k\ge 0$ of policy $i$:
--   $$A^k_iw=\sum_{j=0}^{k}(\lambda P_i)^jw,\qquad A^0_i=I.$$
--   2. A **run of modified policy iteration of order $k$**, recursion (4): sequences $v_0,v_1,\dots$ of functions and $P_0,P_1,\dots$ of policies such that $P_n$ attains the maximum in (1) at $v_n$ and
--   $$v_{n+1}=v_n+A^k_{P_n}Bv_n .$$
--   3. The operators of §4,
--   $$U^kv=\max_{i}\Big\{\sum_{j=0}^{k}(\lambda P_i)^jc_i+(\lambda P_i)^{k+1}v\Big\},$$
--   the maximum taken pointwise as a supremum over policies; $U^0$ is the successive-approximations (value-iteration) operator.
--   4. The set $V_B=\{v\in V: Bv\ge 0\}$.
--
--   For $k=0$ the recursion is value iteration; as $k\to\infty$ it approaches policy iteration.
--
--   **Formalization Note** The page writes (4) with $A^k_{n+1}$, the series of the maximizer at $v_n$ under policy-iteration indexing, and the proofs with $A^k_n$; both mean that the step from $v_n$ uses a maximizer at $v_n$, which is how the run is defined. The pair (policy, sequence) is recorded explicitly rather than chosen inside the definition.
-- source:
--   Puterman and Shin, Modified policy iteration algorithms for discounted Markov decision problems, Management Science 24 (1978), DOI 10.1287/mnsc.24.11.1127, pp. 1128–1130, §3 (A^k and (4)), §4 (U^k, I + A^kB and V_B)

import Mathlib
import Definitions.Def_ModPolicyIter_Conv_Model

open MeasureTheory ProbabilityTheory

namespace ModPolicyIter.Conv

variable {S : Type*} [MeasurableSpace S] {ι : Type*}

/-- The truncated Neumann series `A^k_P w = Σ_{i=0}^k (λP)^i w` of policy `i` (§3, p. 1128).
`A^0 = I`. -/
noncomputable def Apow (m : Model S ι) (i : ι) (k : ℕ) (w : S → ℝ) : S → ℝ :=
  fun s => ∑ j ∈ Finset.range (k + 1), m.lam ^ j * (Pop m i)^[j] w s

/-- A run of modified policy iteration of order `k`, recursion (4) (§3, p. 1128):
`v (n+1) = v n + A^k_{P_n} B (v n)`, where the policy `pol n` used at step `n` attains the
maximum in (1) at `v n`. -/
def IsRun (m : Model S ι) (k : ℕ) (v : ℕ → S → ℝ) (pol : ℕ → ι) : Prop :=
  ∀ n, Attains m (v n) (pol n) ∧ v (n + 1) = v n + Apow m (pol n) k (B m (v n))

/-- The operator `U^k v = Max_P {Σ_{i=0}^k (λP)^i c_P + (λP)^{k+1} v}` (§4, p. 1129), the
maximum taken pointwise as a supremum over policies. -/
noncomputable def U (m : Model S ι) (k : ℕ) (v : S → ℝ) : S → ℝ :=
  fun s => ⨆ i, ((∑ j ∈ Finset.range (k + 1), m.lam ^ j * (Pop m i)^[j] (m.c i) s)
    + m.lam ^ (k + 1) * (Pop m i)^[k + 1] v s)

/-- `V_B = {v ∈ V : Bv ≥ 0}` (§4, p. 1130). -/
def VB (m : Model S ι) : Set (S → ℝ) := {v | IsBM v ∧ ∀ s, 0 ≤ B m v s}

end ModPolicyIter.Conv


