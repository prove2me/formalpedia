-- Prove2me | Definitions.Def_WeightedMajority_General_WMGRun
-- name    : WeightedMajority_General_WMGRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:48.543916+00:00
-- url     : https://prove2.me/theorems/3aa56dca-a5e7-49d5-8e3f-7a47fe5382bb
-- title:
--   Runs of the master algorithm WMG with pool predictions in [0,1] (Section 5)
-- statement:
--   This definition fixes the algorithm WMG of Littlestone and Warmuth (§5), a master algorithm that combines the predictions of a pool of $n$ prediction algorithms, each predicting a number in $[0,1]$, into a binary prediction.
--
--   Consider a sequence of $T$ trials, indexed $k = 0, \dots, T-1$, and a nonempty pool indexed by $i = 1, \dots, n$. In trial $k$ the pool member $i$ predicts $x_{k,i} \in [0,1]$, and the label of the trial is $\rho_k \in \{0,1\}$. The master keeps a weight $w_{k,i}$ for each member at the beginning of trial $k$; the initial weights $w_{0,i}$ are positive, and $w_{T,i}$ are the weights after the last trial. Write
--
--   $$
--   s_k = \sum_{i=1}^n w_{k,i}, \qquad \gamma_k = \frac{\sum_{i=1}^n w_{k,i}\, x_{k,i}}{s_k},
--   $$
--
--   so that $w_{\mathrm{init}} = s_0$ and $w_{\mathrm{fin}} = s_T$.
--
--   A **run of WMG with parameter $0 \le \beta < 1$** consists of predictions $\lambda_k$, update flags and update factors $F_{k,i}$ such that:
--
--   1. $\lambda_k \in \{0,1\}$, with $\lambda_k = 1$ when $\gamma_k > 1/2$ and $\lambda_k = 0$ when $\gamma_k < 1/2$; when $\gamma_k = 1/2$ either prediction is allowed;
--   2. an update step is executed in every trial in which $\lambda_k \ne \rho_k$ (a mistake), and possibly in further trials; in particular both versions of WMG, updating in every trial or only in mistake trials, are runs;
--   3. in an update trial each weight is multiplied by a factor satisfying
--   $$
--   \beta^{|x_{k,i} - \rho_k|} \le F_{k,i} \le 1 - (1-\beta)\,|x_{k,i} - \rho_k|, \qquad w_{k+1,i} = F_{k,i}\, w_{k,i},
--   $$
--   with the convention $0^0 = 1$ (inequality (5.1));
--   4. in a trial without an update step the weights are unchanged.
--
--   The number of mistakes $m$ is the number of trials $k$ with $\lambda_k \ne \rho_k$.
--
--   The definition is the model of Theorem 5.1 and of the two steps of its proofs. When the pool predictions are themselves binary, WMG coincides with the algorithm WM of §1.
--
--   **Formalization Note** The pool has at least one member. The trials are all trials of the sequence, not only the update trials, and the update criterion is an update flag forced on every mistake trial (footnote 8 of the paper). The factor $F_{k,i}$ is an arbitrary number in the interval (5.1) for each trial and member; the paper lets $F$ depend on $\beta$, $x_{k,i}$ and $\rho_k$, and every such choice is a run. The labels and predictions are real numbers constrained to $\{0,1\}$. If the total weight $s_k$ is $0$, Lean's convention $a/0 = 0$ gives $\gamma_k = 0$; the theorem hypotheses exclude this case when a logarithm or weight ratio is used. The power $\beta^{|x-\rho|}$ is the real power `Real.rpow`, for which $0^0 = 1$.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), pp. 232–233, Section 5 (Assumptions, Update Criteria, Prediction of WMC and WMG, Update step (5.1)), footnote 8

import Mathlib
import Definitions.Def_WeightedMajority_Basic_IsWMRun

namespace WeightedMajority.General

/-- The weighted average `γ` of the pool predictions in trial `k`:
`(∑ i, w_i x_i) / s`. If the total weight `s` is `0` this is Lean's `x / 0 = 0`. -/
noncomputable def gamma {n T : ℕ} (x : Fin T → Fin n → ℝ) (w : ℕ → Fin n → ℝ)
    (k : Fin T) : ℝ :=
  (∑ i : Fin n, w k.val i * x k i) / WeightedMajority.Basic.totalWeight w k.val

/-- The number `m` of trials in which the master prediction differs from the label. -/
noncomputable def mistakeCount {T : ℕ} (pred label : Fin T → ℝ) : ℕ :=
  (Finset.univ.filter (fun k => pred k ≠ label k)).card

/-- A run of the master algorithm WMG with parameter `β` on a pool of `n` algorithms and a
sequence of `T` trials (Littlestone–Warmuth 1994, §5, pp. 232–233).

* `x k i ∈ [0, 1]` is the prediction of pool member `i` in trial `k`, and `ρ k ∈ {0, 1}` the label;
* the pool is nonempty;
* the update parameter satisfies `0 ≤ β < 1`;
* `w k i` is the weight of member `i` at the beginning of trial `k` (`w T` are the final
  weights); the initial weights are positive;
* `pred k ∈ {0, 1}` is WMG's prediction: `1` if `γ > 1/2`, `0` if `γ < 1/2`, either if `γ = 1/2`;
* `upd k` records whether an update step is executed in trial `k`; it must hold in every trial in
  which WMG makes a mistake (it may hold in every trial, or in any further trials);
* in an update trial every weight is multiplied by a factor `F k i` with
  `β ^ |x - ρ| ≤ F ≤ 1 - (1 - β) |x - ρ|` (inequality (5.1), with `0 ^ 0 = 1`);
  in any other trial the weights are unchanged. -/
structure IsWMGRun {n T : ℕ} (β : ℝ) (x : Fin T → Fin n → ℝ) (ρ : Fin T → ℝ)
    (w : ℕ → Fin n → ℝ) (pred : Fin T → ℝ) (upd : Fin T → Bool) (F : Fin T → Fin n → ℝ) :
    Prop where
  pool_nonempty : 0 < n
  beta_nonneg : 0 ≤ β
  beta_lt_one : β < 1
  x_mem : ∀ k i, 0 ≤ x k i ∧ x k i ≤ 1
  label_binary : ∀ k, ρ k = 0 ∨ ρ k = 1
  initial_pos : ∀ i, 0 < w 0 i
  pred_binary : ∀ k, pred k = 0 ∨ pred k = 1
  pred_one : ∀ k, 1 / 2 < gamma x w k → pred k = 1
  pred_zero : ∀ k, gamma x w k < 1 / 2 → pred k = 0
  upd_of_mistake : ∀ k, pred k ≠ ρ k → upd k = true
  factor_lower : ∀ k i, upd k = true → β ^ |x k i - ρ k| ≤ F k i
  factor_upper : ∀ k i, upd k = true → F k i ≤ 1 - (1 - β) * |x k i - ρ k|
  update : ∀ k i, upd k = true → w (k.val + 1) i = F k i * w k.val i
  no_update : ∀ k i, upd k = false → w (k.val + 1) i = w k.val i

end WeightedMajority.General


