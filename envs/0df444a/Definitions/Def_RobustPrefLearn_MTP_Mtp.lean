-- Prove2me | Definitions.Def_RobustPrefLearn_MTP_Mtp
-- name    : RobustPrefLearn_MTP_Mtp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:10.416341+00:00
-- url     : https://prove2.me/theorems/e75a3089-7505-47d1-a533-e694d066afce
-- title:
--   Algorithm 1, p. 19 — the Myopic Tracking Policy (MLE over OA rankings, generalized log-likelihood stopping rule, display of top-n sets with probabilities λ^OA_*)
-- statement:
--   This file defines the **Myopic Tracking Policy** (MTP) of Algorithm 1, with threshold $\beta$ and initial display set $S_1$.
--
--   - **Step 0.** The first consumer is shown $S_1$.
--   - **Step 1 (MLE).** Given $H_t$ ($t\ge1$), compute the OA rankings $\sigma$ that maximize the log-likelihood $\sum_{\ell=1}^t\log f^{\mathrm{OA}}_\sigma(X_\ell|S_\ell)$, and pick one, $f^{\mathrm{OA}}_t$, uniformly at random among the maximizers.
--   - **Step 2 (stopping).** With the log-likelihood ratio $L^{f,\bar f}_t=\sum_{\ell=1}^t\log\bigl(f(X_\ell|S_\ell)/\bar f(X_\ell|S_\ell)\bigr)$ of (8), stop at time $t$ if
--   $$\mathcal L_t=\min_{\bar f\in\overline{\mathcal M}^{\mathrm{OA}}_p(f^{\mathrm{OA}}_t)} L^{f^{\mathrm{OA}}_t,\bar f}_t\ \ge\ \beta,$$
--   and select the top-ranked version of $f^{\mathrm{OA}}_t$.
--   - **Step 3 (display).** Otherwise show the next consumer the set $S_{f^{\mathrm{OA}}_t}(n)$ of the top-$n$ versions of $f^{\mathrm{OA}}_t$ with probability $\lambda^{\mathrm{OA}}_*([n])$, $n=2,\dots,K$.
--
--   MTP is the policy whose worst-case asymptotic optimality is the goal of the mission.
--
--   **Formalization Note** The uniform tie-break of Step 1 enters the display rule as the uniform mixture over the MLE set. The stopping rule is "some MLE ranking $\sigma$ has log-likelihood gap at least $\beta$ over every ranking with a different top", and the selection is the top version of a chosen MLE ranking. For $\beta>0$ these do not depend on the tie-break: if two MLE rankings have different tops then $\mathcal L_t\le0<\beta$ for whichever is drawn, and if all have the same top they all give the same $\mathcal L_t$. MTP never stops at $t=0$. The definition needs $K\ge1$ (`[NeZero K]`) to name the top rank.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 18, (8) and S_f(k); p. 19, Algorithm 1 (MLE), (L)

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Policy

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-! # Algorithm 1 (p. 19): the Myopic Tracking Policy. -/

/-- The OA log-likelihood `∑_{ℓ ≤ t} log f^OA_σ(X_ℓ|S_ℓ)` of a history (the objective of
(MLE)). -/
noncomputable def loglikOA {K : ℕ} (p : ℝ) (σ : Equiv.Perm (Fin K)) (h : List (Step K)) : ℝ :=
  (h.map (fun x => Real.log (oa p σ x.1 x.2))).sum

/-- The (MLE) set: the rankings `σ` whose OA preference `f^OA_σ` maximizes the log-likelihood
of the history. -/
noncomputable def mle {K : ℕ} (p : ℝ) (h : List (Step K)) : Finset (Equiv.Perm (Fin K)) :=
  Finset.univ.filter (fun σ => ∀ σ' : Equiv.Perm (Fin K), loglikOA p σ' h ≤ loglikOA p σ h)

/-- The rankings `σ` and `σ'` have different top-ranked versions. -/
def diffTop {K : ℕ} (σ σ' : Equiv.Perm (Fin K)) : Prop :=
  ∀ k : Fin K, (σ k).val = 0 → (σ' k).val ≠ 0

/-- `S_f(n)` (p. 18) for the ranking `σ`: the set of the top-`n` versions. -/
def topSet {K : ℕ} (σ : Equiv.Perm (Fin K)) (n : ℕ) : Finset (Fin K) :=
  Finset.univ.filter (fun X => (σ X).val < n)

open Classical in
/-- Algorithm 1 (p. 19), the Myopic Tracking Policy with threshold `β` and initial display set
`S₁`:
* Step 0: after the empty history the display set is `S₁`;
* Step 1: `f^OA_t` is drawn uniformly at random from the (MLE) set;
* Step 2: stop at `t ≥ 1` when `𝓛_t = min_{f̄ ∈ M̄^OA_p(f^OA_t)} L^{f^OA_t, f̄}_t ≥ β`, and select
  the top-ranked version of `f^OA_t`;
* Step 3: otherwise display `Ŝ_t(n) = S_{f^OA_t}(n)` with probability `λ^OA_*([n])`,
  `n = 2, …, K`.
The uniform tie-break enters the display rule as the uniform mixture over the (MLE) set. For
`β > 0` the stopping decision and the selected version do not depend on the tie-break, so they are
written with "some MLE ranking". -/
noncomputable def mtp {K : ℕ} [NeZero K] (p : ℝ) (S1 : DS K) (β : ℝ) : Policy K where
  disp h S :=
    if h = [] then (if S = S1 then 1 else 0)
    else ((mle p h).card : ℝ≥0∞)⁻¹ * ∑ σ ∈ mle p h, ∑ n ∈ Finset.Icc 2 K,
      (if S.1 = topSet σ n then
        ENNReal.ofReal (lamStar K p n / ∑ m ∈ Finset.Icc 2 K, lamStar K p m) else 0)
  stop h :=
    h ≠ [] ∧ ∃ σ ∈ mle p h, ∀ σ' : Equiv.Perm (Fin K), diffTop σ σ' →
      β ≤ loglikOA p σ h - loglikOA p σ' h
  select h :=
    if hne : (mle p h).Nonempty then hne.choose.symm 0 else 0

end RobustPrefLearn.MTP


