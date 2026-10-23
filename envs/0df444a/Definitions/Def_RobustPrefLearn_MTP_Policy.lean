-- Prove2me | Definitions.Def_RobustPrefLearn_MTP_Policy
-- name    : RobustPrefLearn_MTP_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:04.295446+00:00
-- url     : https://prove2.me/theorems/1afd761e-517b-47c3-b137-fa0582e923de
-- title:
--   §4, pp. 12–13 — admissible policies, the law of the voting history, E[τ], δ-accurate policies (Definition 2), accurate families and their worst-case rate (9)
-- statement:
--   This file formalizes the sequential learning problem.
--
--   At each time $t$ a company shows a display set $S_t$ to an arriving consumer, who votes for a version $X_t\in S_t$; the history is $H_t=(S_1,X_1,\dots,S_t,X_t)$. An **admissible policy** $\pi$ consists of
--
--   1. a randomized display rule: given $H_t$, a probability distribution $\lambda_{t+1}$ on display sets from which $S_{t+1}$ is drawn;
--   2. a stopping rule: the time $\tau$ is the first $t$ at which the history $H_t$ satisfies the stopping condition;
--   3. a selection rule $d_\tau\in[K]$, a function of the stopped history.
--
--   Under a preference $f$, the probability of a history is the product
--   $$\mathbb P^\pi_f(H_t=h)=\prod_{\ell=1}^t \lambda_\ell(S_\ell\mid H_{\ell-1})\,f(X_\ell|S_\ell),$$
--   and $\mathbb E^\pi_f[\tau]=\sum_{t\ge0}\mathbb P^\pi_f(\tau>t)\in[0,\infty]$.
--
--   **Definition 2.** For $\delta\in(0,1)$, $\pi$ is $\delta$-accurate if for every $f\in\mathcal M_p$,
--   $$\mathbb P^\pi_f(\tau<\infty)=1\quad\text{and}\quad \mathbb P^\pi_f\bigl(d_\tau\neq\sigma_f^{-1}(1)\bigr)\le\delta .$$
--   A family $\Pi=\{\pi_\delta\}$ is accurate if each $\pi_\delta$ is $\delta$-accurate. Its asymptotic rate at $f$ is $\limsup_{\delta\downarrow0}\mathbb E^{\pi_\delta}_f[\tau]/\log(1/\delta)$, and its worst-case rate is the supremum of this rate over $f\in\mathcal M_p$, the objective of (9).
--
--   **Formalization Note** A history is a list of (display set, vote) pairs, newest first; `toHist v` turns the steps $v_0=(S_1,X_1),\dots,v_{t-1}=(S_t,X_t)$ into $H_t$. Display probabilities are in `ℝ≥0∞`, and admissibility requires them to sum to $1$ after every history. `survives π h` ($\tau>|h|$) says that no prefix $H_0,\dots,H_{|h|}$ of $h$ triggers the stopping condition; `stopsAt π h` ($\tau=|h|$) says that $h$ triggers it and no proper prefix does. Because everything is discrete, the law of the history is the explicit finite product above, and $\mathbb P(\tau<\infty)$, $\mathbb P(d_\tau\ne\sigma_f^{-1}(1),\tau<\infty)$ and $\mathbb E[\tau]$ are series in $[0,\infty]$. The paper's family is indexed by $\delta\in(0,1]$; accuracy is required for $\delta\in(0,1)$, and limits are along $\delta\downarrow0$ (`𝓝[>] 0`).
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), pp. 12–13, admissible policies and Definition 2; p. 18, (9)

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal Topology

namespace RobustPrefLearn.MTP

/-! # Admissible policies, the law of the voting history, δ-accuracy (§4, pp. 12–13).

A history is a list of (display set, vote) pairs, **newest first**: `(S_t, X_t) :: older`, so the
history `H_t = (S_1, X_1, …, S_t, X_t)` is the list `[(S_t, X_t), …, (S_1, X_1)]`, and the prefixes
`H_s` (`s ≤ t`) of `H_t` are the lists `H_t.drop (t - s)`. Everything is discrete, so the law
`P^π_f` of the history is given by its finite-dimensional probabilities
`P(H_t = h) = ∏_{ℓ ≤ t} λ_ℓ(S_ℓ | H_{ℓ-1}) f(X_ℓ|S_ℓ)`, and expectations of `τ` are series in
`[0, ∞]`. -/

/-- One step of the voting process: the display set shown and the vote cast. -/
abbrev Step (K : ℕ) := DS K × Fin K

/-- An admissible policy `π = ({λ_t}, τ, d_τ)` (p. 12), given through the history:
* `disp h S` is the probability `λ_{t+1}(S)` of displaying `S` to consumer `t + 1` after the
  history `H_t = h` (a randomized display rule adapted to the history);
* `stop h` says that the policy stops once the history `h` has been observed (the stopping time
  `τ` is the first `t` with `stop H_t`);
* `select h` is the final selection `d_τ` made when stopping after the history `h`. -/
structure Policy (K : ℕ) where
  disp : List (Step K) → DS K → ℝ≥0∞
  stop : List (Step K) → Prop
  select : List (Step K) → Fin K

/-- Each display rule `λ_{t+1}(· | H_t)` is a probability distribution on `𝒮`. -/
def Admissible {K : ℕ} (π : Policy K) : Prop :=
  ∀ h : List (Step K), ∑ S, π.disp h S = 1

/-- The probability `P^π_f(H_t = h)` of a history `h` (newest first):
`P([]) = 1` and `P((S, X) :: h) = P(h) · λ(S | h) · f(X|S)`. -/
noncomputable def pathProb {K : ℕ} (π : Policy K) (f : Pref K) : List (Step K) → ℝ≥0∞
  | [] => 1
  | (S, X) :: h => pathProb π f h * π.disp h S * ENNReal.ofReal (f S X)

/-- The history `H_t` (newest first) with steps `v 0 = (S_1, X_1), …, v (t-1) = (S_t, X_t)`. -/
def toHist {K t : ℕ} (v : Fin t → Step K) : List (Step K) :=
  (List.ofFn v).reverse

/-- `τ > |h|` on the history `h`: the policy has not stopped at any of the prefixes
`H_0, …, H_{|h|}` of `h`. -/
def survives {K : ℕ} (π : Policy K) (h : List (Step K)) : Prop :=
  ∀ j ≤ h.length, ¬ π.stop (h.drop j)

/-- `τ = |h|` on the history `h`: the policy stops at `h` and at none of its proper prefixes. -/
def stopsAt {K : ℕ} (π : Policy K) (h : List (Step K)) : Prop :=
  π.stop h ∧ ∀ j, 1 ≤ j → j ≤ h.length → ¬ π.stop (h.drop j)

open Classical in
/-- `P^π_f(τ > t)`. -/
noncomputable def probGT {K : ℕ} (π : Policy K) (f : Pref K) (t : ℕ) : ℝ≥0∞ :=
  ∑ v : Fin t → Step K, if survives π (toHist v) then pathProb π f (toHist v) else 0

/-- `E^π_f[τ] = ∑_{t ≥ 0} P^π_f(τ > t) ∈ [0, ∞]` (it is `∞` when `τ = ∞` with positive
probability). -/
noncomputable def expTau {K : ℕ} (π : Policy K) (f : Pref K) : ℝ≥0∞ :=
  ∑' t : ℕ, probGT π f t

open Classical in
/-- `P^π_f(τ < ∞) = ∑_t P^π_f(τ = t)`. -/
noncomputable def probStop {K : ℕ} (π : Policy K) (f : Pref K) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑ v : Fin t → Step K, if stopsAt π (toHist v) then pathProb π f (toHist v) else 0

open Classical in
/-- `P^π_f(τ < ∞, d_τ ≠ σ_f^{-1}(1))`: the policy stops and selects a version that is not the
top-ranked version of `f`. -/
noncomputable def probWrong {K : ℕ} (π : Policy K) (f : Pref K) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑ v : Fin t → Step K,
    if stopsAt π (toHist v) ∧ ¬ IsTop f (π.select (toHist v)) then pathProb π f (toHist v) else 0

/-- Definition 2 (i)–(ii), pp. 12–13: `π` is an admissible, `δ`-accurate policy:
`P^π_f(τ < ∞) = 1` and `P^π_f(d_τ ≠ σ_f^{-1}(1)) ≤ δ` for every `f ∈ M_p`. -/
def IsDeltaAccurate {K : ℕ} (p δ : ℝ) (π : Policy K) : Prop :=
  Admissible π ∧ ∀ f ∈ (Mp p : Set (Pref K)),
    probStop π f = 1 ∧ probWrong π f ≤ ENNReal.ofReal δ

/-- Definition 2 (iii), p. 13: the family `Π = {π_δ}` is accurate if every `π_δ` is
`δ`-accurate (`δ ∈ (0, 1)`). -/
def IsAccurate {K : ℕ} (p : ℝ) (fam : ℝ → Policy K) : Prop :=
  ∀ δ ∈ Set.Ioo (0 : ℝ) 1, IsDeltaAccurate p δ (fam δ)

/-- The asymptotic rate `limsup_{δ ↓ 0} E^{π_δ}_f[τ] / log(1/δ)` in `[0, ∞]`. -/
noncomputable def rate {K : ℕ} (fam : ℝ → Policy K) (f : Pref K) : ℝ≥0∞ :=
  Filter.limsup (fun δ : ℝ => expTau (fam δ) f / ENNReal.ofReal (Real.log (1 / δ))) (𝓝[>] 0)

/-- The worst-case rate `sup_{f ∈ M_p} limsup_{δ ↓ 0} E^{π_δ}_f[τ] / log(1/δ)` of (9), p. 18. -/
noncomputable def worstRate {K : ℕ} (p : ℝ) (fam : ℝ → Policy K) : ℝ≥0∞ :=
  ⨆ f ∈ (Mp p : Set (Pref K)), rate fam f

end RobustPrefLearn.MTP


