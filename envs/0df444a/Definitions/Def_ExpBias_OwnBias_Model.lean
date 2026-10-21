-- Prove2me | Definitions.Def_ExpBias_OwnBias_Model
-- name    : ExpBias_OwnBias_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:33.311263+00:00
-- url     : https://prove2.me/theorems/98b8b36c-cc02-41f7-ba8e-5f53bf694334
-- title:
--   §2–§2.2, pp. 11–13 — exploit-or-status-quo decision, prior p, threshold p̂, experiment set E, Table 1 signals, value of an experiment
-- statement:
--   This file sets up the decision model of §2 of Gans's paper.
--
--   **Payoffs and prior.** A firm decides whether to exploit a new technology. The state is $W$ (the technology works) or $N$ (it does not). Exploiting earns $v_W$ in state $W$ and $v_N$ in state $N$; not exploiting (the status quo) earns $v_S$ in both states. The firm's prior probability of $W$ is $p$, and $\Lambda$ is the cap on the precisions of an experiment. The **standing assumptions** are
--   $$
--   v_W > v_S > v_N,\qquad 0<p<1,\qquad 1<\Lambda<2 .
--   $$
--   The no-information threshold is $\hat p = \frac{v_S - v_N}{v_W - v_N}$ and $\lambda \equiv \Lambda - 1$.
--
--   **Experiments.** An experiment is a pair $\{\lambda_w,\lambda_n\}$ with $\Pr[w\mid W]=\lambda_w$ and $\Pr[n\mid N]=\lambda_n$ (Table 1). The experiment set is
--   $$
--   \mathbf E=\bigl\{\{\lambda_w,\lambda_n\}\in(0,1]^2 : 1<\lambda_w+\lambda_n\le\Lambda\bigr\}.
--   $$
--   The **w-biased** experiment is $\sigma_w=\{1,\lambda\}$ and the **n-biased** experiment is $\sigma_n=\{\lambda,1\}$.
--
--   **Probabilities.** The joint probability of a state and a signal is the prior times the Table 1 entry, for example $\Pr[W\wedge w]=p\lambda_w$ and $\Pr[N\wedge w]=(1-p)(1-\lambda_n)$. The probability of a signal is the sum over the two states, and the posterior $\Pr[W\mid s]$ is the joint probability divided by the signal probability.
--
--   **Value of an experiment.** A decision rule $d$ says, for each signal, whether to exploit. Its expected payoff is
--   $$
--   R(e,d)=\sum_{\text{state }t}\ \sum_{\text{signal }s}\Pr[t\wedge s]\,u\bigl(t,d(s)\bigr),
--   $$
--   where $u(t,\text{exploit})$ is $v_W$ or $v_N$ and $u(t,\text{status quo})=v_S$. The value of an experiment $e$ is the best of the four rules: $\mathrm{value}(e)=\max_d R(e,d)$. An experiment $e$ is **optimal** if $e\in\mathbf E$ and $\mathrm{value}(e')\le\mathrm{value}(e)$ for every $e'\in\mathbf E$.
--
--   These objects are the vocabulary of Proposition 1 and of every milestone of the mission.
--
--   **Formalization Note.** States and signals are `Bool` (`true` = $W$, resp. $w$); a decision rule is a function `Bool → Bool` (`true` = exploit). The value is `Finset.sup'` over the four rules. The joint probabilities already sum to one, so no normalisation is applied. The posterior uses real division, which returns $0$ on a probability-zero signal; the milestones state posteriors only where the signal has positive probability. The assumptions $0<p<1$ and $1<\Lambda$ are added to the page's: without $1<\Lambda$ the set $\mathbf E$ is empty, and at $p\in\{0,1\}$ the two biased experiments tie.
-- source:
--   Gans, A Synthetic Model of Disruption and Experimentation, NBER Working Paper 29091 (July 2021), pp. 11–13 (PDF 12–14), §2, §2.1, Table 1, §2.2

import Mathlib

namespace ExpBias.OwnBias

/-- The primitives of the model (§2, p. 11): payoffs `vW` (exploit, works), `vS` (status quo),
`vN` (exploit, does not work), the prior `p` that the technology works, and the cap `Lam` (Λ)
on `λw + λn` (§2.1, p. 12). -/
structure Params where
  vW : ℝ
  vS : ℝ
  vN : ℝ
  p : ℝ
  Lam : ℝ

/-- Standing assumptions: `vW > vS > vN` (p. 11) and `Λ < 2` (p. 12), plus the disclosed
additions `0 < p < 1` (a nondegenerate prior) and `1 < Λ` (otherwise `E` is empty). -/
structure Params.Standing (P : Params) : Prop where
  vN_lt_vS : P.vN < P.vS
  vS_lt_vW : P.vS < P.vW
  p_pos : 0 < P.p
  p_lt_one : P.p < 1
  one_lt_Lam : 1 < P.Lam
  Lam_lt_two : P.Lam < 2

/-- The no-information threshold `p̂ = (vS − vN)/(vW − vN)` (p. 11). -/
noncomputable def pHat (P : Params) : ℝ := (P.vS - P.vN) / (P.vW - P.vN)

/-- `λ ≡ Λ − 1` (p. 12). -/
def lam (P : Params) : ℝ := P.Lam - 1

/-- An experiment `{λw, λn}`: `lw = Pr[w | W]`, `ln = Pr[n | N]` (Table 1). -/
structure Experiment where
  lw : ℝ
  ln : ℝ

/-- Membership in the experiment set `E` (p. 12): `{λw, λn} ∈ (0,1]²` with `λw + λn ∈ (1, Λ]`. -/
def InE (P : Params) (e : Experiment) : Prop :=
  0 < e.lw ∧ e.lw ≤ 1 ∧ 0 < e.ln ∧ e.ln ≤ 1 ∧ 1 < e.lw + e.ln ∧ e.lw + e.ln ≤ P.Lam

/-- The w-biased experiment `{λw, λn} = {1, λ}` (p. 12). -/
def wBiased (P : Params) : Experiment := ⟨1, lam P⟩

/-- The n-biased experiment `{λw, λn} = {λ, 1}` (p. 12). -/
def nBiased (P : Params) : Experiment := ⟨lam P, 1⟩

/-- Joint probability `Pr[state ∧ signal]` from the prior and Table 1. States: `true` = W,
`false` = N. Signals: `true` = w, `false` = n. -/
def joint (P : Params) (e : Experiment) (st sig : Bool) : ℝ :=
  (if st then P.p else 1 - P.p) *
    (if st then (if sig then e.lw else 1 - e.lw) else (if sig then 1 - e.ln else e.ln))

/-- Probability of a signal, `Pr[sig]`. -/
def sigProb (P : Params) (e : Experiment) (sig : Bool) : ℝ :=
  joint P e true sig + joint P e false sig

/-- Posterior `Pr[W | sig]` (real division; `0` when the signal has probability `0`). -/
noncomputable def postW (P : Params) (e : Experiment) (sig : Bool) : ℝ :=
  joint P e true sig / sigProb P e sig

/-- Payoff in state `st` of exploiting (`act = true`) or keeping the status quo (`act = false`). -/
def payoff (P : Params) (st act : Bool) : ℝ :=
  if act then (if st then P.vW else P.vN) else P.vS

/-- Expected payoff of the signal-contingent decision rule `d` (`d sig = true`: exploit after `sig`). -/
def ruleValue (P : Params) (e : Experiment) (d : Bool → Bool) : ℝ :=
  ∑ st : Bool, ∑ sig : Bool, joint P e st sig * payoff P st (d sig)

/-- The value of an experiment: the expected payoff under the best of the four
signal-contingent decision rules. -/
noncomputable def value (P : Params) (e : Experiment) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (ruleValue P e)

/-- `e` is an optimal choice from the experiment set `E`. -/
def IsOptimal (P : Params) (e : Experiment) : Prop :=
  InE P e ∧ ∀ e', InE P e' → value P e' ≤ value P e

end ExpBias.OwnBias


