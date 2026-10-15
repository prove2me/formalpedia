-- Prove2me | Definitions.Def_SecretaryAdvice_Memoryless_LP
-- name    : SecretaryAdvice_Memoryless_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T00:42:00.934978+00:00
-- url     : https://prove2.me/theorems/da3e5381-ccee-4c42-acf9-3c4714ae5086
-- title:
--   §3, pp. 9–11 — the LP of secretaries with advice: a(i,s), c(i,s,j,s′), constraint (4), objective (5), reconstructed policy (6)
-- statement:
--   This file defines the linear program of §3 for a signaling structure $\mathbb P$ on $n$ secretaries with finite signal space $\mathcal S$ (see the Setting file for the model).
--
--   For $i\in[n]$ and $s,s'\in\mathcal S$ and $j<i$ define
--   $$a(i,s)=\mathbb P[r_i=n,\ s_i=s],\qquad c(i,s,j,s')=\mathbb P[T_j,\ s_j=s'\mid T_i,\ s_i=s].$$
--   Values $z(i,s)$ are **feasible** when $z(i,s)\ge 0$ and constraint (4) holds:
--   $$z(i,s)\le 1-\sum_{j<i}\sum_{s'\in\mathcal S} z(j,s')\,c(i,s,j,s').\tag{4}$$
--   The objective is
--   $$\mathsf{Obj}=\sum_{i=1}^n\sum_{s\in\mathcal S} z(i,s)\,a(i,s).\tag{5}$$
--   Given $z$, the **reconstructed policy** (6) stops at a best-so-far round $i$ with signal $s$ with probability
--   $$q(i,s)=\frac{z(i,s)}{1-\sum_{j<i}\sum_{s'\in\mathcal S} z(j,s')\,\mathbb P[T_j,\ s_j=s'\mid T_i,\ s_i=s]}$$
--   and never stops at a round that is not best so far.
--
--   The LP is the main tool of §3: Propositions 9 and 10 show that, under Non-Filtering and History-Irrelevance, its feasible points are exactly the winning probabilities achievable by policies.
--
--   **Formalization Note** The conditional probability $c$ is the quotient $\mathbb P[T_j,s_j=s',T_i,s_i=s]/\mathbb P[T_i,s_i=s]$, which Lean evaluates to $0$ when $\mathbb P[T_i,s_i=s]=0$; then constraint (4) at $(i,s)$ reads $z(i,s)\le 1$ and $a(i,s)=0$, so the objective is unaffected. The policy (6) is set to $0$ when its denominator is $0$ (then feasibility forces $z(i,s)=0$). Indices are 0-based as in the Setting file.
-- source:
--   Dütting et al., Secretaries with Advice, arXiv:2011.06726v1, pp. 9–11, §3: definitions of z(i,s), a(i,s), c(i,s,j,s′) (p. 9), constraint (4) and objective (5) (p. 10), policy (6) (p. 11)

import Mathlib
import Definitions.Def_SecretaryAdvice_Memoryless_Setting

namespace SecretaryAdvice.Memoryless

variable {n : ℕ} {S : Type} [Fintype S]

/-- `a(i, s) = P[r_i = n, s_i = s]` (§3, p. 9). -/
noncomputable def a (μ : SignalingStructure n S) (i : Fin n) (s : S) : ℝ :=
  prob μ (fun ω => IsTop i ω ∧ sig i ω = s)

/-- `c(i, s, j, s') = P[T_j, s_j = s' | T_i, s_i = s]` (§3, p. 9), written as the quotient
`P[T_j, s_j = s', T_i, s_i = s] / P[T_i, s_i = s]`; it is `0` when `P[T_i, s_i = s] = 0`
(Lean's convention `x / 0 = 0`). Only the values with `j < i` are used. -/
noncomputable def c (μ : SignalingStructure n S) (i : Fin n) (s : S) (j : Fin n) (s' : S) : ℝ :=
  prob μ (fun ω => T j ω ∧ sig j ω = s' ∧ T i ω ∧ sig i ω = s) /
    prob μ (fun ω => T i ω ∧ sig i ω = s)

/-- The right-hand side of constraint (4): `1 - ∑_{j<i} ∑_{s'} z(j, s') · c(i, s, j, s')`. -/
noncomputable def slack (μ : SignalingStructure n S) (z : Fin n → S → ℝ) (i : Fin n) (s : S) : ℝ :=
  1 - ∑ j ∈ Finset.Iio i, ∑ s', z j s' * c μ i s j s'

/-- Feasibility for the LP of §3: `z(i, s) ≥ 0` and constraint (4) for every `i` and `s`. -/
def LPFeasible (μ : SignalingStructure n S) (z : Fin n → S → ℝ) : Prop :=
  (∀ i s, 0 ≤ z i s) ∧ ∀ i s, z i s ≤ slack μ z i s

/-- The LP objective (5): `Obj = ∑_i ∑_s z(i, s) · a(i, s)`. -/
noncomputable def LPObj (μ : SignalingStructure n S) (z : Fin n → S → ℝ) : ℝ :=
  ∑ i, ∑ s, z i s * a μ i s

/-- The reconstructed policy (6) of the proof of Proposition 10: on a best-so-far round `i` with
signal `s` it stops with probability `z(i, s) / (1 - ∑_{j<i} ∑_{s'} z(j, s') · c(i, s, j, s'))`
(and with probability `0` if that denominator is `0`); on any other round it does not stop. -/
noncomputable def reconstructedPolicy (μ : SignalingStructure n S) (z : Fin n → S → ℝ) :
    Policy n S :=
  fun i x =>
    if bestSoFar x = true then
      (if slack μ z i (lastSignal x) = 0 then 0 else z i (lastSignal x) / slack μ z i (lastSignal x))
    else 0

end SecretaryAdvice.Memoryless


