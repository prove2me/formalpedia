-- Prove2me | Definitions.Def_HiringLP_SimLower_Model
-- name    : HiringLP_SimLower_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:06.881888+00:00
-- url     : https://prove2.me/theorems/a772e9f2-7dce-4dce-a845-463cf162812e
-- title:
--   §3.3, p. 14 and §6.1, pp. 25–26 — Simultaneous Offering instances, the expected reward with overage cost, and OPT_sim
-- statement:
--   This file fixes the **Simultaneous Offering** problem of Epstein and Ma.
--
--   **Instances.** An instance $I=(k,n,p,v)$ consists of a number of positions $k$, a number of candidates $n$, and for each candidate $i\in[n]$ an acceptance probability $p_i$ and a value $v_i$. The instance is *valid*, $I\in\mathcal I_{\mathrm{sim}}$, when
--   1. $1\le k\le n$;
--   2. $0\le p_i\le 1$ and $v_i\ge 0$ for every $i$;
--   3. the candidates are labelled in non-increasing order of value, $v_1\ge v_2\ge\dots\ge v_n$.
--
--   For $\tau>0$ the instance is *$\tau$-bounded*, $I\in\mathcal I^\tau_{\mathrm{sim}}$, when $v_i\ge\tau$ for every $i$.
--
--   **Reward.** The firm sends offers to a set $S\subseteq[n]$; each candidate in $S$ accepts independently with probability $p_i$. If $A\subseteq S$ is the set of acceptances, the reward is
--   $$\sum_{i\in A} v_i-\big[\,|A|-k\,\big]^+ ,$$
--   the overage cost per candidate hired beyond $k$ being normalised to $c=1$. More generally, if the offer to candidate $i$ is sent independently with probability $y_i\in[0,1]$, candidate $i$ is hired independently with probability $y_ip_i$, and the expected reward is
--   $$R(I;y)=\sum_{A\subseteq[n]}\Big(\prod_{i\in A}y_ip_i\prod_{i\notin A}(1-y_ip_i)\Big)\Big(\sum_{i\in A}v_i-\big[\,|A|-k\,\big]^+\Big).$$
--   A deterministic offer set $S$ is the case $y=\mathbf 1_S$, with expected reward $R(I;S)$.
--
--   **Optimum.** $\mathrm{OPT}_{\mathrm{sim}}(I)=\max_{S\subseteq[n]}R(I;S)$ is the best expected reward of a policy; a randomised policy is a mixture of offer sets and cannot do better.
--
--   These objects are shared by every statement of the mission: the LP relaxation, the algorithm $\mathrm{ALG}^s_{\mathrm{sim}}$ and the main theorem are all stated about them.
--
--   **Formalization Note** Candidates are `Fin n` (0-based). The sorted labelling $v_1\ge\dots\ge v_n$, which the paper obtains by relabelling (p. 25), is part of `Valid` as `Antitone I.v`; every statement holds for any labelling consistent with the values, ties in any order. The rescaling $c=1$ is the paper's own (p. 14). `OPTsim` is the supremum of the finitely many values `reward I S`, i.e. their maximum.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 14, §3.3; p. 25, §6.1 (sorted values); p. 26 (τ-bounded instances)

import Mathlib

open Finset

namespace HiringLP.SimLower

/-- An instance `I = (k, n, p, v)` of Simultaneous Offering (Epstein–Ma, §3.3, p. 14): `k` positions and,
for each candidate `i : Fin n`, the acceptance probability `p i` and the value `v i` (relative to an
overage cost normalised to `c = 1`). -/
structure SimInstance (n : ℕ) where
  k : ℕ
  p : Fin n → ℝ
  v : Fin n → ℝ

/-- `I ∈ I_sim` (p. 14: `1 ≤ k ≤ n`, `p ∈ [0,1]ⁿ`, `v ∈ ℝⁿ₊`), with the candidates labelled in
non-increasing order of value (p. 25: "Assume that v₁ ≥ v₂ ≥ ⋯ ≥ vₙ"). -/
def SimInstance.Valid {n : ℕ} (I : SimInstance n) : Prop :=
  1 ≤ I.k ∧ I.k ≤ n ∧ (∀ i, 0 ≤ I.p i ∧ I.p i ≤ 1) ∧ (∀ i, 0 ≤ I.v i) ∧ Antitone I.v

/-- `I ∈ I^τ_sim` (p. 26): every value is at least `τ`. -/
def SimInstance.TauBounded {n : ℕ} (I : SimInstance n) (τ : ℝ) : Prop :=
  ∀ i, τ ≤ I.v i

/-- Probability that the set of hired candidates is exactly `A` when candidate `i` is hired independently
with probability `q i`. -/
def setProb {n : ℕ} (q : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∏ i, if i ∈ A then q i else 1 - q i

/-- Expected reward `E[Σ_{i∈A} vᵢ − [|A| − k]⁺]` (p. 14, `c = 1`) when the offer to candidate `i` is sent
independently with probability `y i` and accepted independently with probability `p i`, so that `i` is
hired independently with probability `y i * p i`. A deterministic offer set is the 0/1 case. -/
def rewardIndep {n : ℕ} (I : SimInstance n) (y : Fin n → ℝ) : ℝ :=
  ∑ A : Finset (Fin n), setProb (fun i => y i * I.p i) A *
    ((∑ i ∈ A, I.v i) - max ((A.card : ℝ) - I.k) 0)

/-- Expected reward of sending offers to exactly the candidates in `S`. -/
def reward {n : ℕ} (I : SimInstance n) (S : Finset (Fin n)) : ℝ :=
  rewardIndep I (fun i => if i ∈ S then 1 else 0)

/-- `OPT_sim(I)` (p. 14): the best expected reward over offer sets. A randomised policy is a mixture of
offer sets, so its expected reward is at most this maximum. -/
noncomputable def OPTsim {n : ℕ} (I : SimInstance n) : ℝ :=
  sSup (Set.range (reward I))

end HiringLP.SimLower


