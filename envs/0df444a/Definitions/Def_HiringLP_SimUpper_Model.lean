-- Prove2me | Definitions.Def_HiringLP_SimUpper_Model
-- name    : HiringLP_SimUpper_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:56.27899+00:00
-- url     : https://prove2.me/theorems/66c3423f-b512-4eea-ab25-5759d43eecbe
-- title:
--   §3.3, §6.1, pp. 14, 25–26 — Simultaneous Offering instances, expected reward of an offer set, OPT_sim, τ-bounded instances, value-ordered policies
-- statement:
--   **Simultaneous Offering** (Epstein–Ma, §3.3). A firm has $k$ positions and $n$ candidates. Candidate $i$ accepts an offer, if sent, with probability $p_i \in [0,1]$, independently of the others, and then adds value $v_i \ge 0$. The firm chooses a set $S \subseteq [n]$ of candidates and sends all offers at once. If $A \subseteq S$ is the random set of candidates who accept, the reward is
--   $$
--   \sum_{i \in A} v_i - [\,|A| - k\,]^+ ,
--   $$
--   i.e. each hire beyond capacity costs $c = 1$ (values are rescaled by $1/c$). An instance is $I = (k, n, p, v)$ with $1 \le k \le n$, $p \in [0,1]^n$, $v \in \mathbb{R}^n_+$, and, as in §6.1, the candidates are labelled so that $v_1 \ge v_2 \ge \cdots \ge v_n$.
--
--   This file defines:
--   1. the **expected reward** $R(I, S)$ of an offer set $S$, written as the finite sum over all possible accepting sets $A$ of $\Pr[A]$ times the reward; more generally $R$ of a vector $y$ of independent offer probabilities, where candidate $i$ is hired with probability $y_i p_i$;
--   2. $\mathrm{OPT}_{\mathrm{sim}}(I)$, the largest expected reward of an offer set (a randomized policy is a mixture of offer sets and cannot do better);
--   3. the class $\mathcal{I}^\tau_{\mathrm{sim}}$ of **$\tau$-bounded** instances, those with $v_i \ge \tau$ for all $i$ (p. 26);
--   4. the **value-ordered policy** with parameter $m$, which sends offers to the $m$ highest-valued candidates $\{1, \dots, m\}$ (p. 25).
--
--   These are the objects of Theorem 4: the comparison is between value-ordered policies and the optimum over all offer sets.
--
--   **Formalization Note.** Candidates are `Fin n`, so the paper's candidate $i$ is index $i-1$ and the value-ordered set is the indices below $m$. Sortedness is the hypothesis `Antitone v` inside `Valid`; with ties any sorted labelling is allowed. The expectation is an explicit finite sum over the $2^n$ accepting sets with product probabilities, no measure theory. `OPTsim` is the supremum of the finite range of offer-set rewards, hence a maximum. The same encoding (same names and bodies) is used in the companion mission on the lower bound (`HiringLP.SimLower`).
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 14 (§3.3, model and I_sim), p. 25 (§6.1, value-ordered policies), p. 26 (τ-bounded instances I^τ_sim)

import Mathlib

namespace HiringLP.SimUpper

open Finset

/-- An instance `I = (k, n, p, v)` of Simultaneous Offering (p. 14): `n` candidates indexed by
`Fin n`, `k` positions, acceptance probabilities `p i` and values `v i` (the overage cost is
normalised to `c = 1`). -/
structure SimInstance (n : ℕ) where
  k : ℕ
  p : Fin n → ℝ
  v : Fin n → ℝ

/-- p. 14 (`1 ≤ k ≤ n`, `p ∈ [0,1]ⁿ`, `v ∈ ℝⁿ₊`) and p. 25 (labels sorted: `v₁ ≥ ⋯ ≥ vₙ`). -/
def SimInstance.Valid {n : ℕ} (I : SimInstance n) : Prop :=
  1 ≤ I.k ∧ I.k ≤ n ∧ (∀ i, 0 ≤ I.p i ∧ I.p i ≤ 1) ∧ (∀ i, 0 ≤ I.v i) ∧ Antitone I.v

/-- p. 26: `I ∈ I^τ_sim`, every value is at least `τ`. -/
def SimInstance.TauBounded {n : ℕ} (I : SimInstance n) (τ : ℝ) : Prop := ∀ i, τ ≤ I.v i

/-- Probability that the accepting set is exactly `A` when candidate `i` accepts independently
with probability `q i`. -/
def setProb {n : ℕ} (q : Fin n → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∏ i, if i ∈ A then q i else 1 - q i

/-- Expected reward `E[Σ_{i∈A} v_i − [|A| − k]⁺]` (p. 14, `c = 1`) when each offer is sent
independently with probability `y i`; a deterministic offer set is the 0/1 case. -/
def rewardIndep {n : ℕ} (I : SimInstance n) (y : Fin n → ℝ) : ℝ :=
  ∑ A : Finset (Fin n), setProb (fun i => y i * I.p i) A *
    ((∑ i ∈ A, I.v i) - max ((A.card : ℝ) - I.k) 0)

/-- Expected reward of sending offers to the set `S` (p. 14). -/
def reward {n : ℕ} (I : SimInstance n) (S : Finset (Fin n)) : ℝ :=
  rewardIndep I (fun i => if i ∈ S then 1 else 0)

/-- `OPT_sim(I)` (p. 14): the best expected reward over offer sets; a randomized policy is a
mixture of offer sets, so this is also the supremum over all policies `Π_sim`. -/
noncomputable def OPTsim {n : ℕ} (I : SimInstance n) : ℝ := sSup (Set.range (reward I))

/-- p. 25: the value-ordered policy with parameter `m` sends offers to the `m` candidates with
the highest values, i.e. (labels sorted) to `{1, …, m}`, here the indices `0, …, m − 1`. -/
def valueOrdered {n : ℕ} (m : ℕ) : Finset (Fin n) := univ.filter (fun i => i.val < m)

end HiringLP.SimUpper


