-- Prove2me | Definitions.Def_BudgetAgg_NashChar_Setting
-- name    : BudgetAgg_NashChar_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T04:59:45.634929+00:00
-- url     : https://prove2.me/theorems/a20b21a7-62ec-4e65-845d-dc476c49c11a
-- title:
--   §3, §4.2, §6, App. A, E — distributions, profiles, Leontief utilities, critical alternatives, efficiency, core fair share, group-strategyproofness, the Nash product
-- statement:
--   This file fixes the model of budget aggregation with Leontief utilities used throughout the mission.
--
--   **Agents, alternatives, distributions.** There are $n\ge1$ agents $N=[n]$ and $m\ge1$ alternatives $M=[m]$. A *distribution* is a vector $q=(q_1,\dots,q_m)$ with $q_j\ge0$ and $\sum_{j\in M}q_j=1$; the set of distributions is the simplex $\Delta^m$. Each agent $i$ reports a *peak* $p_i\in\Delta^m$, her ideal distribution. A *profile* $P=(p_{i,j})$ collects the peaks, and a *mechanism* is a map $f:(\Delta^m)^n\to\Delta^m$.
--
--   **Leontief utility.** With $M_i=\{j\in M: p_{i,j}>0\}$ (nonempty because $p_i$ sums to $1$), agent $i$'s utility from a vector $q$ is
--   $$u_i(q)=\min_{j\in M_i}\frac{q_j}{p_{i,j}}.$$
--   Her *critical alternatives* are $T_{q,i}=\arg\min_{j\in M_i} q_j/p_{i,j}$, and for a group $G\subseteq N$, $T_{q,G}=\bigcup_{i\in G}T_{q,i}$.
--
--   **Axioms.**
--   1. $q\in\Delta^m$ is *efficient* if no $q'\in\Delta^m$ has $u_i(q')\ge u_i(q)$ for all $i$ and $u_i(q')>u_i(q)$ for some $i$.
--   2. $q$ satisfies *core fair share* if no nonempty coalition $N'\subseteq N$ is *blocking*, where $N'$ blocks $q$ if some $q'\in\Delta^m$ satisfies, for every $q''\in\Delta^m$ and every $i\in N'$,
--   $$u_i\Big(\tfrac{|N'|}{n}q'+\big(1-\tfrac{|N'|}{n}\big)q''\Big)>u_i(q).$$
--   3. A mechanism $f$ is *group-strategyproof* if for every $N'\subseteq N$ and profiles $P,P'$ that agree outside $N'$, either $u_i(f(P))>u_i(f(P'))$ for some $i\in N'$, or $u_i(f(P))=u_i(f(P'))$ for all $i\in N'$, where $u_i$ is computed from the true peak $p_i$ of $P$.
--
--   **Nash product.** The Nash product of $q$ is $\prod_{i\in N}u_i(q)$, and $q$ is a Nash outcome at $P$ if $q\in\Delta^m$ maximizes it over $\Delta^m$.
--
--   **Decompositions and the key peak.** A *decomposition* of $q$ is a family of nonnegative vectors $(s_i)_{i\in N}$ with $\sum_{i}s_{i,j}=q_j$ for every $j$ and $\sum_j s_{i,j}=1/n$ for every $i$. The *key peak* of $p_i$ at $q$ concentrates $p_i$ on its critical alternatives:
--   $$p^*_{i,j}=\begin{cases}p_{i,j}/p_i(T_{q,i}) & j\in T_{q,i},\\ 0 & j\notin T_{q,i},\end{cases}\qquad p_i(T_{q,i})=\sum_{j\in T_{q,i}}p_{i,j}.$$
--
--   These are the objects of Theorem 3 and of every milestone of the mission.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. Core fair share quantifies over **nonempty** coalitions: in the paper's literal Definition 3 the empty coalition would satisfy the blocking condition vacuously, so no distribution would have core fair share. The Leontief minimum is a `Finset.inf'` over $M_i$ only, never over all of $M$ (in Lean $x/0=0$). Continuity of a mechanism is `Continuous` for the subtype topology on $(\Delta^m)^n$, which coincides with the $\ell_1$ topology of Definition 7. NASH is not defined as a function; `IsNashOutcome` is the maximizer predicate. `starPeak` is a raw vector; that it is a distribution follows from $T_{q,i}\subseteq M_i$ being nonempty.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, pp. 6–10, 16, 22, 24, 30–31, 33, Definitions 1, 3, 4, 7, 8, 12, 13, §4.2, key profile P∗ (p. 33)

import Mathlib

namespace BudgetAgg.NashChar

open Finset

/-- A profile of peaks and a tops-only aggregation mechanism (§3, pp. 6–7). -/
abbrev Profile (n m : ℕ) := Fin n → stdSimplex ℝ (Fin m)
abbrev Mechanism (n m : ℕ) := Profile n m → stdSimplex ℝ (Fin m)

/-- Every peak in the simplex assigns positive mass to some alternative, so the set
`M_i = {j : p_{i,j} > 0}` of §4.2 (p. 10) is nonempty. -/
theorem positive_support_nonempty {m : ℕ} (p : stdSimplex ℝ (Fin m)) :
    (Finset.univ.filter (fun j => 0 < p.1 j)).Nonempty := by
  by_contra h
  have hz : ∀ j, p.1 j = 0 := by
    intro j
    have hj : ¬ 0 < p.1 j := by
      intro hp
      exact h ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hp⟩⟩
    exact le_antisymm (le_of_not_gt hj) (p.2.1 j)
  have hs : (∑ j, p.1 j) = 0 := by simp [hz]
  have hp := p.2.2
  rw [hs] at hp
  norm_num at hp

/-- Leontief utility, the minimum ratio over the positive support of the peak (§4.2, p. 10). -/
noncomputable def leontief {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) : ℝ :=
  (Finset.univ.filter (fun j => 0 < p.1 j)).inf'
    (positive_support_nonempty p) (fun j => q j / p.1 j)

/-- Critical alternatives of a peak at a distribution (Definition 12, p. 22). -/
noncomputable def crit {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ) :
    Finset (Fin m) :=
  (Finset.univ.filter (fun j => 0 < p.1 j)).filter
    (fun j => q j / p.1 j = leontief p q)

/-- Alternatives critical to at least one member of a group (p. 24). -/
noncomputable def critG {n m : ℕ} (P : Profile n m) (q : Fin m → ℝ)
    (G : Finset (Fin n)) : Finset (Fin m) :=
  G.biUnion (fun i => crit (P i) q)

/-- Pareto efficiency of a distribution (Definition 1, p. 7). -/
def IsEfficient {n m : ℕ} (P : Profile n m) (q : stdSimplex ℝ (Fin m)) : Prop :=
  ¬ ∃ q' : stdSimplex ℝ (Fin m),
    (∀ i, leontief (P i) q.1 ≤ leontief (P i) q'.1) ∧
    (∃ i, leontief (P i) q.1 < leontief (P i) q'.1)

/-- Core fair share, with nonempty blocking coalitions (Definition 3, p. 8). -/
def IsCoreFairShare {n m : ℕ} (P : Profile n m)
    (q : stdSimplex ℝ (Fin m)) : Prop :=
  ∀ S : Finset (Fin n), S.Nonempty →
    ¬ ∃ q' : stdSimplex ℝ (Fin m),
      ∀ q'' : stdSimplex ℝ (Fin m), ∀ i ∈ S,
        leontief (P i) q.1 <
          leontief (P i) (fun j =>
            ((S.card : ℝ) / (n : ℝ)) * q'.1 j +
            (1 - (S.card : ℝ) / (n : ℝ)) * q''.1 j)

/-- Group-strategyproofness, measured at each agent's true peak (Definition 8, p. 9). -/
def IsGroupSP {n m : ℕ} (f : Mechanism n m) : Prop :=
  ∀ (S : Finset (Fin n)) (P P' : Profile n m),
    (∀ j, j ∉ S → P' j = P j) →
    (∃ i ∈ S, leontief (P i) (f P').1 < leontief (P i) (f P).1) ∨
    (∀ i ∈ S, leontief (P i) (f P).1 = leontief (P i) (f P').1)

/-- Product of Leontief utilities (§6, p. 16). -/
noncomputable def nashProduct {n m : ℕ} (P : Profile n m) (q : Fin m → ℝ) : ℝ :=
  ∏ i, leontief (P i) q

/-- Being a Nash-product maximizer among distributions (§6, p. 16). -/
def IsNashOutcome {n m : ℕ} (P : Profile n m) (q : Fin m → ℝ) : Prop :=
  q ∈ stdSimplex ℝ (Fin m) ∧
    ∀ q' ∈ stdSimplex ℝ (Fin m), nashProduct P q' ≤ nashProduct P q

/-- A decomposition into nonnegative shares of size `1/n` (Definition 13, pp. 30–31). -/
def IsDecomposition {n m : ℕ} (q : Fin m → ℝ) (s : Fin n → Fin m → ℝ) : Prop :=
  (∀ i j, 0 ≤ s i j) ∧
  (∀ j, ∑ i, s i j = q j) ∧
  (∀ i, ∑ j, s i j = 1 / (n : ℝ))

/-- The peak obtained by concentrating `p` on its alternatives critical at `q` (p. 33). -/
noncomputable def starPeak {m : ℕ} (p : stdSimplex ℝ (Fin m)) (q : Fin m → ℝ)
    (j : Fin m) : ℝ :=
  if j ∈ crit p q then p.1 j / ∑ k ∈ crit p q, p.1 k else 0

end BudgetAgg.NashChar


