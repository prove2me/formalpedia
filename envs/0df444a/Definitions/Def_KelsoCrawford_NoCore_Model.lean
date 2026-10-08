-- Prove2me | Definitions.Def_KelsoCrawford_NoCore_Model
-- name    : KelsoCrawford_NoCore_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:00.602752+00:00
-- url     : https://prove2.me/theorems/016c976f-ad71-4ccc-81e9-07a80aad3db0
-- title:
--   Section 2, pp. 1486–1488 — job-matching market, profits, demand sets, (MP), (NFL), (GS), allocations, core (D1, D3)
-- statement:
--   There are finitely many workers $i \in W$ and finitely many firms $j \in F$. A **job-matching market** consists of
--
--   1. utilities $u^i(j; s)$: worker $i$'s utility of working for firm $j$ at salary $s \in \mathbb{R}$;
--   2. technologies $y^j(C)$: firm $j$'s gross product when it hires the set of workers $C \subseteq W$;
--   3. reservation salaries $\sigma_{ij} \in \mathbb{R}$.
--
--   Firm $j$'s **net profit** from a set $C$ at the salary vector $s^j = (s_{ij})_{i \in W}$ is
--   $$\pi^j(C; s^j) = y^j(C) - \sum_{i \in C} s_{ij},$$
--   and $C$ is **demanded** at $s^j$, written $C \in M^j(s^j)$, when it maximizes $\pi^j(\cdot\,; s^j)$ over all sets of workers. Firm $j$'s technology satisfies **gross substitutes** (GS) on a set $S$ of salary vectors if, whenever $s^j, \tilde s^j \in S$, $s^j \le \tilde s^j$ and $C \in M^j(s^j)$, some $\tilde C \in M^j(\tilde s^j)$ contains every worker of $C$ whose salary did not change. The market satisfies (MP) if $y^j(C \cup \{i\}) - y^j(C) - \sigma_{ij} \ge 0$ for every $i$, $j$ and $C \not\ni i$, and (NFL) if $y^j(\emptyset) = 0$ for every $j$.
--
--   An **allocation** assigns every worker $i$ to a firm $f(i)$ and pays worker $i$ the salary $s_{if(i)}$; $C^j = \{i : f(i) = j\}$ is the set of workers firm $j$ hires. It is **individually rational** (D1) if $s_{if(i)} \ge \sigma_{if(i)}$ for every worker and $\pi^j(C^j; s^j) \ge 0$ for every firm. Given, for each pair $(i, j)$, a set $R_{ij}$ of salaries a coalition may use, a firm $j$ and a set of workers $C$ **strictly improve upon** the allocation if there are salaries $r_{ij} \in R_{ij}$ ($i \in C$) with
--   $$u^i(j; r_{ij}) > u^i(f(i); s_{if(i)}) \ \text{ for all } i \in C, \qquad \pi^j(C; r^j) > \pi^j(C^j; s^j).$$
--   A **core allocation** (D3) is an individually rational allocation that pays permitted salaries and that no firm–set-of-workers coalition can strictly improve upon. With $R_{ij} = \mathbb{R}$ (salaries vary continuously) this is the core of the continuous market.
--
--   These are the paper's basic objects; the example of Section 6 is a market of this kind.
--
--   **Formalization Note** Salaries are real numbers; an allocation is a function $f : W \to F$ (every worker is employed, as in D1) together with the vector of salaries each worker receives at his or her own firm. `anySalary` is the continuous choice $R_{ij} = \mathbb{R}$. The coalition $C = \emptyset$ is allowed, as in the paper. The reservation salaries $\sigma_{ij}$ are taken as data.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1486–1488, Section 2, (MP), (NFL), (A), (GS), D1–D3

import Mathlib
import Definitions.Def_KelsoCrawford_ContinuousCore_Model
import Definitions.Def_KelsoCrawford_Process_Model

namespace KelsoCrawford.NoCore

structure Market (W F : Type) where
  u : W → F → ℝ → ℝ
  y : F → Finset W → ℝ
  σ : W → F → ℝ

variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

def Market.MP (M : Market W F) : Prop :=
  ∀ i j (C : Finset W), i ∉ C →
    0 ≤ M.y j (insert i C) - M.y j C - M.σ i j

def Market.NFL (M : Market W F) : Prop := ∀ j, M.y j ∅ = 0

structure Allocation (W F : Type) where
  assign : W → F
  sal : W → ℝ

def Allocation.hired (A : Allocation W F) (j : F) : Finset W :=
  Finset.univ.filter (fun i => A.assign i = j)

def Market.IsIR (M : Market W F) (A : Allocation W F) : Prop :=
  (∀ i, M.σ i (A.assign i) ≤ A.sal i) ∧
    ∀ j, 0 ≤ KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal

def Market.CanStrictlyImprove (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ),
    (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∧
    KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal < KelsoCrawford.Process.profit (M.y j) C r

def Market.IsCore (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanStrictlyImprove R A

end KelsoCrawford.NoCore


