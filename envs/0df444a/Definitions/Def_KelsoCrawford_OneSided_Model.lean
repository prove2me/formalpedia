-- Prove2me | Definitions.Def_KelsoCrawford_OneSided_Model
-- name    : KelsoCrawford_OneSided_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:05.402958+00:00
-- url     : https://prove2.me/theorems/cd521049-22e0-4966-8f04-a53dabc0294f
-- title:
--   Section 2, pp. 1486–1488 — job-matching market, profit, demand (A), (GS), allocations, individual rationality (D1) and the strict core (D2)
-- statement:
--   There are finitely many workers $i \in W$ and finitely many firms $j \in F$ (the paper's $\{1,\dots,m\}$ and $\{1,\dots,n\}$). A **market** consists of utilities $u^i(j; s)$ (worker $i$'s utility of working for firm $j$ at salary $s \in \mathbb R$), gross products $y^j(C)$ (firm $j$'s output when it hires the set $C \subseteq W$), and reservation salaries $\sigma_{ij}$ (the lowest salary at which worker $i$ would consider working for firm $j$).
--
--   Facing the salary vector $s^j = (s_{1j}, \dots, s_{mj})$, firm $j$'s **net profit** from hiring $C$ is
--   $$\pi^j(C; s^j) = y^j(C) - \sum_{i \in C} s_{ij},$$
--   and $C$ is **demanded**, $C \in M^j(s^j)$, if it maximizes $\pi^j(\cdot\,; s^j)$ over all sets of workers (problem (A)).
--
--   **Gross substitutes (GS)** for one firm, relative to a set $S$ of admissible salary vectors: whenever $s^j, \tilde s^j \in S$ with $s^j \le \tilde s^j$ componentwise and $C \in M^j(s^j)$, some $\tilde C \in M^j(\tilde s^j)$ contains $T^j(C) = \{ i \in C : \tilde s_{ij} = s_{ij} \}$.
--
--   An **allocation** assigns every worker $i$ to a firm $f(i)$ at a salary $s_{if(i)}$; $C^j = \{ i : f(i) = j\}$. It is **individually rational** (D1) if $s_{if(i)} \ge \sigma_{if(i)}$ for every $i$ and $\pi^j(C^j; s^j) \ge 0$ for every $j$. Given sets $R_{ij}$ of salaries coalitions may use, a firm $j$, a set $C$ of workers and salaries $r_{ij} \in R_{ij}$ ($i \in C$) **improve upon** the allocation if
--   $$u^i(j; r_{ij}) \ge u^i(f(i); s_{if(i)}) \ (i \in C), \qquad \pi^j(C; r^j) \ge \pi^j(C^j; s^j),$$
--   with strict inequality for at least one member of $C \cup \{j\}$. A **strict core allocation** (D2) is an individually rational allocation, paying salaries in $R$, that no such coalition can improve upon.
--
--   These are the objects of the one-sided market theorem (Theorem 3) and of the comparative statics of Section 5.
--
--   **Formalization Note** The admissible salaries are a parameter `R`; in the continuous market it is `anySalary` (every real salary), declared in the companion module of Section 4. Every worker is assigned to exactly one firm (no unemployment), as the paper's $f : \{1,\dots,m\} \to \{1,\dots,n\}$; the empty coalition is allowed. The paper's definition of $\sigma_{ij}$ by $u^i(j;\sigma_{ij}) = u^i(0;0)$ is not built in: $\sigma$ is data.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1486–1488, Section 2, (A), (GS), D1–D2

import Mathlib
import Definitions.Def_KelsoCrawford_ContinuousCore_Model

namespace KelsoCrawford.OneSided

structure Market (W F : Type) where
  u : W → F → ℝ → ℝ
  y : F → Finset W → ℝ
  σ : W → F → ℝ

def profit {W : Type} [DecidableEq W] (y : Finset W → ℝ)
    (C : Finset W) (s : W → ℝ) : ℝ := y C - ∑ i ∈ C, s i

def IsDemanded {W : Type} [DecidableEq W] (y : Finset W → ℝ)
    (s : W → ℝ) (C : Finset W) : Prop :=
  ∀ C' : Finset W, profit y C' s ≤ profit y C s

def GrossSubstitutesOn {W : Type} [DecidableEq W] (y : Finset W → ℝ)
    (S : Set (W → ℝ)) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, s ≤ s' → ∀ C, IsDemanded y s C →
    ∃ C', IsDemanded y s' C' ∧ C.filter (fun i => s' i = s i) ⊆ C'

structure Allocation (W F : Type) where
  assign : W → F
  sal : W → ℝ

def Allocation.hired {W F : Type} [Fintype W] [DecidableEq W] [DecidableEq F]
    (A : Allocation W F) (j : F) : Finset W :=
  Finset.univ.filter (fun i => A.assign i = j)

def Market.IsIR {W F : Type} [Fintype W] [DecidableEq W] [Fintype F]
    [DecidableEq F] (M : Market W F) (A : Allocation W F) : Prop :=
  (∀ i, M.σ i (A.assign i) ≤ A.sal i) ∧
    ∀ j, 0 ≤ profit (M.y j) (A.hired j) A.sal

def Market.CanImprove {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ),
    (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) ≤ M.u i j (r i)) ∧
    profit (M.y j) (A.hired j) A.sal ≤ profit (M.y j) C r ∧
    ((∃ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∨
      profit (M.y j) (A.hired j) A.sal < profit (M.y j) C r)

def Market.IsStrictCore {W F : Type} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanImprove R A

end KelsoCrawford.OneSided


