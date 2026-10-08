-- Prove2me | Definitions.Def_KelsoCrawford_FirmOptimal_Model
-- name    : KelsoCrawford_FirmOptimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:09.464655+00:00
-- url     : https://prove2.me/theorems/27beedc3-1153-4b91-a893-4c33f33d8cc3
-- title:
--   Section 2, pp. 1486–1488 — job-matching market, (MP), (NFL), (GS), discrete salaries, allocations, strict core (D2) and core (D3)
-- statement:
--   This definition file sets up the job-matching model of Kelso and Crawford.
--
--   There are finitely many workers $i \in W$ and finitely many firms $j \in F$. A **market** consists of
--
--   1. utilities $u^i(j; s)$: worker $i$'s utility of working for firm $j$ at salary $s \in \mathbb{R}$;
--   2. production functions $y^j(C)$: firm $j$'s gross product when it hires the set $C \subseteq W$ of workers;
--   3. starting permitted salaries $\sigma_{ij} \in \mathbb{R}$, initially defined as reservation salaries in Section 2 and permitted to be perturbed in Section 5.
--
--   Facing the salary vector $s^j = (s_{1j}, \dots, s_{mj})$, firm $j$ earns the **net profit**
--   $$\pi^j(C; s^j) = y^j(C) - \sum_{i \in C} s_{ij}$$
--   from hiring $C$, and $M^j(s^j)$ is the set of profit-maximizing sets $C$ (problem (A)). The standing assumptions of the paper are:
--
--   - **regularity**: each $u^i(j; \cdot)$ is strictly increasing and continuous;
--   - **(MP)**: $y^j(C \cup \{i\}) - y^j(C) - \sigma_{ij} \ge 0$ for all $(i, j)$ and all $C$ with $i \notin C$;
--   - **(NFL)**: $y^j(\varnothing) = 0$ for all $j$;
--   - **(GS)** (for one firm, over a set $S$ of allowed salary vectors): if $C \in M^j(s^j)$ and $\tilde s^j \ge s^j$ with both in $S$, then some $\tilde C \in M^j(\tilde s^j)$ contains $T^j(C) = \{ i \in C : \tilde s_{ij} = s_{ij}\}$.
--
--   In the **discrete market with salary unit $\delta$**, firm $j$ may offer worker $i$ the salaries $\sigma_{ij} + k\delta$, $k = 0, 1, 2, \dots$; the corresponding salary vectors form the set on which (GS) is imposed.
--
--   An **allocation** $(f; s_{1f(1)}, \dots, s_{mf(m)})$ assigns every worker $i$ to a firm $f(i)$ at salary $s_{if(i)}$; $C^j = \{ i : f(i) = j \}$. It is **individually rational** (D1) if $s_{if(i)} \ge \sigma_{if(i)}$ for every $i$ and $\pi^j(C^j; s^j) \ge 0$ for every $j$. A firm $j$ and a set $C$ of workers with permitted salaries $r^j$ **improve upon** the allocation if
--   $$u^i(j; r_{ij}) \ge u^i[f(i); s_{if(i)}] \ \ (i \in C), \qquad \pi^j(C; r^j) \ge \pi^j(C^j; s^j),$$
--   with strict inequality for at least one member of $C \cup \{j\}$; they **strictly improve upon** it if all these inequalities are strict. A **(discrete) strict core allocation** (D2) is an individually rational allocation at permitted salaries that no coalition can improve upon; a **(discrete) core allocation** (D3) is one that no coalition can strictly improve upon.
--
--   These objects are the vocabulary of every statement in this mission.
--
--   **Formalization Note** The starting salaries $\sigma_{ij}$ are data; the paper's initial defining relation $u^i(j;\sigma_{ij}) = u^i(0;0)$ is not imposed, as in Section 5, where the $\sigma_{ij}$ are perturbed independently of $u^i(0;0)$. The core notions take the sets of permitted salaries as a parameter $R$; this mission always uses the discrete grid. Allocations have no unemployment (as in D1, $f$ is a function into the firms). The coalition $C = \varnothing$ is allowed, as in the paper.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1486–1488, Section 2, (MP), (NFL), (A), (GS), D1–D3; p. 1496 (discrete market, unit size)

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model

namespace KelsoCrawford.FirmOptimal

/-- A job-matching market (Kelso–Crawford 1982, §2, p. 1486): `u i j s` is worker `i`'s utility
of working for firm `j` at salary `s`, `y j C` is firm `j`'s gross product when it hires the set
`C` of workers, and `σ i j` is the lowest salary at which `i` would consider working for `j`. -/
structure Market (W F : Type) where
  u : W → F → ℝ → ℝ
  y : F → Finset W → ℝ
  σ : W → F → ℝ

variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

/-- Every utility `u^i(j; ·)` is strictly increasing and continuous. -/
def Market.UtilityRegular (M : Market W F) : Prop :=
  ∀ i j, StrictMono (M.u i j) ∧ Continuous (M.u i j)

/-- (MP): `y^j(C ∪ {i}) − y^j(C) − σ_ij ≥ 0` for all `(i, j)` and all `C` with `i ∉ C`. -/
def Market.MP (M : Market W F) : Prop :=
  ∀ i j (C : Finset W), i ∉ C → 0 ≤ M.y j (insert i C) - M.y j C - M.σ i j

/-- (NFL): `y^j(∅) = 0` for all `j`. -/
def Market.NFL (M : Market W F) : Prop := ∀ j, M.y j ∅ = 0

/-- Permitted salaries of a discrete market with unit `δ`: `σ_ij + kδ`, `k ∈ ℕ`. -/
def Market.grid (M : Market W F) (δ : ℝ) (i : W) (j : F) : Set ℝ :=
  {r | ∃ k : ℕ, r = M.σ i j + k * δ}

/-- Salary vectors firm `j` is permitted to offer in the discrete market with unit `δ`. -/
def Market.gridVectors (M : Market W F) (δ : ℝ) (j : F) : Set (W → ℝ) :=
  {s | ∀ i, s i ∈ M.grid δ i j}

/-- An allocation `(f; s_{1f(1)}, …, s_{mf(m)})`: every worker is assigned to a firm and paid a
salary there. -/
structure Allocation (W F : Type) where
  assign : W → F
  sal : W → ℝ

/-- `C^j = {i | f(i) = j}`, the workers hired by firm `j`. -/
def Allocation.hired (A : Allocation W F) (j : F) : Finset W :=
  Finset.univ.filter (fun i => A.assign i = j)

/-- D1: individual rationality, (1) and (2). -/
def Market.IsIR (M : Market W F) (A : Allocation W F) : Prop :=
  (∀ i, M.σ i (A.assign i) ≤ A.sal i) ∧ ∀ j, 0 ≤ KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal

/-- A coalition `(j, C)` with salaries `r` in `R` satisfying (3) and (4), with strict inequality
for at least one member of `C ∪ {j}`, improves upon `A`. -/
def Market.CanImprove (M : Market W F) (R : W → F → Set ℝ) (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ), (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) ≤ M.u i j (r i)) ∧
    KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal ≤ KelsoCrawford.Process.profit (M.y j) C r ∧
    ((∃ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∨
      KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal < KelsoCrawford.Process.profit (M.y j) C r)

/-- A coalition satisfying both (3) and (4) with strict inequality strictly improves upon `A`. -/
def Market.CanStrictlyImprove (M : Market W F) (R : W → F → Set ℝ) (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ), (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∧
    KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal < KelsoCrawford.Process.profit (M.y j) C r

/-- D2: a (discrete) strict core allocation for the salary sets `R`. -/
def Market.IsStrictCore (M : Market W F) (R : W → F → Set ℝ) (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanImprove R A

/-- D3: a (discrete) core allocation for the salary sets `R`. -/
def Market.IsCore (M : Market W F) (R : W → F → Set ℝ) (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanStrictlyImprove R A

end KelsoCrawford.FirmOptimal


