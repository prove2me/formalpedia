-- Prove2me | Definitions.Def_KelsoCrawford_Process_Model
-- name    : KelsoCrawford_Process_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:12:54.933654+00:00
-- url     : https://prove2.me/theorems/f96618cf-eda0-4d93-bbc6-23dbea5becf9
-- title:
--   Section 2, pp. 1486–1488 — job-matching market, (MP), (NFL), (GS), the discrete salary grid, allocations, individual rationality (D1) and the discrete core (D3)
-- statement:
--   There are finitely many workers $i \in W$ and finitely many firms $j \in F$ (the paper's $\{1,\dots,m\}$ and $\{1,\dots,n\}$). A **market** consists of
--
--   1. utilities $u^i(j; s)$: worker $i$'s utility of working for firm $j$ at salary $s \in \mathbb R$;
--   2. gross products $y^j(C) \in \mathbb R$: firm $j$'s output when it hires the set $C \subseteq W$;
--   3. starting salaries $\sigma_{ij} \in \mathbb R$, the lowest salary at which worker $i$ would consider working for firm $j$.
--
--   Given a salary vector $s^j = (s_{1j},\dots,s_{mj})$ facing firm $j$, its **net profit** from hiring $C$ is
--   $$\pi^j(C; s^j) = y^j(C) - \sum_{i \in C} s_{ij},$$
--   and $M^j(s^j)$ is the set of profit-maximizing sets $C$ (problem (A)). The standing assumptions of p. 1486 are:
--
--   1. **regularity**: each $u^i(j;\cdot)$ is strictly increasing and continuous;
--   2. **(MP)**: $y^j(C \cup \{i\}) - y^j(C) - \sigma_{ij} \ge 0$ for all $i, j$ and all $C \not\ni i$;
--   3. **(NFL)**: $y^j(\emptyset) = 0$ for every $j$;
--   4. **(GS)**, relative to a set $S$ of admissible salary vectors: if $C \in M^j(s^j)$ and $\tilde s^j \ge s^j$ (both in $S$), there is $\tilde C \in M^j(\tilde s^j)$ with $T^j(C) \subseteq \tilde C$, where $T^j(C) = \{ i \in C : \tilde s_{ij} = s_{ij}\}$.
--
--   In the **discrete market with unit $\delta > 0$**, firm $j$ may pay worker $i$ only the salaries $\sigma_{ij} + k\delta$, $k = 0, 1, 2, \dots$; the corresponding salary vectors form the set $S$ used for (GS).
--
--   An **allocation** assigns each worker $i$ to a firm $f(i)$ at a salary $s_{if(i)}$; $C^j = \{i : f(i) = j\}$. It is **individually rational** (D1) if $s_{if(i)} \ge \sigma_{if(i)}$ for every $i$ and $\pi^j(C^j; s^j) \ge 0$ for every $j$. A firm $j$, a set $C$ of workers and salaries $r^j$ **strictly improve upon** the allocation if
--   $$u^i(j; r_{ij}) > u^i(f(i); s_{if(i)}) \ \text{ for all } i \in C, \qquad \pi^j(C; r^j) > \pi^j(C^j; s^j).$$
--   A **(discrete) core allocation** (D3) is an individually rational allocation, paying permitted salaries, that no firm and set of workers can strictly improve upon using permitted salaries.
--
--   These are the objects of Theorem 1 and its lemmas.
--
--   **Formalization Note** The starting salaries $\sigma_{ij}$ are data; the paper's defining relation $u^i(j;\sigma_{ij}) = u^i(0;0)$ is not imposed (Theorem 1 does not use it). The set of permitted salaries is a parameter `R` of the core: the discrete market uses `M.grid δ`. Every worker is assigned to some firm (as the paper's $f : \{1,\dots,m\} \to \{1,\dots,n\}$); the coalition $C$ may be empty. (GS) is stated for one firm (`GrossSubstitutesOn`) and relative to the admissible salary vectors, because the paper notes (p. 1487) that a discrete market may satisfy (GS) while the continuous one does not.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1486–1488, Section 2 (model, (MP), (NFL), (A), (GS); D1, D3)

import Mathlib

namespace KelsoCrawford.Process

/-- A job-matching market (Kelso–Crawford 1982, §2, p. 1486): `u i j s` is worker `i`'s utility of
working for firm `j` at salary `s`; `y j C` is firm `j`'s gross product when it hires the set `C`
of workers; `σ i j` is the starting (lowest) salary of worker `i` at firm `j`. -/
structure Market (W F : Type) where
  u : W → F → ℝ → ℝ
  y : F → Finset W → ℝ
  σ : W → F → ℝ

variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

/-- Net profit `π^j(C; s^j) = y^j(C) − Σ_{i ∈ C} s_ij` of a firm with gross product `y`, hiring `C`
at the salary vector `s`. -/
def profit (y : Finset W → ℝ) (C : Finset W) (s : W → ℝ) : ℝ :=
  y C - ∑ i ∈ C, s i

/-- `C ∈ M^j(s^j)`: the set `C` maximizes profit at the salary vector `s` over all sets of
workers (problem (A), p. 1486). -/
def IsDemanded (y : Finset W → ℝ) (s : W → ℝ) (C : Finset W) : Prop :=
  ∀ C' : Finset W, profit y C' s ≤ profit y C s

/-- Gross substitutes (GS), p. 1486, for one firm, over the set `S` of admissible salary
vectors: if `C ∈ M(s)` and `s ≤ s'` (both in `S`), there is `C' ∈ M(s')` containing every member
of `C` whose salary did not change. -/
def GrossSubstitutesOn (y : Finset W → ℝ) (S : Set (W → ℝ)) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, s ≤ s' → ∀ C, IsDemanded y s C →
    ∃ C', IsDemanded y s' C' ∧ C.filter (fun i => s' i = s i) ⊆ C'

/-- Every utility `u^i(j; ·)` is strictly increasing and continuous in the salary (p. 1486). -/
def Market.UtilityRegular (M : Market W F) : Prop :=
  ∀ i j, StrictMono (M.u i j) ∧ Continuous (M.u i j)

/-- (MP), p. 1486: `y^j(C ∪ {i}) − y^j(C) − σ_ij ≥ 0` for all `i, j` and all `C ∌ i`. -/
def Market.MP (M : Market W F) : Prop :=
  ∀ i j (C : Finset W), i ∉ C →
    0 ≤ M.y j (insert i C) - M.y j C - M.σ i j

/-- (NFL), p. 1486: `y^j(∅) = 0` for every firm. -/
def Market.NFL (M : Market W F) : Prop := ∀ j, M.y j ∅ = 0

/-- The salaries firm `j` may offer worker `i` in the discrete market with unit `δ`:
`σ_ij, σ_ij + δ, σ_ij + 2δ, …`. -/
def Market.grid (M : Market W F) (δ : ℝ) (i : W) (j : F) : Set ℝ :=
  {r | ∃ k : ℕ, r = M.σ i j + k * δ}

/-- Salary vectors of firm `j` all of whose entries are permitted salaries. -/
def Market.gridVectors (M : Market W F) (δ : ℝ) (j : F) : Set (W → ℝ) :=
  {s | ∀ i, s i ∈ M.grid δ i j}

/-- An allocation (D1, p. 1488): every worker `i` is assigned to the firm `assign i` at the
salary `sal i`. -/
structure Allocation (W F : Type) where
  assign : W → F
  sal : W → ℝ

/-- `C^j = {i | f(i) = j}`, the workers hired by firm `j`. -/
def Allocation.hired (A : Allocation W F) (j : F) : Finset W :=
  Finset.univ.filter (fun i => A.assign i = j)

/-- Individual rationality, D1 (1)–(2), p. 1488. -/
def Market.IsIR (M : Market W F) (A : Allocation W F) : Prop :=
  (∀ i, M.σ i (A.assign i) ≤ A.sal i) ∧
    ∀ j, 0 ≤ profit (M.y j) (A.hired j) A.sal

/-- A firm `j`, a set `C` of workers and salaries `r` (with `r i ∈ R i j` for `i ∈ C`) strictly
improve upon `A`: (3) and (4) of p. 1488 both hold with strict inequality (D3). -/
def Market.CanStrictlyImprove (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ),
    (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∧
    profit (M.y j) (A.hired j) A.sal < profit (M.y j) C r

/-- A (discrete) core allocation, D3, p. 1488, with permitted salaries `R`: individually
rational, paying permitted salaries, and not strictly improvable by any coalition of one firm
and a set of workers using permitted salaries. -/
def Market.IsCore (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanStrictlyImprove R A

end KelsoCrawford.Process


