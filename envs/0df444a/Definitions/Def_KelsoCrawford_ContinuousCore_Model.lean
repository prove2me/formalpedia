-- Prove2me | Definitions.Def_KelsoCrawford_ContinuousCore_Model
-- name    : KelsoCrawford_ContinuousCore_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:22.810448+00:00
-- url     : https://prove2.me/theorems/254f9b61-5b59-469b-be72-405c2d1846bf
-- title:
--   Sections 2 and 4 — job-matching market, gross substitutes, and core allocations
-- statement:
--   The job-matching market of Kelso and Crawford. There is a finite set $W$ of workers (the paper's $i=1,\dots,m$) and a finite set $F$ of firms (the paper's $j=1,\dots,n$). A **market** consists of
--
--   1. utilities $u^i(j;s)$: worker $i$'s utility of working for firm $j$ at salary $s\in\mathbb R$;
--   2. technologies $y^j(C)$: firm $j$'s gross product when it hires the set $C\subseteq W$;
--   3. reservation salaries $\sigma_{ij}\in\mathbb R$, the lowest salary at which worker $i$ would consider working for firm $j$.
--
--   Facing a salary vector $s^j=(s_{1j},\dots,s_{mj})$, firm $j$'s net profit from hiring $C$ is
--
--   $$\pi^j(C;s^j)=y^j(C)-\sum_{i\in C}s_{ij},$$
--
--   and $C$ is **demanded**, $C\in M^j(s^j)$, if it maximizes $\pi^j(\cdot\,;s^j)$ over all sets of workers (problem (A)).
--
--   The standing assumptions of Section 2 are named as follows. *Regular utilities*: each $u^i(j;\cdot)$ is strictly increasing and continuous. *(MP)*: $y^j(C\cup\{i\})-y^j(C)-\sigma_{ij}\ge 0$ for all $i,j$ and all $C\not\ni i$. *(NFL)*: $y^j(\emptyset)=0$ for all $j$. *Reservation salaries*: $u^i(j;\sigma_{ij})$ does not depend on $j$ (the paper defines $\sigma_{ij}$ by $u^i(j;\sigma_{ij})=u^i(0;0)$, the utility of unemployment). *(GS) on a set $S$ of salary vectors*: whenever $s^j,\tilde s^j\in S$, $s^j\le\tilde s^j$ componentwise and $C\in M^j(s^j)$, some $\tilde C\in M^j(\tilde s^j)$ contains $T^j(C)=\{i\in C:\tilde s_{ij}=s_{ij}\}$.
--
--   For a unit $\delta>0$, the **grid** of permitted salaries of the pair $(i,j)$ is $\{\sigma_{ij}+k\delta: k=0,1,2,\dots\}$; a grid salary vector of firm $j$ has every entry on its grid.
--
--   An **allocation** assigns every worker $i$ to a firm $f(i)$ and pays a salary $s_{if(i)}$; $C^j=\{i: f(i)=j\}$. It is **individually rational** (D1) if $s_{if(i)}\ge\sigma_{if(i)}$ for every $i$ and $\pi^j(C^j;s^j)\ge 0$ for every $j$. Given, for each pair $(i,j)$, a set $R_{ij}$ of salaries coalitions may use (all of $\mathbb R$ in the continuous market, the grid in a discrete one), a firm $j$, a set $C$ of workers and salaries $r_{ij}\in R_{ij}$ ($i\in C$) **improve upon** the allocation if
--
--   $$u^i(j;r_{ij})\ge u^i(f(i);s_{if(i)})\ (i\in C),\qquad \pi^j(C;r^j)\ge\pi^j(C^j;s^j),$$
--
--   with strict inequality for at least one member of $C\cup\{j\}$; they **strictly improve upon** it if all these inequalities are strict. A **strict core allocation** (D2) is an individually rational allocation paying salaries in $R$ that no coalition can improve upon; a **core allocation** (D3) is one that no coalition can strictly improve upon.
--
--   These are the objects of Theorem 2 and of its proof by discrete approximation.
--
--   **Formalization Note** $\sigma$ is part of the data, and its link to the unemployment utility is the separate predicate `ReservationSalaries`. An allocation has no unemployment ($f$ is a function into $F$), as in D1. The empty coalition $C=\emptyset$ is allowed, as in the paper; under (NFL) and D1 it can never improve. The paper's discrete salaries are "integer" with unit 1 starting at $\sigma_{ij}$ (R1, R4); here the unit is a general $\delta>0$, because the proof of Theorem 2 shrinks it.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), pp. 1486–1488, Section 2 (A), (MP), (NFL), (GS), (D1)–(D3); p. 1492, Section 4

import Mathlib
import Definitions.Def_KelsoCrawford_Process_Model

namespace KelsoCrawford.ContinuousCore

structure Market (W F : Type) where
  u : W → F → ℝ → ℝ
  y : F → Finset W → ℝ
  σ : W → F → ℝ

variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

def Market.UtilityRegular (M : Market W F) : Prop :=
  ∀ i j, StrictMono (M.u i j) ∧ Continuous (M.u i j)

def Market.MP (M : Market W F) : Prop :=
  ∀ i j (C : Finset W), i ∉ C →
    0 ≤ M.y j (insert i C) - M.y j C - M.σ i j

def Market.NFL (M : Market W F) : Prop := ∀ j, M.y j ∅ = 0

def Market.ReservationSalaries (M : Market W F) : Prop :=
  ∀ i j k, M.u i j (M.σ i j) = M.u i k (M.σ i k)

def Market.grid (M : Market W F) (δ : ℝ) (i : W) (j : F) : Set ℝ :=
  {r | ∃ k : ℕ, r = M.σ i j + k * δ}

def Market.gridVectors (M : Market W F) (δ : ℝ) (j : F) : Set (W → ℝ) :=
  {s | ∀ i, s i ∈ M.grid δ i j}

structure Allocation (W F : Type) where
  assign : W → F
  sal : W → ℝ

def Allocation.hired (A : Allocation W F) (j : F) : Finset W :=
  Finset.univ.filter (fun i => A.assign i = j)

def Market.IsIR (M : Market W F) (A : Allocation W F) : Prop :=
  (∀ i, M.σ i (A.assign i) ≤ A.sal i) ∧
    ∀ j, 0 ≤ KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal

def anySalary : W → F → Set ℝ := fun _ _ => Set.univ

def Market.CanImprove (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ),
    (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) ≤ M.u i j (r i)) ∧
    KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal ≤ KelsoCrawford.Process.profit (M.y j) C r ∧
    ((∃ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∨
      KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal < KelsoCrawford.Process.profit (M.y j) C r)

def Market.CanStrictlyImprove (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  ∃ (j : F) (C : Finset W) (r : W → ℝ),
    (∀ i ∈ C, r i ∈ R i j) ∧
    (∀ i ∈ C, M.u i (A.assign i) (A.sal i) < M.u i j (r i)) ∧
    KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal < KelsoCrawford.Process.profit (M.y j) C r

def Market.IsStrictCore (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanImprove R A

def Market.IsCore (M : Market W F) (R : W → F → Set ℝ)
    (A : Allocation W F) : Prop :=
  M.IsIR A ∧ (∀ i, A.sal i ∈ R i (A.assign i)) ∧ ¬ M.CanStrictlyImprove R A

end KelsoCrawford.ContinuousCore


