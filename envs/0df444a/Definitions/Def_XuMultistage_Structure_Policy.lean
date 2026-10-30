-- Prove2me | Definitions.Def_XuMultistage_Structure_Policy
-- name    : XuMultistage_Structure_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T00:23:40.60261+00:00
-- url     : https://prove2.me/theorems/4c44eae2-ed45-41fe-84fd-590c3978c337
-- title:
--   Deterministic policies and feasible binary path matrices
-- statement:
--   A deterministic commitment policy is an initial assortment $S\subseteq N^1$ and a continuation assortment $B_i\subseteq N^2$ after every active choice $i\in S\cup\{0\}$. Every assortment may be empty. In particular $B_0$ is freely chosen. Continuations are stored also for inactive first-stage choices but those values do not affect any choice probability or revenue.
--
--   A binary path matrix $X$ is feasible precisely when
--   $$X_{00}=1,\qquad X_{ij}=1\Longrightarrow X_{i0}=1.$$
--   The policy's matrix is $X_{ij}=1$ exactly when $i\in S\cup\{0\}$ and $j\in B_i\cup\{0\}$. Conversely, ordinary products in a feasible matrix are recovered as $S=\{i>0:X_{i0}=1\}$ and $B_i=\{j>0:X_{ij}=1\}$. The operation $\operatorname{setPath}(X,i,j,b)$ changes only entry $(i,j)$ to $b$.
--
--   These are all deterministic policies and all matrices feasible for (5) and (9); revenue ordering, nesting, and optimality are not feasibility constraints.
--
--   **Formalization Note** Binary entries are Booleans. Both stage-specific finite types contain option zero; the policy's ordinary assortments explicitly exclude it. Recovering a policy from an infeasible matrix is a total operation, but only feasible matrices represent the source's solutions.
-- source:
--   Xu and Wang, Assortment Optimization for a Multi-Stage Choice Model, https://doi.org/10.1287/msom.2023.1224, held source.pdf (published citation basis; SSRN footer 3243742; catalog label 2018, PDF metadata 2023; PDF pages equal printed pages), §4, p. 11; §4.2, p. 14, constraints in (5); (9), pp. 18–19

import Mathlib

namespace XuMultistage.Structure

/-- A binary matrix of offered paths, including both outside-option indices. -/
abbrev PathMatrix (n₁ n₂ : ℕ) := Fin (n₁ + 1) → Fin (n₂ + 1) → Bool

/-- Exactly the constraints in (5) and (9). -/
def Feasible {n₁ n₂ : ℕ} (X : PathMatrix n₁ n₂) : Prop :=
  X 0 0 = true ∧ ∀ i j, X i j = true → X i 0 = true

/-- Change only one path, leaving the rest of the matrix unchanged. -/
def setPath {n₁ n₂ : ℕ} (X : PathMatrix n₁ n₂)
    (i : Fin (n₁ + 1)) (j : Fin (n₂ + 1)) (b : Bool) : PathMatrix n₁ n₂ :=
  fun k l => if k = i ∧ l = j then b else X k l

/-- A deterministic committed two-stage policy. Unavailable rows are irrelevant;
no-purchase continuation is a free assortment. No structure is required of the assortments. -/
structure Policy (n₁ n₂ : ℕ) where
  first : Finset (Fin (n₁ + 1))
  next : Fin (n₁ + 1) → Finset (Fin (n₂ + 1))
  first_noZero : 0 ∉ first
  next_noZero : ∀ i, 0 ∉ next i

/-- Convert assortments to the offered-path indicators, adding outside options. -/
def Policy.paths {n₁ n₂ : ℕ} (π : Policy n₁ n₂) : PathMatrix n₁ n₂ :=
  fun i j => decide ((i = 0 ∨ i ∈ π.first) ∧ (j = 0 ∨ j ∈ π.next i))

/-- Recover the ordinary assortments; inactive rows become empty on feasible matrices. -/
def policyOfPaths {n₁ n₂ : ℕ} (X : PathMatrix n₁ n₂) : Policy n₁ n₂ where
  first := Finset.univ.filter (fun i => i ≠ 0 ∧ X i 0 = true)
  next := fun i => Finset.univ.filter (fun j => j ≠ 0 ∧ X i j = true)
  first_noZero := by simp
  next_noZero := by intro i; simp

end XuMultistage.Structure


