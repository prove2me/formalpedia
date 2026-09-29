-- Prove2me | Definitions.Def_JohnsonApprox_SubsetSum_Problem
-- name    : JohnsonApprox_SubsetSum_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:16:17.78598+00:00
-- url     : https://prove2.me/theorems/0a3a6c1b-58c7-49f5-8df3-410ed6b4b215
-- title:
--   SUBSET-SUM: inputs ⟨T, s, b⟩, approximate solutions, measure and optimum (Section 3)
-- statement:
--   This is the optimization problem SUBSET-SUM (SS) of Johnson (1974), a simple form of the knapsack problem, in the paper's formal framework of Section 2. The paper defines it as follows:
--
--   > INPUT_SS = {⟨T, s, b⟩: T is a finite set, s : T → Q+ is a map which assigns to each x ∈ T a "size" s(x), and b > 0 is a single rational number}.
--   > SOL_SS(⟨T, s, b⟩) = {T′ ⊆ T: Σ_{x∈T′} s(x) ≤ b}. m_SS(T′) = Σ_{x∈T′} s(x).
--
--   An **input** $u = \langle T, s, b\rangle$ consists of a finite set $T$, a size $s(x) > 0$ (a positive rational) for every $x \in T$, and a positive rational bound $b$. An **approximate solution** is a subset $T' \subseteq T$ whose total size is at most $b$, and its **measure** is
--
--   $$m(T') = \sum_{x \in T'} s(x).$$
--
--   SUBSET-SUM is a maximization problem, and the **optimal measure** is
--
--   $$\langle T, s, b\rangle^* = \max\{\, m(T') : T' \subseteq T,\ m(T') \le b \,\}.$$
--
--   The maximum is over a finite set that always contains $T' = \emptyset$ (measure $0 \le b$), so it exists; it equals $0$ when every element is larger than $b$.
--
--   These objects are the substrate for the approximation algorithms $A_k$ and Theorem 1 of the paper.
--
--   **Formalization Note** The ground set is a `Finset` $T$ of an arbitrary type $\alpha$; the size map is a function $\alpha \to \mathbb{Q}$ whose values are required to be positive on $T$ only (values off $T$ are never used). The set of approximate solutions is `feasibleSet u`, the powerset of $T$ filtered by $m(T') \le b$; `opt u` is `Finset.sup'` of the measure over it, with nonemptiness witnessed by $\emptyset$ (the lemma `empty_mem_feasibleSet`). `IsFeasible u T'` is the same condition as a predicate.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), pp. 258–259, Sections 2–3 (definition of SUBSET-SUM)

import Mathlib

namespace JohnsonApprox.SubsetSum

/-- An input `⟨T, s, b⟩` of SUBSET-SUM (Johnson 1974, p. 259): a finite set `T`, a size map
`s` that is a positive rational on every element of `T`, and a positive rational bound `b`. -/
structure Input (α : Type) where
  /-- The finite ground set `T`. -/
  T : Finset α
  /-- The size map `s : T → Q+` (only its values on `T` matter). -/
  s : α → ℚ
  /-- The bound `b`. -/
  b : ℚ
  s_pos : ∀ x ∈ T, 0 < s x
  b_pos : 0 < b

variable {α : Type}

/-- The measure `m_SS(T') = Σ_{x ∈ T'} s(x)`. -/
def measure (u : Input α) (T' : Finset α) : ℚ := ∑ x ∈ T', u.s x

/-- `T'` is an approximate solution: `T' ⊆ T` and `Σ_{x ∈ T'} s(x) ≤ b`. -/
def IsFeasible (u : Input α) (T' : Finset α) : Prop :=
  T' ⊆ u.T ∧ measure u T' ≤ u.b

/-- The finite set `SOL_SS(⟨T, s, b⟩)` of approximate solutions. -/
def feasibleSet (u : Input α) : Finset (Finset α) :=
  u.T.powerset.filter (fun T' => measure u T' ≤ u.b)

/-- The empty set is always an approximate solution, so `SOL_SS` is nonempty. -/
theorem empty_mem_feasibleSet (u : Input α) : (∅ : Finset α) ∈ feasibleSet u := by
  unfold feasibleSet
  rw [Finset.mem_filter]
  refine ⟨Finset.empty_mem_powerset _, ?_⟩
  rw [measure, Finset.sum_empty]
  exact u.b_pos.le

/-- The optimal measure `⟨T, s, b⟩* = MAX{m(T') : T' ⊆ T and m(T') ≤ b}`, a maximum over the
finite nonempty set of approximate solutions. -/
def opt (u : Input α) : ℚ :=
  (feasibleSet u).sup' ⟨∅, empty_mem_feasibleSet u⟩ (measure u)

end JohnsonApprox.SubsetSum


