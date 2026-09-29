-- Prove2me | Definitions.Def_JohnsonApprox_SetCover_Problem
-- name    : JohnsonApprox_SetCover_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:24:47.897491+00:00
-- url     : https://prove2.me/theorems/36fcd86b-268d-4a86-90dd-47d075d328d7
-- title:
--   SET COVERING I: families, subcovers, the optimum F* and the subproblem SC(k) (Section 5)
-- statement:
--   This file sets up the minimization problem SET COVERING I (SC) of Johnson (1974), Section 5, which the paper describes as follows:
--   $$\mathrm{INPUT}_{SC} = \{F : F \text{ is a finite family } \{S_1, S_2, \dots, S_p\} \text{ of finite sets}\},$$
--   $$\mathrm{SOL}_{SC}(F) = \Big\{F' \subseteq F : \bigcup_{S \in F'} S = \bigcup_{S \in F} S\Big\}, \qquad m_{SC}(F') = |F'|.$$
--
--   1. An input is a finite family of finite sets $S_i$, $i \in \iota$, over a ground type $\alpha$. The **family** $F = \{S_i : i \in \iota\}$ is the finite set of these sets, and the set to be covered is $T = \bigcup_{S \in F} S$.
--   2. A **subcover** is a subfamily $F' \subseteq F$ whose union is $T$. The family $F$ itself is a subcover, so $\mathrm{SOL}_{SC}(F)$ is nonempty.
--   3. The optimal measure is the minimum cardinality of a subcover,
--   $$F^* = \min\{|F'| : F' \in \mathrm{SOL}_{SC}(F)\}.$$
--   4. "SC(k) will denote the subproblem with inputs restricted to families, no set of which has more than $k$ elements": $F \in SC(k)$ iff $|S_i| \le k$ for every $i$.
--
--   These are the objects about which Theorem 4 (the greedy algorithm C1) is stated.
--
--   **Formalization Note** The family is given as an indexed family `S : ι → Finset α` over a finite index type `ι`, which plays the role of the indices $1, \dots, p$; algorithm C1 chooses indices. Two indices may carry the same set; the family `family S` is the image, a set of sets, and subcovers and $F^*$ are taken over subfamilies of it, as on the page. `opt S` is `Finset.inf'` of the cardinality over the finite, nonempty set `subcovers S` (nonemptiness is the lemma `family_mem_subcovers`, proved in the file). If $T = \emptyset$ then $\emptyset$ is a subcover and $F^* = 0$.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), pp. 264–265, Section 5 (SET COVERING I, INPUT_SC, SOL_SC, m_SC, SC(k)); pp. 258–259, Section 2

import Mathlib

namespace JohnsonApprox.SetCover

/-!
SET COVERING I (Johnson 1974, Section 5, pp. 264–265).

An input is a finite family `{S_1, …, S_p}` of finite sets, given as an indexed family
`S : ι → Finset α` over a finite index type `ι` (the paper's `1, …, p`). The indices are what
algorithm C1 chooses from ("Choose j ≤ N"). Two indices may carry the same set.
-/

variable {ι α : Type} [Fintype ι] [DecidableEq α]

/-- The family `F = {S_i : i ∈ ι}` as a finite set of finite sets. -/
def family (S : ι → Finset α) : Finset (Finset α) := Finset.univ.image S

/-- The set to be covered, `T = ⋃_{S ∈ F} S`. -/
def ground (S : ι → Finset α) : Finset α := Finset.univ.biUnion S

/-- The feasible solutions `SOL_SC(F) = {F' ⊆ F : ⋃_{S ∈ F'} S = ⋃_{S ∈ F} S}` (the subcovers). -/
def subcovers (S : ι → Finset α) : Finset (Finset (Finset α)) :=
  (family S).powerset.filter (fun F' => F'.biUnion id = ground S)

/-- `F` itself is a subcover, so `SOL_SC(F)` is nonempty. -/
theorem family_mem_subcovers (S : ι → Finset α) : family S ∈ subcovers S := by
  unfold subcovers family ground
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_powerset_self _, by rw [Finset.image_biUnion]; rfl⟩

/-- The optimal measure `F* = MIN{|F'| : F' ∈ SOL_SC(F)}` (with `m_SC(F') = |F'|`), a minimum
over a finite nonempty set. -/
def opt (S : ι → Finset α) : ℕ :=
  (subcovers S).inf' ⟨family S, family_mem_subcovers S⟩ Finset.card

/-- `F` is an input of `SC(k)`: no set of the family has more than `k` elements. -/
def InSC (k : ℕ) (S : ι → Finset α) : Prop := ∀ i, (S i).card ≤ k

end JohnsonApprox.SetCover


