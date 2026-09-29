-- Prove2me | Definitions.Def_JohnsonApprox_ExactCover_Problem
-- name    : JohnsonApprox_ExactCover_Problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:29:26.843176+00:00
-- url     : https://prove2.me/theorems/4fa2b778-4a90-4134-abb1-ca5f38a2d1fa
-- title:
--   SET COVERING II (EC): inputs, subcovers, the measure Σ|S|, the optimum F* and EC(k) (Section 6)
-- statement:
--   This file sets up the problem SET COVERING II of Johnson (1974), Section 6, denoted EC. In the paper's words:
--   $$\mathrm{INPUT}_{EC} = \{F : F \text{ is a finite family } \{S_1, S_2, \dots, S_p\} \text{ of finite sets}\},$$
--   $$\mathrm{SOL}_{EC}(F) = \Big\{F' \subseteq F : \bigcup_{S \in F'} S = \bigcup_{S \in F} S\Big\}, \qquad m_{EC}(F') = \sum_{S \in F'} |S|.$$
--   "An optimal solution is a subcover of the set $T = \bigcup_{S\in F} S$ with the least possible overlapping. EC(k) will be the subproblem with inputs restricted to families, no set of which contains more than $k$ points."
--
--   1. An **input** is a number $p$ and sets $S_1, \dots, S_p$ (finite subsets of a type of points).
--   2. The **covered set** is $T = S_1 \cup \dots \cup S_p$.
--   3. A **subcover** is a set $M$ of indices with $\bigcup_{i \in M} S_i = T$; its **measure** is $m(M) = \sum_{i\in M} |S_i|$.
--   4. The **optimum** is $F^* = \min\{m(M) : M \text{ a subcover}\}$. The full index set is a subcover, so the minimum is over a finite nonempty family. EC is a minimization problem.
--   5. $F \in EC(k)$ when $|S_i| \le k$ for every $i$.
--
--   Since $m(M) \ge |T|$ for every subcover, $F^* - |T|$ is the least possible overlap. These are the objects about which Theorem 6 (algorithm C2) is stated.
--
--   **Formalization Note** The family is indexed by `Fin p` (0-based), so a set may occur twice; this only widens the input class, and a repeated set counts twice in the measure when both copies are chosen. Subcovers are index sets (`Finset (Fin p)`). $F^*$ is `Finset.inf'` of the measure over the finite, nonempty set `subcovers` (the lemma `subcovers_nonempty` supplies nonemptiness), so it is a genuine minimum, never a junk value.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 270, Section 6 (SET COVERING II); pp. 258–259, Section 2

import Mathlib

namespace JohnsonApprox.ExactCover

/-- An input of SET COVERING II (EC): a finite family `{S_1, …, S_p}` of finite sets, indexed by
`Fin p` (0-based). Repeated sets are allowed. -/
structure Input (α : Type) where
  p : ℕ
  S : Fin p → Finset α

variable {α : Type} [DecidableEq α]

/-- The covered set `T = ⋃_{S ∈ F} S`. -/
def Input.ground (F : Input α) : Finset α := Finset.univ.biUnion F.S

/-- `SOL_EC(F)`: the index set `M` describes a subcover, `⋃_{i ∈ M} S_i = ⋃_{S ∈ F} S`. -/
def Input.IsSubcover (F : Input α) (M : Finset (Fin F.p)) : Prop := M.biUnion F.S = F.ground

instance (F : Input α) (M : Finset (Fin F.p)) : Decidable (F.IsSubcover M) := by
  unfold Input.IsSubcover; infer_instance

/-- `m_EC(F′) = Σ_{S ∈ F′} |S|`. -/
def Input.measure (F : Input α) (M : Finset (Fin F.p)) : ℕ := ∑ i ∈ M, (F.S i).card

/-- The finite set of all subcovers (as index sets). -/
def Input.subcovers (F : Input α) : Finset (Finset (Fin F.p)) :=
  Finset.univ.filter F.IsSubcover

theorem Input.univ_mem_subcovers (F : Input α) : Finset.univ ∈ F.subcovers := by
  simp [Input.subcovers, Input.IsSubcover, Input.ground]

theorem Input.subcovers_nonempty (F : Input α) : F.subcovers.Nonempty :=
  ⟨_, F.univ_mem_subcovers⟩

/-- The optimum `F* = MIN {m_EC(F′) : F′ ∈ SOL_EC(F)}`, a minimum over a finite nonempty set. -/
def Input.opt (F : Input α) : ℕ := F.subcovers.inf' F.subcovers_nonempty F.measure

/-- `EC(k)`: no set of the family contains more than `k` points. -/
def InEC (k : ℕ) (F : Input α) : Prop := ∀ i, (F.S i).card ≤ k

end JohnsonApprox.ExactCover


