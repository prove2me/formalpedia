-- Prove2me | Definitions.Def_MasekPaterson_Shared_steps
-- name    : MasekPaterson_Shared_steps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:02:12.107315+00:00
-- url     : https://prove2.me/theorems/8421baca-3348-439a-afbe-32ce16d1a4bb
-- title:
--   Steps of edit matrices and discreteness of the cost set $\Omega$
-- statement:
--   Let $\gamma$ be a cost function on the edit operations over an alphabet $\Sigma$, and let $\delta_{i,j} = \delta(\gamma, A^i, B^j)$ be the edit matrix of strings $A, B$ (see the definition of the edit distance).
--
--   A **step** is the difference between two vertically or horizontally adjacent entries of an edit matrix: a vertical step $\delta_{i,j} - \delta_{i-1,j}$ with $1 \le i \le |A|$, $0 \le j \le |B|$, or a horizontal step $\delta_{i,j} - \delta_{i,j-1}$ with $0 \le i \le |A|$, $1 \le j \le |B|$. The **set of possible steps** of $\gamma$ is the set of all such differences, over all pairs of strings $A, B \in \Sigma^*$.
--
--   The **cost set** is
--
--   $$\Omega = \{D_a \mid a \in \Sigma\} \cup \{I_a \mid a \in \Sigma\} \cup \{R_{a,b} \mid a, b \in \Sigma\},$$
--
--   and $\Omega$ is **discrete** if there is a constant $r > 0$ such that every element of $\Omega$ is an integral multiple of $r$.
--
--   Discreteness is the restriction on costs under which the Masek–Paterson algorithm works: it makes the set of possible steps finite (Lemma 4), so the submatrix table of Algorithm Y ranges over a finite set of step vectors. Without discreteness the set of possible steps can be infinite (Section 3, Theorem 5, p. 30).
--
--   Used by both missions of this paper: 01-four-russians (Lemma 4 and the correctness of Algorithm Z, pp. 23–24; steps defined p. 21, $\Omega$ and discreteness p. 23) and 02-discreteness-necessary (Theorem 5 and the example cost function of Section 3, pp. 28–30, which satisfies every condition but discreteness).
--
--   **Formalization Note** The paper writes "The set $\Omega$ is discrete only if there exists some constant $r$ such that …"; the "only if" is read as the definition. The constant is required to be positive: if the paper's $r$ were $0$, then $\Omega = \{0\}$ and $r = 1$ also works, so nothing is lost. Steps on the boundary row and column ($j = 0$ or $i = 0$) are included, since Algorithm Z feeds them to the table.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 21, Section 2.1 (definition of step); p. 23 (definition of Ω and of discrete)

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist

namespace MasekPaterson.Shared

variable {α : Type*}

/-- The set of possible steps for the cost function `γ`: every difference between two
vertically adjacent entries, `δ_{i,j} - δ_{i-1,j}` (`1 ≤ i ≤ |A|`, `0 ≤ j ≤ |B|`), or two
horizontally adjacent entries, `δ_{i,j} - δ_{i,j-1}` (`0 ≤ i ≤ |A|`, `1 ≤ j ≤ |B|`), of the
edit matrix of some pair of strings `A, B` over the alphabet. -/
def possibleSteps (γ : EditOp α → ℝ) : Set ℝ :=
  {s : ℝ | ∃ (A B : List α) (i j : ℕ),
    (1 ≤ i ∧ i ≤ A.length ∧ j ≤ B.length ∧ s = dmat γ A B i j - dmat γ A B (i - 1) j) ∨
    (i ≤ A.length ∧ 1 ≤ j ∧ j ≤ B.length ∧ s = dmat γ A B i j - dmat γ A B i (j - 1))}

/-- `Ω = {D_a | a ∈ Σ} ∪ {I_a | a ∈ Σ} ∪ {R_{a,b} | a, b ∈ Σ}`, the set of edit costs. -/
def costSet (γ : EditOp α → ℝ) : Set ℝ :=
  {x | ∃ a, x = delCost γ a} ∪ {x | ∃ a, x = insCost γ a} ∪ {x | ∃ a b, x = replCost γ a b}

/-- `Ω` is discrete: there is a constant `r > 0` such that every element of `Ω` is an
integral multiple of `r`. -/
def IsDiscrete (γ : EditOp α → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ ω ∈ costSet γ, ∃ z : ℤ, ω = z * r

end MasekPaterson.Shared


