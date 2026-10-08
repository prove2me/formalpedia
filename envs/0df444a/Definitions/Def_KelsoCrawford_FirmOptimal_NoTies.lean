-- Prove2me | Definitions.Def_KelsoCrawford_FirmOptimal_NoTies
-- name    : KelsoCrawford_FirmOptimal_NoTies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:28.267305+00:00
-- url     : https://prove2.me/theorems/e3cdb12a-0387-49b0-a139-0b66d6728657
-- title:
--   Section 5, p. 1494 — (strictly) s-possible, and the no-ties conditions (NTW), (NTF)
-- statement:
--   Fix a discrete market with salary unit $\delta$.
--
--   Worker $i$ is **$s$-possible** for firm $j$ if some discrete core allocation (D3) assigns $i$ to $j$ at salary $s$, and **strictly $s$-possible** if some discrete strict core allocation (D2) does.
--
--   The **no-ties condition for workers (NTW)** requires: whenever worker $i$ is $s_{ij}$-possible for firm $j$, then for every other firm $k$ and every salary $s_{ik}$ that $k$ is permitted to offer $i$,
--   $$u^i(j; s_{ij}) \neq u^i(k; s_{ik}).$$
--
--   The **no-ties condition for firms (NTF)** requires: whenever a discrete core allocation assigns the set $C^j$ to firm $j$ at salaries $s^j$, then for every other nonempty set $\tilde C$ and every salary vector $\tilde s^j$ of permitted salaries,
--   $$y^j(C^j) - \sum_{i \in C^j} s_{ij} \neq y^j(\tilde C) - \sum_{i \in \tilde C} \tilde s_{ij}.$$
--
--   Together these say that no worker or firm is indifferent between what it gets in a core allocation and any other assignment permitted in the discrete market. They are the hypotheses of Theorem 4 and of its Corollary.
--
--   **Formalization Note** Both conditions quantify over discrete core allocations (D3), as printed. "Any other non-empty set of workers $\tilde C$" is read as $\tilde C \neq C^j$: for the same set at other permitted salaries equal profits cannot be excluded in general (shift one unit of salary between two workers). (NTW) is stated directly on core allocations, which is the same as stating it for every $s_{ij}$-possible pair.
-- source:
--   Kelso and Crawford, Job matching, coalition formation, and gross substitutes, Econometrica 50 (1982), p. 1494, Section 5, definition of (strictly) s-possible, (NTW), (NTF)

import Mathlib
import Definitions.Def_KelsoCrawford_FirmOptimal_Model

namespace KelsoCrawford.FirmOptimal

variable {W F : Type} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]

/-- Worker `i` is `s`-possible for firm `j` (p. 1494): some discrete core allocation of the
discrete market with unit `δ` assigns `i` to `j` at salary `s`. -/
def Market.Possible (M : Market W F) (δ : ℝ) (i : W) (j : F) (s : ℝ) : Prop :=
  ∃ A, M.IsCore (M.grid δ) A ∧ A.assign i = j ∧ A.sal i = s

/-- Worker `i` is strictly `s`-possible for firm `j` (p. 1494): some discrete strict core
allocation of the discrete market with unit `δ` assigns `i` to `j` at salary `s`. -/
def Market.StrictlyPossible (M : Market W F) (δ : ℝ) (i : W) (j : F) (s : ℝ) : Prop :=
  ∃ A, M.IsStrictCore (M.grid δ) A ∧ A.assign i = j ∧ A.sal i = s

/-- (NTW), p. 1494: no worker is indifferent between the assignment and salary he or she has in a
discrete core allocation and any other firm at any salary that firm is permitted to offer. -/
def Market.NTW (M : Market W F) (δ : ℝ) : Prop :=
  ∀ A, M.IsCore (M.grid δ) A → ∀ i (k : F), k ≠ A.assign i →
    ∀ r ∈ M.grid δ i k, M.u i (A.assign i) (A.sal i) ≠ M.u i k r

/-- (NTF), p. 1494: no firm earns, at permitted salaries, from a nonempty set of workers other
than the one a discrete core allocation assigns to it, exactly the KelsoCrawford.Process.profit it earns there. -/
def Market.NTF (M : Market W F) (δ : ℝ) : Prop :=
  ∀ A, M.IsCore (M.grid δ) A → ∀ (j : F) (C : Finset W), C.Nonempty → C ≠ A.hired j →
    ∀ r ∈ M.gridVectors δ j, KelsoCrawford.Process.profit (M.y j) (A.hired j) A.sal ≠ KelsoCrawford.Process.profit (M.y j) C r

end KelsoCrawford.FirmOptimal


