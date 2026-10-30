-- Prove2me | Definitions.Def_SubsamplingSM_Offline_IsSubmodular
-- name    : SubsamplingSM_Offline_IsSubmodular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:46:29.093165+00:00
-- url     : https://prove2.me/theorems/a06229b8-89fa-405c-a84d-a87b4a12e959
-- title:
--   Submodular set function, eq. (1)
-- statement:
--   A set function $f:2^N\to\mathbb R$ on a finite ground set $N$ is **submodular** if it has diminishing returns:
--   $$f(A\cup\{e\})-f(A)\ \ge\ f(B\cup\{e\})-f(B)\qquad\text{for all } A\subseteq B\subseteq N \text{ and } e\notin B.$$
--
--   This is inequality (1) of the paper, the standing assumption on the objective in problem (2).
--
--   **Formalization Note** No normalization $f(\emptyset)=0$ and no monotonicity is part of the definition.
-- source:
--   Harshaw, Kazemi, Feldman, Karbasi, The Power of Subsampling in Submodular Maximization, arXiv:2104.02772v1, §3, p. 5, eq. (1)

import Mathlib

namespace SubsamplingSM.Offline

/-- **Submodular set function**, eq. (1).
Harshaw, Kazemi, Feldman, Karbasi, *The Power of Subsampling in Submodular Maximization*,
arXiv:2104.02772v1, §3, p. 5, eq. (1): "Such a function f is submodular if
`f(A ∪ {e}) − f(A) ≥ f(B ∪ {e}) − f(B)` for all sets `A ⊆ B ⊆ N` and element `e ∉ B`."

The ground set `N` is the whole (finite) type `α` in every statement that uses this predicate;
sets are `Finset α` and `f : Finset α → ℝ`.

**Formalization Note.** No normalization `f ∅ = 0` and no monotonicity is bundled; this is
exactly the diminishing-returns inequality (1). -/
def IsSubmodular {α : Type*} [DecidableEq α] (f : Finset α → ℝ) : Prop :=
  ∀ A B : Finset α, ∀ e : α, A ⊆ B → e ∉ B →
    f (insert e B) - f B ≤ f (insert e A) - f A

end SubsamplingSM.Offline


