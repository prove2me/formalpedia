-- Prove2me | Definitions.Def_SubmodOrder_IsSubmodularOrder
-- name    : SubmodOrder_IsSubmodularOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:48.448993+00:00
-- url     : https://prove2.me/theorems/b21c7e4b-004f-4cd9-981c-ed27501ae54e
-- title:
--   Submodular order
-- statement:
--   A permutation $\pi$ of the ground set $N$ is a **submodular order** of a set function $f$ if
--
--   $$
--   f(C\mid A)\ \le\ f(C\mid B)
--   $$
--
--   for all sets $B\subseteq A$ and every set $C$ to the right of $A$, i.e. $l_\pi(C)>r_\pi(A)$ (inequality (1) of the paper).
--
--   A function is submodular exactly when every permutation is a submodular order. Functions with a known submodular order include the revenue functions of several assortment optimization problems, and they allow constant-factor approximation where general monotone subadditive maximization does not.
--
--   **Formalization Note** $\pi$ is a bijection $\alpha\simeq\{0,\dots,n-1\}$, and "to the right of" is the ∀-comparison of `IsRightOf`, vacuous on empty sets. Every submodular order is a weak submodular order.
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, p.3, "Submodular order", inequality (1)

import Mathlib
import Definitions.Def_SubmodOrder_marginal
import Definitions.Def_SubmodOrder_IsRightOf

namespace SubmodOrder

/-- `π` is a (strong) submodular order of `f` (Udwani, arXiv:2107.02743v5, p.3, (1):
"A permutation π of elements in N is a submodular order if for all sets B ⊆ A and C to the
right of A i.e., lπ(C) > rπ(A), we have f(C | A) ≤ f(C | B).").

**Formalization Note.** `π : α ≃ Fin n` is the permutation, `π e` the index of `e`. "C to the
right of A" is `IsRightOf π A C` (vacuous when `A` or `C` is empty). -/
def IsSubmodularOrder {α : Type*} [DecidableEq α] {n : ℕ} (f : Finset α → ℝ) (π : α ≃ Fin n) :
    Prop :=
  ∀ A B C : Finset α, B ⊆ A → IsRightOf π A C → marginal f C A ≤ marginal f C B

end SubmodOrder


