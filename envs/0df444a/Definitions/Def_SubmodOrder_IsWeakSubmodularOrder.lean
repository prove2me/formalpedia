-- Prove2me | Definitions.Def_SubmodOrder_IsWeakSubmodularOrder
-- name    : SubmodOrder_IsWeakSubmodularOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:36:49.630919+00:00
-- url     : https://prove2.me/theorems/656bc8f6-0285-423b-8146-f272b8630f1f
-- title:
--   Weak submodular order
-- statement:
--   An order $\pi$ of the ground set $N$ is a **weak submodular order** of a set function $f$ if
--
--   $$
--   f(C\mid A)\ \le\ f(C\mid B)
--   $$
--
--   for all $\pi$-nested sets $B\subseteq A$ and every set $C$ with $l_\pi(C)>r_\pi(A)$.
--
--   The weak order imposes nothing on pairs $B\subseteq A$ that are not $\pi$-nested, so it is a milder condition than a submodular order. All approximation results of the paper are proved under it.
--
--   **Formalization Note** $\pi$-nestedness and "to the right of" are the ∀-comparisons `IsPiNested` and `IsRightOf`, vacuous on empty sets, which is how the paper applies the definition (with $B=\emptyset$ in Lemma 1).
-- source:
--   Udwani, Submodular Order Functions and Assortment Optimization, arXiv:2107.02743v5, p.4, "Weak submodular order and π nested sets"

import Mathlib
import Definitions.Def_SubmodOrder_marginal
import Definitions.Def_SubmodOrder_IsRightOf
import Definitions.Def_SubmodOrder_IsPiNested

namespace SubmodOrder

/-- `π` is a weak submodular order of `f` (Udwani, arXiv:2107.02743v5, p.4: "An order π is a weak
submodular order if f(C | A) ≤ f(C | B) for all π-nested sets B ⊆ A and set C with
lπ(C) > rπ(A).").

**Formalization Note.** `π : α ≃ Fin n` is the order, `π e` the index of `e`. `π`-nestedness and
"`C` to the right of `A`" are the ∀-comparisons `IsPiNested` and `IsRightOf`, which are vacuous
on empty sets; this is the reading the paper uses (`B = E(0) = ∅` in the proof of Lemma 1). -/
def IsWeakSubmodularOrder {α : Type*} [DecidableEq α] {n : ℕ} (f : Finset α → ℝ)
    (π : α ≃ Fin n) : Prop :=
  ∀ A B C : Finset α, IsPiNested π B A → IsRightOf π A C → marginal f C A ≤ marginal f C B

end SubmodOrder


