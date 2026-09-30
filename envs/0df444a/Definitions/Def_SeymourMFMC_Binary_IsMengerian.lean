-- Prove2me | Definitions.Def_SeymourMFMC_Binary_IsMengerian
-- name    : SeymourMFMC_Binary_IsMengerian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T01:13:33.662457+00:00
-- url     : https://prove2.me/theorems/5677102c-335f-4805-b08c-77e5a98fb073
-- title:
--   Mengerian clutter: integral max-packing = min-weight blocker member for all weights
-- statement:
--   A clutter $\mathbf L$ is **Mengerian** if either $\mathbf L = \{\emptyset\}$, or for every weight map $w : E(\mathbf L) \to \mathbb Z^+$ (the nonnegative integers) there is an integral packing $q : \mathbf L \to \mathbb Z^+$ such that
--
--   1. for each $x \in E(\mathbf L)$, $\displaystyle\sum_{A \in \mathbf L,\ A \ni x} q(A) \le w(x)$, and
--   2. the value of the packing equals the minimum weight of a member of the blocker:
--   $$
--   \sum_{A \in \mathbf L} q(A) = \min_{B \in b(\mathbf L)} \sum_{x \in B} w(x).
--   $$
--
--   Equivalently, every clutter obtained from $\mathbf L$ by deleting and replicating elements packs. This is the integral max-flow min-cut property; the paper characterizes it among binary clutters.
--
--   **Formalization Note** $w$ and $q$ are $\mathbb N$-valued functions on all of `α` and all of `Finset α`; their values off $E(\mathbf L)$ and off $\mathbf L$ are never read. The minimum in (2) is written as the existence of some $B \in b(\mathbf L)$ whose weight is at most that of every $B' \in b(\mathbf L)$ and equals the packing value; since $b(\mathbf L)$ is finite and nonempty whenever $\mathbf L \neq \{\emptyset\}$, this is the paper's minimum. The exception $\mathbf L = \{\emptyset\}$ (where $b(\mathbf L) = \emptyset$ and the minimum is undefined) is the paper's convention that $\{\emptyset\}$ packs.
-- source:
--   Seymour, The Matroids with the Max-Flow Min-Cut Property, J. Combin. Theory Ser. B 23 (1977), p. 192, Section 1 (the 'more explicitly' definition, (i)-(ii))

import Mathlib
import Definitions.Def_SeymourMFMC_Binary_ground
import Definitions.Def_SeymourMFMC_Binary_blocker

namespace SeymourMFMC.Binary

/-- `IsMengerian L` (Seymour 1977, p. 192, the "more explicit" form): either `L = {∅}`, or for
every weight map `w : E(L) → ℤ⁺` (nonnegative integers) there is an integer packing
`q : L → ℤ⁺` such that
(i) for each `x ∈ E(L)`, `∑ (q A : A ∈ L, x ∈ A) ≤ w x`, and
(ii) `∑_{A ∈ L} q A = min_{B ∈ b(L)} ∑_{x ∈ B} w x`.
The minimum in (ii) is written as: some `B ∈ b(L)` has minimum weight among all members of
`b(L)`, and the total packing value equals that weight. Weights and packings are `ℕ`-valued;
values of `w` off `E(L)` and of `q` off `L` are never read. -/
def IsMengerian {α : Type*} [DecidableEq α] (L : Finset (Finset α)) : Prop :=
  L = {∅} ∨
    ∀ w : α → ℕ, ∃ q : Finset α → ℕ,
      (∀ x ∈ ground L, ∑ A ∈ L.filter (fun A => x ∈ A), q A ≤ w x) ∧
        ∃ B ∈ blocker L, (∑ A ∈ L, q A = ∑ x ∈ B, w x) ∧
          ∀ B' ∈ blocker L, ∑ x ∈ B, w x ≤ ∑ x ∈ B', w x

end SeymourMFMC.Binary


