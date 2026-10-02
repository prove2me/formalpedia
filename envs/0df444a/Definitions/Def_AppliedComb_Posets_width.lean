-- Prove2me | Definitions.Def_AppliedComb_Posets_width
-- name    : AppliedComb_Posets_width
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:04:44.82499+00:00
-- url     : https://prove2.me/theorems/9ad46aad-fb83-4e88-97ae-bb0040b48223
-- title:
--   Width and height of a finite poset (Section 6.1)
-- statement:
--   Let $\mathbf P = (X, P)$ be a finite partially ordered set, represented by a finite type $\alpha$ with a partial order $\le$. A subset $C \subseteq X$ is a **chain** if every two distinct points of $C$ are comparable, and a subset $A \subseteq X$ is an **antichain** if every two distinct points of $A$ are incomparable; the empty set and every one-point set are both.
--
--   The **width** and **height** of $\mathbf P$ are
--   $$\operatorname{width}(\mathbf P) = \max\{|A| : A \subseteq X \text{ an antichain}\}, \qquad \operatorname{height}(\mathbf P) = \max\{|C| : C \subseteq X \text{ a chain}\}.$$
--   Both maxima are over a nonempty finite family (the empty set is always both a chain and an antichain), so they are attained; for the empty poset both are $0$.
--
--   These are the two parameters of Dilworth's theorem and its dual: the width is compared with the least number of chains, the height with the least number of antichains, needed to partition $X$.
--
--   **Formalization Note.** Chains and antichains are Mathlib's `IsChain (· ≤ ·)` and `IsAntichain (· ≤ ·)` on the coerced `Finset`; the maximum is `Finset.sup Finset.card` over all subsets of `α` that are antichains (resp. chains). Width is defined from antichains, not as a least number of chains in a partition.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), pp. 118–119, Section 6.1 (chains, antichains, height, width)

import Mathlib

namespace AppliedComb.Posets

open Classical in
/-- Width of a finite poset (Keller & Trotter, *Applied Combinatorics*, 2017 Edition, p. 119):
the largest `w` for which there exists an antichain of `w` points. An antichain is a subset
in which every distinct pair of points is incomparable (Mathlib's `IsAntichain (· ≤ ·)`);
the empty set is an antichain, so the maximum is taken over a nonempty finite family. -/
noncomputable def width (α : Type*) [PartialOrder α] [Fintype α] : ℕ :=
  ((Finset.univ : Finset (Finset α)).filter
    (fun A : Finset α => IsAntichain (· ≤ ·) (A : Set α))).sup Finset.card

open Classical in
/-- Height of a finite poset (Keller & Trotter, p. 119): the largest `h` for which there exists
a chain of `h` points. A chain is a subset in which every distinct pair of points is comparable
(Mathlib's `IsChain (· ≤ ·)`); the empty set is a chain. -/
noncomputable def height (α : Type*) [PartialOrder α] [Fintype α] : ℕ :=
  ((Finset.univ : Finset (Finset α)).filter
    (fun C : Finset α => IsChain (· ≤ ·) (C : Set α))).sup Finset.card

end AppliedComb.Posets


