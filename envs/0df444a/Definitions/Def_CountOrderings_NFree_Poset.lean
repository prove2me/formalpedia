-- Prove2me | Definitions.Def_CountOrderings_NFree_Poset
-- name    : CountOrderings_NFree_Poset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:56:35.99022+00:00
-- url     : https://prove2.me/theorems/3d3bb35f-9cdb-4d52-902c-a4af4e2dc216
-- title:
--   N-freeness, height, number of linear extensions, and rooted tree posets
-- statement:
--   Let $P$ be a finite poset with order $\preceq$. An element $y$ **covers** $x$, written $x \lessdot y$, if $x \prec y$ and no element $z$ satisfies $x \prec z \prec y$; the covers are the edges of the **Hasse diagram** of $P$.
--
--   - $P$ is **N-free** if its Hasse diagram contains no induced copy of the four-element pattern $N$: there are no pairwise distinct $a, b, c, d \in P$ with
--   $$a \lessdot c,\qquad b \lessdot c,\qquad b \lessdot d,\qquad a \not\lessdot d .$$
--   (The other covers among four such elements are impossible, so "induced" only excludes $a \lessdot d$.)
--   - The **height** of $P$ is the maximum number of elements in a chain of $P$ (a set of pairwise comparable elements); the empty poset has height $0$.
--   - $\#\mathrm{LE}(P)$ is the number of **linear extensions** of $P$: orderings of $P$ in which every element follows all its predecessors, i.e. bijections $L : P \to \{0, \dots, |P|-1\}$ with $x \preceq y \Rightarrow L(x) \le L(y)$ (the published definition `FCP.Order.LinearExtensions`).
--   - $P$ is a **rooted tree poset** (its Hasse diagram is a rooted tree, the root is the minimum element and the order increases along paths away from it) if it has a least element $r$ and every element other than $r$ covers exactly one element.
--   - For $v \in P$, $T_v = \{u \in P \mid v \preceq u\}$, and $|T_v|$ is its number of elements; in a rooted tree poset $T_v$ is the subtree rooted at $v$.
--
--   **Formalization Note.** Covers are Mathlib's `CovBy` (`a ⋖ c`). The poset is any finite type (`Fintype`) with a `PartialOrder`, in `Type`.
-- source:
--   Arenas, Schild and Subercaseaux, Hardness of Counting Orderings: Taking Gadget Amplification to the Limit, STOC 2027 submission, p. 6 (PDF p. 7), §1.2 (N-free); p. 5 (PDF p. 6), §1.2 (height); p. 2 (PDF p. 3) and p. 7 (PDF p. 8), §2 (linear extensions); p. 8 (PDF p. 9), Lemma 2.2 and footnote 2 (rooted tree posets, T_v)

import Mathlib
import Definitions.Def_FCP_LinearExtensions

namespace CountOrderings.NFree

/-- A finite poset `P` is **N-free** if its Hasse diagram contains no induced copy of the
four-element pattern `N`: there are no pairwise distinct `a, b, c, d` with the cover relations
`a ⋖ c`, `b ⋖ c`, `b ⋖ d` and without the cover `a ⋖ d`. (`x ⋖ y` is Mathlib's `CovBy`: `x < y`
and nothing lies strictly between them, i.e. an edge of the Hasse diagram.) -/
def IsNFree (P : Type) [PartialOrder P] : Prop :=
  ¬ ∃ a b c d : P, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    a ⋖ c ∧ b ⋖ c ∧ b ⋖ d ∧ ¬ a ⋖ d

open Classical in
/-- The **height** of a finite poset: the maximum number of elements in a chain (a set of
pairwise comparable elements). The empty poset has height `0`. -/
noncomputable def height (P : Type) [PartialOrder P] [Fintype P] : ℕ :=
  ((Finset.univ : Finset (Finset P)).filter
    (fun s : Finset P => IsChain (· ≤ ·) (↑s : Set P))).sup Finset.card

/-- `#LE(P)`: the number of linear extensions of a finite poset `P`, i.e. of the
order-preserving bijections `P ≃ Fin |P|` (the published `FCP.Order.LinearExtensions`). -/
noncomputable def numLinExt (P : Type) [Fintype P] [PartialOrder P] : ℕ :=
  (FCP.Order.LinearExtensions P).ncard

/-- A finite poset **whose Hasse diagram is a rooted tree**, the root being the minimum element
and the order increasing along paths away from it: there is a least element `r`, and every other
element covers exactly one element (has exactly one parent in the Hasse diagram). -/
def IsRootedTreePoset (T : Type) [PartialOrder T] : Prop :=
  ∃ r : T, (∀ x : T, r ≤ x) ∧ ∀ x : T, x ≠ r → ∃! y : T, y ⋖ x

open Classical in
/-- `|T_v|`: the number of elements of the principal up-set `T_v = {u ∈ T | v ⪯ u}`, the
subtree rooted at `v` when `T` is a rooted tree poset. -/
noncomputable def upSetCard {T : Type} [PartialOrder T] [Fintype T] (v : T) : ℕ :=
  ((Finset.univ : Finset T).filter (fun u => v ≤ u)).card

end CountOrderings.NFree


