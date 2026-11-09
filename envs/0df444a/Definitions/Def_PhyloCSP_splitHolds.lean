-- Prove2me | Definitions.Def_PhyloCSP_splitHolds
-- name    : PhyloCSP_splitHolds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:23:53.279943+00:00
-- url     : https://prove2.me/theorems/a47ab5fa-d1f4-43fe-9854-9e687d3ab369
-- title:
--   Split predicates $\mathrm{split}_v(y_1,\dots,y_m)$
-- statement:
--   Let $T$ be a tree and $S=(y_1,\dots,y_m)$, $m\ge 2$, distinct variables with lowest common ancestor $z=y_1\vee\dots\vee y_m$. The variables in one child subtree of $z$ get label $0$ and the others label $1$; this is the **split vector** $s\in\mathbb F_2^m$, defined up to $s\leftrightarrow \mathbf 1-s$. For $v\in\mathbb F_2^m$ with $v\neq 0$ and an even number of ones, the **split predicate** $\mathrm{split}_v(y_1,\dots,y_m)$ requires
--   $$
--   \langle v,s\rangle=\sum_{i=1}^m v_is_i=0\quad\text{in }\mathbb F_2 .
--   $$
--
--   Here the predicate is indexed by subsets $V\subseteq S$ of the variables, $V=\{y_i : v_i=1\}$: two variables $y,z\in S$ lie on the same side of the top split of $S$ iff $y=z$ or some $w\in S$ satisfies $w\mid yz$, and the condition is that for every $y\in S$ the number of elements of $V$ on the side of $y$ is even. Since $|V|$ is even, this does not depend on which side is labeled $1$. The admissible indices are $|S|\ge 2$, $\emptyset\neq V\subseteq S$, $|V|$ even.
--
--   For example, with $|S|=3$ and $V=\{y_2,y_3\}$ this is the rooted triplet $y_1\mid y_2y_3$, and for $|S|=2$, $V=S$ it is always false.
--
--   **Formalization Note** Tuples and vectors are replaced by subsets; the paper notes (p.13) that rearranging arguments gives an equivalent predicate.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Section 5, pp.12–13 (PDF pp.14–15), split vectors and split predicates, Example 5.1

import Mathlib
import Definitions.Def_PhyloCSP_Pattern

set_option autoImplicit false

namespace PhyloCSP

/-- **Split predicates.**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Section 5, pp.12–13 (PDF pp.14–15): for distinct variables
`S = (y₁, …, y_m)`, `m ≥ 2`, with lowest common ancestor `z = y₁ ∨ ⋯ ∨ y_m`, "Some of the variables
lie in one child subtree of z, and the others lie in the other child subtree … These labels give
the split vector s ∈ F₂^m … For a vector v ∈ F₂^m with v ≠ 0, the split predicate split_v(y₁, …, y_m)
requires ⟨v, s⟩ = 0 in F₂ … we require that v have an even number of 1s".

`splitHolds P S V` is `split_v` on the variables of `S`, with `V = {yᵢ : vᵢ = 1}`: two variables
`y, z ∈ S` lie on the same side of the top split of `S` iff `y = z` or some `w ∈ S` is the outgroup
of `{w, y, z}`; the condition is that, for each `y ∈ S`, the number of elements of `V` on the side
of `y` is even. Because `|V|` is even, the parity on one side equals the parity on the other, so
this is `⟨v, s⟩ = 0` for either choice of `s` or `1 − s`.

**Formalization Note.** Tuples `(y₁, …, y_m)` and vectors `v` are replaced by subsets
`V ⊆ S ⊆ {x₁, …, x_k}`; the paper notes (p.13) that rearranging arguments gives an equivalent
predicate, so nothing is lost. The admissibility conditions `m ≥ 2`, `v ≠ 0`, `⟨1, v⟩ = 0` are
`IsSplitIndex`. -/
def splitHolds {k : ℕ} (P : Pattern (Fin k)) (S V : Finset (Fin k)) : Prop :=
  ∀ y ∈ S, Even (V.filter (fun z => z = y ∨ ∃ w ∈ S, P.1 w y z = true)).card

instance {k : ℕ} (P : Pattern (Fin k)) (S V : Finset (Fin k)) : Decidable (splitHolds P S V) := by
  unfold splitHolds; infer_instance

/-- The admissible indices of a split predicate: at least two variables (`m ≥ 2`), and a nonzero
vector `v` (`V ≠ ∅`, `V ⊆ S`) with an even number of ones. -/
def IsSplitIndex {k : ℕ} (S V : Finset (Fin k)) : Prop :=
  2 ≤ S.card ∧ V ⊆ S ∧ V.Nonempty ∧ Even V.card

instance {k : ℕ} (S V : Finset (Fin k)) : Decidable (IsSplitIndex S V) := by
  unfold IsSplitIndex; infer_instance

end PhyloCSP


