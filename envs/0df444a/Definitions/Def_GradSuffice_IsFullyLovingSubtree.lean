-- Prove2me | Definitions.Def_GradSuffice_IsFullyLovingSubtree
-- name    : GradSuffice_IsFullyLovingSubtree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:43.863931+00:00
-- url     : https://prove2.me/theorems/d03366a3-a75e-48c1-b5c9-a2e24bbb6e0d
-- title:
--   Fully loving complete binary subtree of depth $d$
-- statement:
--   Let $T$ be the complete binary tree of depth $n$, in which each branch $\beta$ **loves** some of the $n$ internal vertices it visits. A **subtree** $F$ of $T$ is a nonempty set of vertices closed under least common ancestors; its edges join each retained vertex to its nearest retained strict ancestor, and its depth is measured with these edges. $F$ is **fully loving** if every branch of $F$ extends to a branch of $T$ that loves every internal vertex of $F$ along that branch.
--
--   A fully loving complete binary subtree of depth $d$ is described by
--   1. for each internal vertex of the complete binary tree of depth $d$, reached by a sign prefix $\tau_{<j}$, the level $\mathrm{lev}_j(\tau_{<j})$ of the vertex of $T$ it is mapped to, with levels strictly increasing along every branch;
--   2. for each branch $\tau\in\{0,1\}^d$, a branch $\beta_\tau$ of $T$ through these vertices: branches $\tau,\tau'$ with the same first $j$ turns pass through the same vertex at depth $j$;
--   3. at its depth-$j$ vertex, $\beta_\tau$ turns in the direction $\tau_j$ and loves that vertex.
--
--   **Formalization Note** As the paper allows (App. B), terminal vertices of the subtree are original leaves, reached by the witnessing branches.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §4.1, p.11; App. B, p.37

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_histPrefix

namespace GradSuffice

/-- **Fully loving complete binary subtree of depth `d`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §4.1, p.11: "A subtree `F` of `T`
is a nonempty set of vertices closed under least common ancestors. Its edges join each retained
vertex to its nearest retained strict ancestor. […] Its depth is measured using these new edges. We
call `F` fully loving if every branch of `F` extends to a branch of `T` that loves every internal
vertex of `F` along that branch." App. B, p.37: "We may require the terminal vertices of a fully
loving subtree to be original leaves".

**Formalization Note.** `T` is the complete binary tree of depth `n`; a branch of `T` is
`β : Fin n → Bool`, its internal vertex at level `l` is the prefix `β<l`, and `love β l` says that `β`
loves that vertex. A complete binary subtree of depth `d` is given by the levels
`lev j (τ<j)` of its internal vertices (`τ : Fin d → Bool` a branch of the subtree, `j` its depth in
the subtree) and, for each `τ`, a branch `br τ` of `T` through them:
1. levels strictly increase along each branch of the subtree;
2. two branches of the subtree with the same first `j` turns pass through the same vertex at depth
   `j` (their `T`-branches agree before that level);
3. at its depth-`j` vertex, `br τ` turns in direction `τ j` and loves the vertex.
Then the retained vertices form a set closed under least common ancestors whose induced tree is
the complete binary tree of depth `d`, and `br τ` is the extension of the subtree branch `τ` that
loves all its internal vertices; conversely every fully loving complete binary subtree of depth
`d` (with leaves extended to original leaves, App. B) arises this way. -/
def IsFullyLovingSubtree {n : ℕ} (love : (Fin n → Bool) → Fin n → Prop) {d : ℕ}
    (lev : NondualOpt.Tree (Fin n) d) (br : (Fin d → Bool) → Fin n → Bool) : Prop :=
  (∀ (τ : Fin d → Bool) (j k : Fin d), j < k →
      lev j (NondualOpt.histPrefix τ j) < lev k (NondualOpt.histPrefix τ k)) ∧
  (∀ (τ τ' : Fin d → Bool) (j : Fin d),
      NondualOpt.histPrefix τ j = NondualOpt.histPrefix τ' j →
      ∀ l : Fin n, l < lev j (NondualOpt.histPrefix τ j) → br τ l = br τ' l) ∧
  (∀ (τ : Fin d → Bool) (j : Fin d),
      br τ (lev j (NondualOpt.histPrefix τ j)) = τ j ∧
        love (br τ) (lev j (NondualOpt.histPrefix τ j)))

end GradSuffice


