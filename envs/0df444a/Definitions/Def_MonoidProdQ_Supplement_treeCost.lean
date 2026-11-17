-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_treeCost
-- name    : MonoidProdQ_Supplement_treeCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:12:21.975413+00:00
-- url     : https://prove2.me/theorems/e4cd61c2-99ee-4264-8863-ff1b64d24a8e
-- title:
--   Recursive tree cost $C_v$
-- statement:
--   For a finite rooted tree with positive vertex costs $t_v$, define recursively
--
--   $$C_v=t_v+\sqrt{\sum_{u\text{ child of }v}C_u^2},$$
--
--   with the empty sum equal to zero, so $C_v=t_v$ at a leaf. Theorem 42 shows that searching the tree for a marked vertex costs $O(C_\rho)$ queries.
--
--   **Formalization Note** On the published rooted-tree model the children of $v$ are the non-root vertices whose parent is $v$. The recursion is unfolded $|V|$ times starting from $t$; after $k$ unfoldings the value at $v$ equals $C_v$ as soon as $k$ is at least the height of the subtree of $v$, and every height is below $|V|$, so the result is $C_v$ at every vertex.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 42, Eq. (48), p.59

import Definitions.Def_HarelTarjan_Compressed_RootedTree

namespace MonoidProdQ.Supplement

open HarelTarjan.Compressed

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 42, Eq. (48), p.59: for a finite
rooted tree with vertex costs `t_v`,
`C_v = t_v + √(Σ_{u child of v} C_u²)`, "with the empty sum equal to zero, so C_v = t_v at a
leaf".

**Formalization Note.** The tree is the published `HarelTarjan.Compressed.RootedTree`; the
children of `v` are the `u ≠ root` with `parent u = v`. The recursion is unfolded `|V|` times
starting from `t`: after `k` unfoldings the value at `v` is `C_v` as soon as `k` is at least the
height of the subtree of `v` (a leaf has height `0`), and every height is at most `|V| − 1`, so
the result is `C_v` at every vertex. -/
noncomputable def treeCost {V : Type*} [Fintype V] [DecidableEq V] (T : RootedTree V)
    (t : V → ℝ) : V → ℝ :=
  Nat.rec (motive := fun _ => V → ℝ) t
    (fun _ c v => t v + Real.sqrt (∑ u ∈ Finset.univ.filter (fun u => u ≠ T.root ∧ T.parent u = v),
      c u ^ 2))
    (Fintype.card V)

end MonoidProdQ.Supplement


