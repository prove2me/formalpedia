-- Prove2me | Definitions.Def_NondualOpt_IsSeqCover
-- name    : NondualOpt_IsSeqCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:36.619203+00:00
-- url     : https://prove2.me/theorems/f1a85d58-4aea-4b6c-bb02-dfab66bfbed2
-- title:
--   $\ell_\infty$ sequential $\alpha$-cover on a tree
-- statement:
--   For a depth-$n$ tree $z$ over $Z$, a set $V$ of real depth-$n$ trees is an **$\ell_\infty$ sequential $\alpha$-cover** of $G$ on $z$ if
--   $$
--   \forall h\in G,\ \forall\varepsilon\in\{\pm1\}^n,\ \exists v\in V:\quad\max_{1\le t\le n}\big|h(z_t(\varepsilon_{<t}))-v_t(\varepsilon_{<t})\big|\le\alpha .
--   $$
--   The tree $v$ may depend on both $h$ and $\varepsilon$ (a pathwise cover).
--
--   **Formalization Note** Covers are finite sets of trees; when only infinite covers exist the covering number is $\infty$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Definition 17, p.23

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_histPrefix

namespace NondualOpt

/-- `V` is an `ℓ∞` sequential `α`-cover of `G` on the depth-`n` tree `z`: for every `h ∈ G` and
every sign path `ε` some real tree `v ∈ V` satisfies `max_t |h(z_t(ε_{<t})) − v_t(ε_{<t})| ≤ α`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Definition 17, p.23.

**Formalization Note.** `v` may depend on both `h` and `ε` (a pathwise cover), as on the page.
Covers are finite sets of real trees; an instance with no finite cover has covering number `⊤`
(`seqCoverNum`). -/
def IsSeqCover {Z : Type*} {n : ℕ} (G : Set (Z → ℝ)) (z : Tree Z n) (α : ℝ)
    (V : Finset (Tree ℝ n)) : Prop :=
  ∀ h ∈ G, ∀ ε : Fin n → Bool, ∃ v ∈ V, ∀ t : Fin n,
    |h (z t (histPrefix ε t)) - v t (histPrefix ε t)| ≤ α

end NondualOpt


