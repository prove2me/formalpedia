-- Prove2me | Definitions.Def_NondualOpt_sfat
-- name    : NondualOpt_sfat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:32.230207+00:00
-- url     : https://prove2.me/theorems/21f75eb3-0583-4310-b81e-9e8682c9eeea
-- title:
--   The sequential fat-shattering dimension $\mathrm{sfat}_\alpha(G)$
-- statement:
--   Let $G\subseteq\mathbb R^Z$ and $\alpha>0$. A depth-$n$ predictable tree $z$ over $Z$ is **sequentially $\alpha$-shattered** by $G$ if there is a real-valued predictable tree $s$ such that for every sign path $\varepsilon\in\{\pm1\}^n$ some $h_\varepsilon\in G$ satisfies
--   $$
--   \varepsilon_t\big(h_\varepsilon(z_t(\varepsilon_{<t}))-s_t(\varepsilon_{<t})\big)\ge\frac\alpha2,\qquad t=1,\dots,n .
--   $$
--   The **sequential fat-shattering dimension** $\mathrm{sfat}_\alpha(G)$ is the largest such depth $n$.
--
--   It is the complexity measure through which Theorem 6 controls the max-regret value and Theorem 30 is stated.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$: $\infty$ if arbitrarily deep trees are shattered, and $0$ for an empty class. The margin is $\alpha/2$ as on the page.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Definition 1, p.8

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_histPrefix

namespace NondualOpt

/-- The sequential fat-shattering dimension `sfat_α(G)` of a class `G ⊆ ℝ^Z`: the largest depth `n`
of a predictable tree `z` over `Z` that is sequentially `α`-shattered by `G`, i.e. there is a real
predictable tree `s` such that for every sign path `ε ∈ {±1}^n` some `h_ε ∈ G` satisfies
`ε_t (h_ε(z_t(ε_{<t})) − s_t(ε_{<t})) ≥ α/2` for all `t`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Definition 1, p.8.

**Formalization Note.** Valued in `ℕ∞`: `⊤` when arbitrarily deep trees are shattered, `0` when
`G` is empty (no depth qualifies). Signs are `Bool` with `true ↦ +1`. The margin is `α/2`, as on
the page; the paper takes `α > 0`, and every statement using `sfat` assumes it. -/
noncomputable def sfat {Z : Type*} (G : Set (Z → ℝ)) (α : ℝ) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ z : Tree Z n, ∃ s : Tree ℝ n, ∀ ε : Fin n → Bool, ∃ h ∈ G, ∀ t : Fin n,
      α / 2 ≤ (if ε t then (1 : ℝ) else -1) *
        (h (z t (histPrefix ε t)) - s t (histPrefix ε t))), (n : ℕ∞)

end NondualOpt


