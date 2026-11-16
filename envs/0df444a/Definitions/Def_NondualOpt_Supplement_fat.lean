-- Prove2me | Definitions.Def_NondualOpt_Supplement_fat
-- name    : NondualOpt_Supplement_fat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:11:56.967755+00:00
-- url     : https://prove2.me/theorems/e634a167-9201-47cb-8947-b382c1a239ff
-- title:
--   The fat-shattering dimension $\mathrm{fat}_\alpha(G)$
-- statement:
--   Let $Z$ be a set, $G\subseteq\mathbb R^Z$ a class of real functions on $Z$, and $\alpha>0$. Points $z_1,\dots,z_m\in Z$ are **$\alpha$-shattered** by $G$ if there are thresholds $s_1,\dots,s_m\in\mathbb R$ such that for every sign vector $\varepsilon\in\{\pm1\}^m$ some $h_\varepsilon\in G$ satisfies
--   $$
--   \varepsilon_i\big(h_\varepsilon(z_i)-s_i\big)\ge\frac{\alpha}{2}\qquad\text{for all }i=1,\dots,m.
--   $$
--   The **fat-shattering dimension** $\mathrm{fat}_\alpha(G)\in\mathbb N\cup\{\infty\}$ is the largest such $m$ (and $\infty$ if arbitrarily large sets are shattered).
--
--   This is the non-sequential counterpart of the sequential fat-shattering dimension $\mathrm{sfat}_\alpha$; Theorem 10 bounds the iid convex-hull approximation error through $\mathrm{fat}_\alpha(L_{X,H})$.
--
--   **Formalization Note** The value is an extended natural number; signs are booleans (`true` is $+1$); the margin is $\alpha/2$ as in the paper. The points form a family indexed by $\{1,\dots,m\}$; for $\alpha>0$ a shattered family cannot repeat a point, so this is the paper's "set". The conventions are those of the published `NondualOpt.sfat`.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Definition 1, p.8

import Mathlib

namespace NondualOpt.Supplement

/-- The (non-sequential) fat-shattering dimension `fat_α(G)` of a class `G ⊆ ℝ^Z`: the largest `m`
such that some points `z_1, …, z_m ∈ Z` are `α`-shattered by `G`, i.e. there are thresholds
`s_1, …, s_m ∈ ℝ` such that for every sign vector `ε ∈ {±1}^m` some `h_ε ∈ G` satisfies
`ε_i (h_ε(z_i) − s_i) ≥ α/2` for all `i = 1, …, m`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Definition 1, p.8.

**Formalization Note.** Same conventions as the published sequential version `NondualOpt.sfat`:
valued in `ℕ∞` (`⊤` when arbitrarily large sets are shattered, `0` when `G` is empty); signs are
`Bool` with `true ↦ +1`; the margin is `α/2`, as on the page. The points are a family
`z : Fin m → Z`; for `α > 0` (every use) a shattered family has no repeated points, so this is the
paper's "set". -/
noncomputable def fat {Z : Type*} (G : Set (Z → ℝ)) (α : ℝ) : ℕ∞ :=
  ⨆ (m : ℕ) (_ : ∃ z : Fin m → Z, ∃ s : Fin m → ℝ, ∀ ε : Fin m → Bool, ∃ h ∈ G, ∀ i : Fin m,
      α / 2 ≤ (if ε i then (1 : ℝ) else -1) * (h (z i) - s i)), (m : ℕ∞)

end NondualOpt.Supplement


