-- Prove2me | Definitions.Def_NondualOpt_seqCoverNum
-- name    : NondualOpt_seqCoverNum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:59:43.561125+00:00
-- url     : https://prove2.me/theorems/4dfd9e5a-bfe6-4ade-84c4-8556e5b9b2ce
-- title:
--   The sequential covering number $N^{\mathrm{seq}}_\infty(\alpha,G,n)$
-- statement:
--   The **sequential covering number** is the worst-case size of an optimal cover,
--   $$
--   N^{\mathrm{seq}}_\infty(\alpha,G,n)=\sup_{z}\ \min_{V_z}|V_z|,
--   $$
--   the supremum over depth-$n$ trees $z$ over $Z$ and the minimum over $\ell_\infty$ sequential $\alpha$-covers $V_z$ of $G$ on $z$. Its logarithm is the entropy in the chaining bound of Proposition 20.
--
--   **Formalization Note** Valued in $\mathbb N\cup\{\infty\}$.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Definition 17, p.23

import Mathlib
import Definitions.Def_NondualOpt_IsSeqCover

namespace NondualOpt

/-- The sequential covering number `N^seq_∞(α, G, n) = sup_z min_{V_z} |V_z|`, the size of a
worst-case optimal `ℓ∞` sequential `α`-cover over depth-`n` trees.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Definition 17, p.23.

**Formalization Note.** Valued in `ℕ∞`; the minimum over an empty family of finite covers is `⊤`
(only infinite covers exist). -/
noncomputable def seqCoverNum {Z : Type*} (G : Set (Z → ℝ)) (α : ℝ) (n : ℕ) : ℕ∞ :=
  ⨆ z : Tree Z n, ⨅ (V : Finset (Tree ℝ n)) (_ : IsSeqCover G z α V), (V.card : ℕ∞)

end NondualOpt


