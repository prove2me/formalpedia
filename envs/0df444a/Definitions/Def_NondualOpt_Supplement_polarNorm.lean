-- Prove2me | Definitions.Def_NondualOpt_Supplement_polarNorm
-- name    : NondualOpt_Supplement_polarNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:12:36.57449+00:00
-- url     : https://prove2.me/theorems/cf8bdf29-84cc-411f-807e-8cb69dc0df3b
-- title:
--   The polar norm $\|z\|_{X^\circ}$
-- statement:
--   For a set $X\subseteq\mathbb R^d$ and $z\in\mathbb R^d$, the **polar norm** of $z$ with respect to $X$ is
--   $$
--   \|z\|_{X^\circ}=\sup_{u\in X}|\langle u,z\rangle|,
--   $$
--   the gauge of the polar body $X^\circ=\{z:\sup_{u\in X}|\langle u,z\rangle|\le1\}$. For an origin-symmetric convex body $X$ it is a norm on $\mathbb R^d$; for $X=B_p^d$ it is the dual norm $\|\cdot\|_{p^*}$.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ` and $\langle u,z\rangle$ is the published dot product. The supremum is a real supremum; it is the true supremum whenever $X$ is nonempty and bounded, as for the convex bodies of Theorem 10.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, §5.1, p.13

import Mathlib
import Definitions.Def_NondualOpt_dotPair

namespace NondualOpt.Supplement

/-- The polar norm `‖z‖_{X°} = sup_{u ∈ X} |⟨u, z⟩|` of `z ∈ ℝ^d` with respect to `X ⊆ ℝ^d`
(the gauge of the polar body `X° = {z : sup_{u ∈ X} |⟨u, z⟩| ≤ 1}`).
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, §5.1, p.13.

**Formalization Note.** `ℝ^d` is `Fin d → ℝ` and `⟨u, z⟩` is the published dot product
`NondualOpt.dotPair d z u`. The value is the real `sSup`; every use takes `X` a convex body
(compact, nonempty), where the set is nonempty and bounded and this is the true supremum. -/
noncomputable def polarNorm {d : ℕ} (X : Set (Fin d → ℝ)) (z : Fin d → ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u ∈ X, r = |NondualOpt.dotPair d z u|}

end NondualOpt.Supplement


