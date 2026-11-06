-- Prove2me | Definitions.Def_NondualOpt_crossDuality
-- name    : NondualOpt_crossDuality
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:42.189203+00:00
-- url     : https://prove2.me/theorems/b73a00d7-f1c5-425d-b695-8a551bf2c288
-- title:
--   The cross-duality constant $\Lambda_{X,H}$
-- statement:
--   For a bilinear pairing $\langle\cdot,\cdot\rangle$ between a space $F$ (in the paper $E^*$) and $E$, and sets $X\subseteq E$, $H\subseteq F$, the **cross-duality constant** is
--   $$
--   \Lambda_{X,H}=\sup_{g\in H,\,u\in X}|\langle g,u\rangle| .
--   $$
--   Every function of the linear class $L_{X,H}$ takes values in $[-\Lambda_{X,H},\Lambda_{X,H}]$. For $p\le q$, $\Lambda_{B_p^d,B_{q^*}^d}=1$.
--
--   **Formalization Note** The value is a real supremum; every statement using it assumes $X,H$ nonempty and $\Lambda_{X,H}<\infty$ (Assumption 3), where it is the true supremum. The pairing is abstract: the paper uses functionals only through pairings (footnote 7).
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, (5), p.7

import Mathlib

namespace NondualOpt

/-- The cross-duality constant `Λ_{X,H} = sup_{g ∈ H, u ∈ X} |⟨g, u⟩|`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, (5), p.7.

**Formalization Note.** The pairing is an abstract bilinear map `pair : F → E → ℝ` (the duality
pairing between `E∗` and `E` is the instance `F = E∗`; the paper uses `µ_t` only through such
pairings, footnote 7, p.11). The value is the real `sSup`; every statement using it assumes
`X, H` nonempty and the set bounded above (Assumption 3), where it is the true supremum. -/
noncomputable def crossDuality {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F) : ℝ :=
  sSup {r : ℝ | ∃ g ∈ H, ∃ u ∈ X, r = |pair g u|}

end NondualOpt


