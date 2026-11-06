-- Prove2me | Definitions.Def_NondualOpt_offsetClass
-- name    : NondualOpt_offsetClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:56.363449+00:00
-- url     : https://prove2.me/theorems/daf4e7de-2249-421a-9d49-1cab7b954720
-- title:
--   The offset envelope class $\Phi\circ(\tfrac12A_{X,H})$
-- statement:
--   The **offset envelope class** is
--   $$
--   \Phi\circ\big(\tfrac12A_{X,H}\big)=\Big\{(g,b)\mapsto\phi\Big(\frac{\langle g,u\rangle+b}2\Big):\ u\in X,\ \phi\in\Phi\Big\},
--   $$
--   as functions on $H\times[-1,1]$. Lemma 5 bounds the convex-hull distance by an offset process indexed by this class, and Lemma 22 compares its sequential entropy with that of $L_{X,H}$.
--
--   **Formalization Note** Since $\phi$ is defined on $[-1,1]$, its argument is clamped to $[-1,1]$. When $|\langle g,u\rangle|\le1$ on $H\times X$ (the paper's $\Lambda_{X,H}=1$) the argument already lies in $[-1,1]$, and the clamp changes no value.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Definition 21, p.30

import Mathlib
import Definitions.Def_NondualOpt_PhiClass
import Definitions.Def_NondualOpt_unitZ

namespace NondualOpt

/-- The offset envelope class `Φ ∘ (½ A_{X,H}) = {(g, b) ↦ ϕ((⟨g, u⟩ + b)/2) : u ∈ X, ϕ ∈ Φ}`, as
functions on `H × [−1, 1]`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Definition 21, p.30.

**Formalization Note.** `ϕ` is defined on `[−1, 1]`, so its argument is clamped to `[−1, 1]`
(`Set.projIcc`). Whenever `|⟨g, u⟩| ≤ 1` on `H × X` (the paper's `Λ_{X,H} = 1`) the argument already
lies in `[−1, 1]` ("every argument of `ϕ` belongs to `[−1, 1]`", p.30), and the clamp changes no
value. -/
def offsetClass {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (pair : F →ₗ[ℝ] E →ₗ[ℝ] ℝ) (X : Set E) (H : Set F) : Set (unitZ H → ℝ) :=
  {h | ∃ u ∈ X, ∃ ϕ ∈ PhiClass, h = fun z : unitZ H =>
    ϕ (Set.projIcc (-1) 1 (by norm_num) ((pair (z : F × ℝ).1 u + (z : F × ℝ).2) / 2))}

end NondualOpt


