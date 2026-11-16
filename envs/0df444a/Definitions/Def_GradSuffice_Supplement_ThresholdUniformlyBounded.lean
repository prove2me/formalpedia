-- Prove2me | Definitions.Def_GradSuffice_Supplement_ThresholdUniformlyBounded
-- name    : GradSuffice_Supplement_ThresholdUniformlyBounded
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:26:38.490832+00:00
-- url     : https://prove2.me/theorems/f2e3b75e-d2ab-4c85-9196-dc6ee9045745
-- title:
--   Uniformly bounded threshold structures
-- statement:
--   Let $V$ be a real normed space with unit ball $B_V$ and dual unit ball $B_V^\star$. The $(B_V,B_V^\star)$-**threshold structures are uniformly bounded** if for every margin $\theta>0$ there is an $N(\theta)$ such that every threshold structure of margin $\theta$ has size at most $N(\theta)$.
--
--   Items 2 and 3 of Theorem 7 are this property for $V=X$ and for $V=X^\star$.
--
--   **Formalization Note** "Size at most $N(\theta)$" quantifies every family $(w_i,\xi_i)_{i<N}$ satisfying the threshold condition.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §6.2, p.17

import Mathlib
import Definitions.Def_GradSuffice_Supplement_IsThresholdStructure

namespace GradSuffice.Supplement

/-- **Uniformly bounded threshold structures.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §6.2, p.17: "Say that `(B, B⋆)`-threshold
structures are uniformly bounded if for every `θ > 0` there exists an `N(θ)` so that every threshold
structure of margin `θ > 0` is at most of size `N(θ)`."

**Formalization Note.** For a real normed space `V` with unit ball `B_V` and dual unit ball `B_V⋆`:
the `(B_V, B_V⋆)`-threshold structures (`IsThresholdStructure`) are uniformly bounded.
`V = StrongDual ℝ X` gives the `(B⋆, (B⋆)⋆)`-structures of Theorem 7, item 3. -/
def ThresholdUniformlyBounded (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : Prop :=
  ∀ θ : ℝ, 0 < θ → ∃ Nθ : ℕ, ∀ (N : ℕ) (w : Fin N → V) (ξ : Fin N → StrongDual ℝ V),
    IsThresholdStructure θ w ξ → N ≤ Nθ

end GradSuffice.Supplement


