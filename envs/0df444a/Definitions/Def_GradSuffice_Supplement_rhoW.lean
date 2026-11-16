-- Prove2me | Definitions.Def_GradSuffice_Supplement_rhoW
-- name    : GradSuffice_Supplement_rhoW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:25:20.920697+00:00
-- url     : https://prove2.me/theorems/5a441f5a-c2ea-4678-9447-71ae83b1dc1c
-- title:
--   Non-dual gauge $\rho_W(\xi)=\sup_{w\in W}|w\cdot\xi|$
-- statement:
--   Let $X$ be a real normed space, $W\subseteq X$ a parameter set and $\xi\in X^\star$ a continuous linear functional. The **non-dual gauge** of $\xi$ with respect to $W$ is
--   $$\rho_W(\xi)=\sup_{w\in W}|w\cdot\xi| .$$
--   For $W=B$, the closed unit ball, this is the dual norm $\|\xi\|_\star$; for a smaller set $W\subseteq B$ it is at most $\|\xi\|_\star$.
--
--   It replaces the dual norm in the sequential Rademacher complexity when the optimization domain $W$ is not the unit ball (§6.1).
--
--   **Formalization Note** The supremum is the real `sSup` of $\{|\xi(w)|: w\in W\}$. For nonempty $W\subseteq B$ this set is nonempty and bounded by $\|\xi\|_\star$, so the value is the true supremum; every statement using $\rho_W$ assumes these conditions (the empty set would give the value $0$).
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §6.1, p.14

import Mathlib

namespace GradSuffice.Supplement

/-- **The non-dual gauge `ρ_W`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §6.1, p.14: for a parameter set `W ⊆ B` and a dual vector
`ξ ∈ X⋆`, "`ρ_W(ξ) = sup_{w∈W} |w · ξ|`".

**Formalization Note.** The supremum is the real `sSup` of the image `{|ξ w| : w ∈ W}`. For
`W ⊆ B` this set is bounded by `‖ξ‖`, so for nonempty `W` the value is the true supremum; every
statement using `ρ_W` assumes `W` nonempty and `W ⊆ B` (the value `0` at `W = ∅` is never used). -/
noncomputable def rhoW {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (W : Set X)
    (ξ : StrongDual ℝ X) : ℝ :=
  sSup ((fun w => |ξ w|) '' W)

end GradSuffice.Supplement


