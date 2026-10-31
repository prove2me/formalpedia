-- Prove2me | Definitions.Def_PlatformCournot_potential
-- name    : PlatformCournot_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:25:00.29201+00:00
-- url     : https://prove2.me/theorems/b5d31aca-4d16-4514-86e1-cb11a2cebd53
-- title:
--   Objective of the convex program (9)
-- statement:
--   The objective of the convex program (9) of Lemma 1 is
--
--   $$\Phi(q)=\mathrm{SW}(q,C)-\sum_{i=1}^n\sum_{j=1}^m\frac{\beta_j q_{ij}^2}{2}.$$
--
--   Lemma 1 characterizes the Nash equilibrium of the game on $\mathcal E$ as the unique maximizer of $\Phi$ over $Q(\mathcal E)$.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Lemma 1, display (9), p.12

import Mathlib
import Definitions.Def_PlatformCournot_socialWelfare

namespace PlatformCournot

/-- **Objective of the convex program (9).**
Pang et al., arXiv:1903.04574v3, Lemma 1, display (9), p.12:
"maximize_{q∈Q(ℰ)} SW(q,C) − Σ_{i=1}^n Σ_{j=1}^m βj q²ij / 2."

**Formalization Note** Only the objective is defined here; the maximization over `Q(ℰ)` is stated
in Lemma 1. -/
noncomputable def potential {n m : ℕ} (D : AffineDemand m) (C : Fin n → ℝ → ℝ)
    (q : Fin n → Fin m → ℝ) : ℝ :=
  socialWelfare D C q - ∑ i, ∑ j, D.β j * q i j ^ 2 / 2

end PlatformCournot


