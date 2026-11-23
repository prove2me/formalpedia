-- Prove2me | Definitions.Def_ManipPotential_referenceCurve
-- name    : ManipPotential_referenceCurve
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T03:25:50.489469+00:00
-- url     : https://prove2.me/theorems/264dcb8d-d14e-4023-b9c8-3b94a2f0bf6d
-- title:
--   The reference curve $B_\rho(t)$ in Proposition 6.12
-- statement:
--   For a common-junction map $G$, a base point $z_0$, a direction $v$, distinct candidates $c_i,c_j$, and real parameters $\rho,t$, this defines the reference curve
--   $$
--   B_\rho(t)=G(z_0+t\rho v)-\varepsilon\mathbf 1+
--   \rho\big((1-t)\ell_i+t\ell_j\big),
--   \qquad \varepsilon=\frac{\rho}{4\kappa},
--   $$
--   where $\kappa=2m!(K+1)^m$ and $\mathbf 1$ is the all-ones profile.
--
--   This is the curve used in Step 1 of Proposition 6.12: its cyclic increment moves from $\rho\ell_i$ to $\rho\ell_j$, while its common-junction component follows the linearized direction $v$. Sharing this definition keeps the analytic error estimates and the support conclusion of Lemma 6.10 literally aligned.
--
--   **Formalization Note** Rankings are represented by their unit vectors, and $\rho,t$ are real parameters; the path construction later chooses $\rho$ rational.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Proposition 6.12, Step 1, definition of $B_\rho(t)$, p.36; $\kappa$ from Lemma 6.10, p.32.

import Mathlib
import Definitions.Def_ManipPotential_ExtRanking
import Definitions.Def_ManipPotential_ell
import Definitions.Def_ManipPotential_unitVec
import Definitions.Def_ManipPotential_kappa

namespace ManipPotential

/-- The reference curve `B_ρ(t)` in Proposition 6.12, Step 1, with
`ε = ρ / (4 κ)`. -/
noncomputable def referenceCurve {m : ℕ} [NeZero m] (K : ℕ)
    (G : ((ExtRanking m → ℝ) × ℝ) → (Ranking m → ℝ))
    (z₀ v : ((ExtRanking m → ℝ) × ℝ)) (i j : Fin m) (ρ t : ℝ) : Ranking m → ℝ :=
  G (z₀ + (t * ρ) • v) - (fun _ => ρ / (4 * kappa m K)) +
    ρ • ((1 - t) • unitVec (ell i) + t • unitVec (ell j))

end ManipPotential


