-- Prove2me | Definitions.Def_GibbsCongestion_gibbs
-- name    : GibbsCongestion_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:02:10.646515+00:00
-- url     : https://prove2.me/theorems/b4b7f022-8243-4544-b7b2-efffe694b8e8
-- title:
--   Gibbs distribution $\pi(s)\propto e^{-T\Phi(s)}$
-- statement:
--   At temperature $T\ge0$, the **Gibbs distribution** over the strategy profiles of a congestion game is
--   $$\pi(s)=\frac{e^{-T\Phi(s)}}{Z},\qquad Z=\sum_{t\in\mathcal P^n}e^{-T\Phi(t)},$$
--   where $\Phi$ is Rosenthal's potential. It is the stationary distribution of the logit dynamics and of the relaxed logit dynamics; $T=0$ gives the uniform distribution and large $T$ concentrates on potential minimizers.
--
--   **Formalization Note** The game is uncapacitated ($u_e=n$ for every resource), so every profile is feasible and $Z$ sums over all of $\mathcal P^n$.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.1, p.8

import Mathlib
import Definitions.Def_GibbsCongestion_potential

namespace GibbsCongestion

/-- The **Gibbs distribution** at temperature `T`: `π(s) = e^{-TΦ(s)}/Z` with
`Z = ∑_t e^{-TΦ(t)}` (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.1, p.8).

**Formalization Note** Uncapacitated congestion game (`u_e = n`), so every profile is feasible
and `Z` sums over all of `Pⁿ`. -/
noncomputable def gibbs {E : Type*} [Fintype E] [DecidableEq E] (P : Finset (Finset E)) (n : ℕ)
    (c : E → ℕ → ℝ) (T : ℝ) (s : Fin n → P) : ℝ :=
  Real.exp (-T * potential c s) / ∑ t : Fin n → P, Real.exp (-T * potential c t)

end GibbsCongestion


