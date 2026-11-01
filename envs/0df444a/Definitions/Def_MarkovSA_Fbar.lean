-- Prove2me | Definitions.Def_MarkovSA_Fbar
-- name    : MarkovSA_Fbar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:12.381521+00:00
-- url     : https://prove2.me/theorems/193f73ed-eb3b-4c3a-a747-a870743ef74e
-- title:
--   Expected operator $\bar F(x)=\mathbb E_{Y\sim\mu}[F(x,Y)]$
-- statement:
--   Let $\mathcal Y$ be a finite set, $\mu$ a distribution on $\mathcal Y$ and $F:E\times\mathcal Y\to E$. The **expected operator** is
--
--   $$
--   \bar F(x)=\mathbb E_{Y\sim\mu}[F(x,Y)]=\sum_{y\in\mathcal Y}\mu(y)\,F(x,y).
--   $$
--
--   The stochastic approximation scheme seeks the solution $x^*$ of $\bar F(x)=x$ (Eq. (5)).
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, §2.1, Eq. (5), p.5

import Mathlib

namespace MarkovSA

/-- The **expected operator** `F̄(x) = E_{Y∼μ}[F(x, Y)] = Σ_y μ(y) F(x, y)` of Eq. (5)
(Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §2.1, p.5), for a finite set `𝒴` and a distribution `μ` on it. -/
noncomputable def Fbar {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴]
    (F : E → 𝒴 → E) (μ : 𝒴 → ℝ) (x : E) : E :=
  ∑ y, μ y • F x y

end MarkovSA


