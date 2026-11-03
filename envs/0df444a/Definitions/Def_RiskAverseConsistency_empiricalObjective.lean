-- Prove2me | Definitions.Def_RiskAverseConsistency_empiricalObjective
-- name    : RiskAverseConsistency_empiricalObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:22:57.215549+00:00
-- url     : https://prove2.me/theorems/d8c85203-01f4-4902-b0f5-e277d625d942
-- title:
--   Objective of the empirical approximation (10)
-- statement:
--   With the data of (8), let $\xi^1,\xi^2,\dots$ be i.i.d. copies of $\xi$ on $(\Omega',\mathcal F',P')$, let $\hat H_{y,N}(\cdot;\omega')$ be the empirical distribution function of $f(y,\xi^1(\omega')),\dots,f(y,\xi^N(\omega'))$ and $G:\Omega\to[0,1]$ uniform. The objective of the empirical approximation (10) is
--
--   $$
--   z\ \longmapsto\ \mathcal R[\hat H_{\mathbf Bz,N}]+\wp(z)=\mathcal R\bigl[\hat H^{-1}_{\mathbf Bz,N}(G(\cdot);\omega')\bigr]+\wp(z),
--   $$
--
--   and (10) is $\min_{z\in Z_{\mathrm{ad}}}\mathcal R[\hat H_{\mathbf Bz,N}]+\wp(z)$.
--
--   **Formalization Note** The sample is $\xi^0,\dots,\xi^{N-1}$ in Lean. The real value is cast to `EReal`, so that $\hat m^*_N$ and $\hat{\mathscr S}^r_N$ are `optimalValue` and `epsSolutionSet` of this function over $Z_{\mathrm{ad}}$.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, pp.8–9, (10)

import Mathlib
import Definitions.Def_RiskAverseConsistency_empiricalRisk

open MeasureTheory

namespace RiskAverseConsistency

/-- The objective of the empirical approximation (10): `z ↦ ℛ[Ĥ_{Bz,N}] + ℘(z)`, where
`ℛ[Ĥ_{Bz,N}] = ℛ(Ĥ⁻¹_{Bz,N}(G(·); ω′))` and `Ĥ_{y,N}(·; ω′)` is the empirical distribution function
of the sample `f(y, ξ¹(ω′)), …, f(y, ξᴺ(ω′))`.

Milz, Surowiec, arXiv:2207.14756v2, (10), pp.8–9, and p.9 (`ℛ[Ĥ_{y,N}(ω′)] = ℛ[Ĥ⁻¹_{y,N}(G(·); ω′)]`).

Formalization Note: the sample is `ξs 0, …, ξs (N-1)` (the paper's `ξ¹, …, ξᴺ`). The value is real
and is cast to `EReal`. -/
noncomputable def empiricalObjective {Ω Ω' Ξ Y Z : Type*} [MeasurableSpace Ω] {p : ENNReal}
    {P : Measure Ω} [AddCommGroup Y] [Module ℝ Y] [AddCommGroup Z] [Module ℝ Z]
    (ℛ : Lp ℝ p P → ℝ) (G : Ω → ℝ) (ξs : ℕ → Ω' → Ξ) (f : Y → Ξ → ℝ) (B : Z →ₗ[ℝ] Y)
    (φ : Z → ℝ) (N : ℕ) (ω' : Ω') : Z → EReal :=
  fun z => ((empiricalRisk ℛ G (fun i => f (B z) (ξs i ω')) N + φ z : ℝ) : EReal)

end RiskAverseConsistency


