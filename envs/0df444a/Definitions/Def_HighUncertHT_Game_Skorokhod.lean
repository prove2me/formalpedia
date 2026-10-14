-- Prove2me | Definitions.Def_HighUncertHT_Game_Skorokhod
-- name    : HighUncertHT_Game_Skorokhod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:33:35.273987+00:00
-- url     : https://prove2.me/theorems/2cd92370-c6f5-4c52-9ad9-d2c2b7ae898b
-- title:
--   (10), p. 7 — the Skorokhod map Γ = (Γ₁, Γ₂) on the half line
-- statement:
--   The **Skorokhod map on the half line** sends a path $\psi:[0,\infty)\to\mathbb R$ to the pair $(\varphi,\eta)=\Gamma(\psi)$,
--   $$
--   \eta(t)=\Gamma_2(\psi)(t)=\sup_{0\le s\le t}\psi(s)^-,\qquad \varphi(t)=\Gamma_1(\psi)(t)=\psi(t)+\eta(t),\qquad t\ge0,
--   $$
--   where $x^-=\max(-x,0)$. The path $\varphi$ is the reflection of $\psi$ at the origin and $\eta$ is the minimal nondecreasing pushing that keeps it nonnegative.
--
--   In the scheduling game, $(W^{\mathrm{tot},n},R^n)=\Gamma(A^{\mathrm{tot},n}-n\,\mathrm{id})$ for every work-conserving strategy, which expresses work conservation.
--
--   **Formalization Note** Paths are functions $\mathbb R\to\mathbb R$ of which only times $t\ge0$ are used. The supremum is the real supremum over $s\in[0,t]$; it equals the paper's value whenever $\psi$ is bounded below on $[0,t]$, in particular for càdlàg $\psi$, the paper's domain.
-- source:
--   Atar, Castiel, Shadmi, Scheduling in the High Uncertainty Heavy Traffic Regime, arXiv:2204.05733v1, p. 7, (10)

import Mathlib

namespace HighUncertHT.Game

/-!
Atar, Castiel, Shadmi, arXiv:2204.05733v1, §2.1.2, p. 7, (10): the Skorokhod map on the half line,
`Γ(ψ) = (φ, η)` with `η(t) = sup_{0 ≤ s ≤ t} ψ(s)⁻` and `φ = ψ + η`. Paths are functions `ℝ → ℝ`;
only times `t ≥ 0` are used.
-/

/-- `Γ₂(ψ)(t) = sup_{0 ≤ s ≤ t} ψ(s)⁻`, with `x⁻ = max(-x, 0)` ((10), p. 7). The supremum is the
real supremum over `s ∈ [0, t]`; it is the paper's value whenever `ψ` is bounded below on `[0, t]`,
in particular for every càdlàg `ψ`, which is the paper's domain `𝒟_ℝ[0, ∞)`. -/
noncomputable def skorokhodΓ₂ (ψ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ⨆ s : Set.Icc (0 : ℝ) t, max (-ψ s) 0

/-- `Γ₁(ψ)(t) = ψ(t) + Γ₂(ψ)(t)` ((10), p. 7): the reflected path. -/
noncomputable def skorokhodΓ₁ (ψ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ψ t + skorokhodΓ₂ ψ t

end HighUncertHT.Game


