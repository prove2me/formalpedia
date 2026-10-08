-- Prove2me | Definitions.Def_GenEmpLik_Expansion_reparamSets
-- name    : GenEmpLik_Expansion_reparamSets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:25:31.270922+00:00
-- url     : https://prove2.me/theorems/403f87e6-1ab3-49f0-92a9-acfd312fb18c
-- title:
--   The sets $\mathcal U_{\rm sm}\subset\mathcal U\subset\mathcal U_{\rm big}$ of (31)
-- statement:
--   Fix $n\ge1$, $\rho>0$, a divergence function $f$, and constants $\epsilon,C$. Writing a weight vector as $p=u+\mathbb 1/n$, the paper introduces three sets of perturbations $u\in\mathbb R^n$:
--
--   $$
--   \begin{aligned}
--   \mathcal U_{\rm sm}&=\Big\{u\in\mathbb R^n : \mathbb 1^Tu=0,\ \|nu\|_\infty\le\epsilon,\ (1+C\epsilon)\|nu\|_2^2\le\rho\Big\},\\
--   \mathcal U&=\Big\{u\in\mathbb R^n : \mathbb 1^Tu=0,\ u\ge-1/n,\ \sum_{i=1}^n f(nu_i+1)\le\rho\Big\},\\
--   \mathcal U_{\rm big}&=\Big\{u\in\mathbb R^n : \mathbb 1^Tu=0,\ \sum_{i=1}^n h_\epsilon(nu_i)\le\frac{\rho}{2(1-C\epsilon)}\Big\},
--   \end{aligned}
--   $$
--
--   where $h_\epsilon$ is the Huber function. $\mathcal U$ is the $f$-divergence ball around the uniform weights, recentred; $\mathcal U_{\rm sm}$ and $\mathcal U_{\rm big}$ are an inner quadratic and an outer Huber approximation of it.
--
--   **Formalization Note** The three sets are `Usm n ε C ρ`, `Umid f n ρ` and `Ubig n ε C ρ`. The sum in `Umid` is in `EReal`, since $f$ may be $+\infty$ at $0$. The inclusions $\mathcal U_{\rm sm}\subset\mathcal U\subset\mathcal U_{\rm big}$ are not part of the definition; they hold when the sandwich (30) holds at $\epsilon<1$ and $C$ with $C\epsilon<1$ (milestone (32)).
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, p. 32, (31)

import Mathlib
import Definitions.Def_GenEmpLik_Expansion_huber

namespace GenEmpLik.Expansion

/-- The small set of (31) (Duchi, Glynn & Namkoong, arXiv:1610.03425v3, p. 32):
`𝒰_sm = {u ∈ ℝⁿ | 𝟙ᵀu = 0, ‖n u‖_∞ ≤ ε, (1 + Cε) ‖n u‖₂² ≤ ρ}`. -/
def Usm (n : ℕ) (ε C ρ : ℝ) : Set (Fin n → ℝ) :=
  {u | ∑ i, u i = 0 ∧ (∀ i, |(n : ℝ) * u i| ≤ ε) ∧
    (1 + C * ε) * ∑ i, ((n : ℝ) * u i) ^ 2 ≤ ρ}

/-- The middle set `𝒰` of (31) (p. 32): `𝒰 = {u ∈ ℝⁿ | 𝟙ᵀu = 0, u ≥ −1/n, ∑ᵢ f(n uᵢ + 1) ≤ ρ}`,
the f-divergence ball around the uniform weights re-centred by `u = p − 𝟙/n` (the sum is taken
in `EReal`, since `f` may be `+∞` at `0`). -/
def Umid (f : ℝ → EReal) (n : ℕ) (ρ : ℝ) : Set (Fin n → ℝ) :=
  {u | ∑ i, u i = 0 ∧ (∀ i, -1 / (n : ℝ) ≤ u i) ∧
    ∑ i, f ((n : ℝ) * u i + 1) ≤ (ρ : EReal)}

/-- The big set of (31) (p. 32):
`𝒰_big = {u ∈ ℝⁿ | 𝟙ᵀu = 0, ∑ᵢ h_ε(n uᵢ) ≤ ρ / (2(1 − Cε))}`, with `h_ε` the Huber function. -/
def Ubig (n : ℕ) (ε C ρ : ℝ) : Set (Fin n → ℝ) :=
  {u | ∑ i, u i = 0 ∧ ∑ i, huber ε ((n : ℝ) * u i) ≤ ρ / (2 * (1 - C * ε))}

end GenEmpLik.Expansion


