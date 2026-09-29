-- Prove2me | Definitions.Def_WangZahlKakeya_assertions
-- name    : WangZahlKakeya_assertions
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-20T11:28:40.374036+00:00
-- url     : https://prove2.me/theorems/34c8a706-556e-4e00-be89-efd5d3e5b215
-- title:
--   Assertions $D(\sigma,\omega)$ and $E(\sigma,\omega)$
-- statement:
--   This file states the two families of volume estimates of Wang–Zahl, Definition 1.5. They are parametrized by two nonnegative numbers $\sigma$ and $\omega$; smaller values are stronger statements, and the endpoint $\sigma = \omega = 0$ is what the paper ultimately proves.
--
--   **Assertion $D(\sigma,\omega)$.** For every $\varepsilon > 0$ there exist $\kappa, \eta > 0$ such that for every $\delta > 0$ and every nonempty system $(\mathbb{T},Y)_\delta$ of essentially distinct $\delta$-tubes in the unit ball which is $\delta^\eta$-dense and satisfies
--
--   $$C_{\mathrm{KT\text{-}CW}}(\mathbb{T}) \le \delta^{-\eta}, \qquad C_{\mathrm{F\text{-}SW}}(\mathbb{T}) \le \delta^{-\eta},$$
--
--   one has
--
--   $$\Big|\bigcup_{T \in \mathbb{T}} Y(T)\Big| \;\ge\; \kappa\, \delta^{\omega+\varepsilon}\,(\#\mathbb{T})|T| \,\big((\#\mathbb{T})|T|^{1/2}\big)^{-\sigma}.$$
--
--   **Assertion $E(\sigma,\omega)$.** For every $\varepsilon > 0$ there exist $\kappa, \eta > 0$ such that for every $\delta > 0$ and every nonempty $\delta^\eta$-dense system $(\mathbb{T},Y)_\delta$ — with no Wolff-axiom hypothesis — one has
--
--   $$\Big|\bigcup_{T \in \mathbb{T}} Y(T)\Big| \;\ge\; \kappa\, \delta^{\omega+\varepsilon}\, m^{-1}(\#\mathbb{T})|T|\,\big(m^{-3/2}\,\ell\,(\#\mathbb{T})|T|^{1/2}\big)^{-\sigma},$$
--
--   where $m = C_{\mathrm{KT\text{-}CW}}(\mathbb{T})$ and $\ell = C_{\mathrm{F\text{-}SW}}(\mathbb{T})$.
--
--   In the special case $\sigma = \omega$, Assertion $D(\sigma,\sigma)$ says that at most $\delta^{-\varepsilon}(\#\mathbb{T})^{\sigma}$ tubes pass through a typical point of the shaded union, so small $\sigma$ means the union is almost disjoint. $E(\sigma,\omega)$ formally implies $D(\sigma,\omega)$, and the paper's Proposition 1.6 gives the converse for $0 \le \sigma \le 2/3$. Both assertions are designed to be stable under the anisotropic rescalings used in induction on scales, which is why the Wolff constants appear explicitly in $E$.
--
--   **Formalization Note** The exponents are real, so all powers are real powers of nonnegative reals. The systems quantified over are required to be nonempty, excluding the degenerate empty family. Volumes are compared as real numbers.
-- source:
--   Hong Wang and Joshua Zahl, *Volume estimates for unions of convex sets, and the Kakeya set conjecture in three dimensions*, arXiv:2502.17655v1 (2025), https://arxiv.org/abs/2502.17655, §1.2, Definition 1.5 (inequalities (1.2) and (1.3))

import Definitions.Def_WangZahlKakeya_wolff

/-!
# Assertions D(σ, ω) and E(σ, ω)

Definition 1.5 of Wang–Zahl, *Volume estimates for unions of convex sets, and the Kakeya set
conjecture in three dimensions* (arXiv:2502.17655v1): the two families of Kakeya-type volume
estimates for unions of shaded `δ`-tubes in `ℝ³`.
-/

namespace WangZahlKakeya

open MeasureTheory Metric Set

/-- **Assertion D(σ, ω)** (Definition 1.5, inequality (1.2)).

For every `ε > 0` there are `κ, η > 0` so that for every `δ > 0` and every nonempty system
`(T, Y)_δ` of essentially distinct `δ`-tubes in the unit ball which is `δ^η` dense and obeys
both the Katz–Tao Convex Wolff Axioms and the Frostman Slab Wolff Axioms with error at most
`δ^{-η}`, one has

`|⋃_T Y(T)| ≥ κ δ^{ω+ε} (#T)|T| ((#T)|T|^{1/2})^{-σ}`. -/
def AssertionD (σ ω : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ κ > (0 : ℝ), ∃ η > (0 : ℝ), ∀ δ > (0 : ℝ),
    ∀ (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3),
      0 < n →
      IsTubeSystem δ n p v Y →
      IsDenseSystem δ n Y (δ ^ η) →
      KTCW δ n p v ≤ δ ^ (-η) →
      FSW δ n p v ≤ δ ^ (-η) →
      (volume (shadingUnion Y)).toReal ≥
        κ * δ ^ (ω + ε) * ((n : ℝ) * tubeVol δ) *
          ((n : ℝ) * (tubeVol δ) ^ ((1 : ℝ) / 2)) ^ (-σ)

/-- **Assertion E(σ, ω)** (Definition 1.5, inequality (1.3)).

For every `ε > 0` there are `κ, η > 0` so that for every `δ > 0` and every nonempty system
`(T, Y)_δ` of essentially distinct `δ`-tubes in the unit ball which is `δ^η` dense, one has

`|⋃_T Y(T)| ≥ κ δ^{ω+ε} m^{-1} (#T)|T| (m^{-3/2} ℓ (#T)|T|^{1/2})^{-σ}`,

where `m = C_{KT-CW}(T)` and `ℓ = C_{F-SW}(T)`. -/
def AssertionE (σ ω : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ κ > (0 : ℝ), ∃ η > (0 : ℝ), ∀ δ > (0 : ℝ),
    ∀ (n : ℕ) (p v : Fin n → E3) (Y : Fin n → Set E3),
      0 < n →
      IsTubeSystem δ n p v Y →
      IsDenseSystem δ n Y (δ ^ η) →
      (volume (shadingUnion Y)).toReal ≥
        κ * δ ^ (ω + ε) * (KTCW δ n p v)⁻¹ * ((n : ℝ) * tubeVol δ) *
          ((KTCW δ n p v) ^ (-(3 : ℝ) / 2) * (FSW δ n p v) *
            ((n : ℝ) * (tubeVol δ) ^ ((1 : ℝ) / 2))) ^ (-σ)

end WangZahlKakeya


