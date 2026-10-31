-- Prove2me | Definitions.Def_CryptoMiningMFG_IsEquilibrium
-- name    : CryptoMiningMFG_IsEquilibrium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:37.780988+00:00
-- url     : https://prove2.me/theorems/16a1ff3a-5b87-4091-a819-c13c1b2ecf5b
-- title:
--   Equilibrium mean hash rate (2.8)
-- statement:
--   Let $m_0$ be the law of the miners' initial wealth at time $t_0$. A mean hash rate $\bar\alpha$ is an **equilibrium mean hash rate** when:
--
--   1. $\bar\alpha$ is admissible (measurable and positive on $[t_0,T]$);
--   2. $v(t,\cdot;\bar\alpha)$ is differentiable for every $t\in[t_0,T]$;
--   3. the feedback $\alpha^*$ of (2.6) is realized: there is a control for each initial wealth $x_0$ such that, for the miner started at $(t_0,x_0)$, almost surely and for almost every $s\in[t_0,T]$, the hash rate in force at time $s$ equals $\alpha^*(s,X_s;\bar\alpha)$;
--   4. the consistency condition (2.8) holds: for every $t\in[t_0,T]$,
--
--   $$
--   \bar\alpha_t=\int_{\mathbb R}\alpha^*(t,x;\bar\alpha)\,m(t,dx),
--   $$
--
--   where $m(t,\cdot)$ is the law of the closed-loop wealth $X_t$ when the initial wealth has law $m_0$ and is independent of the reward clocks.
--
--   The mean hash rate the population produces when every miner follows its optimal feedback is the one each miner took as given.
--
--   **Formalization Note** The paper's density $m(t,x)$ is read as the law of $X_t$; the Fokker–Planck equation (2.11) is the equation it satisfies and is not imposed separately. The integral in (2.8) is a lower Lebesgue integral of $\max(\alpha^*,0)$; for exponential utility $\alpha^*\ge0$, so nothing is clipped.
-- source:
--   Li, Reppen, Sircar, A Mean Field Games Model for Cryptocurrency Mining, arXiv:1912.01952v2 (preprint, 22 Jan 2022), https://arxiv.org/abs/1912.01952v2, §2.5 p.11, eq. (2.8) and the assumptions "ᾱ*_t ≠ 0 for all t", "v is a classical solution of (2.5)" (p.11)

import Mathlib
import Definitions.Def_CryptoMiningMFG_Admissible
import Definitions.Def_CryptoMiningMFG_optRate

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CryptoMiningMFG

/-- **Equilibrium mean hash rate**, §2.5, p.11 of Li, Reppen, Sircar, arXiv:1912.01952v2:
"Let α*(t, x; ᾱ) be the optimal hash rate of miner x, and denote by m(t, x; ᾱ) the resulting
density of the miners' wealth … We say ᾱ* forms an equilibrium mean hash rate of the mining game if
ᾱ*_t = ∫_ℝ α*(t, x; ᾱ*) m(t, x; ᾱ*) dx, ∀ t ∈ [t0, T]. (2.8)"

`IsEquilibrium P m0 ᾱ` holds when
1. `ᾱ` is admissible (measurable, positive on `[t0, T]`; "We assume that ᾱ*_t ≠ 0 for all t");
2. `v(t, ·; ᾱ)` is differentiable for every `t ∈ [t0, T]` (the paper's "v is a classical
   solution", restricted to the `∂ₓv` that (2.6) uses);
3. there is a family `ψ` of controls, one per initial wealth `x₀`, that realizes the feedback (2.6):
   started at `(t0, x₀)`, for almost every clock path and almost every `s ∈ [t0, T]`, the hash rate
   in force at `s` is `α*(s, X_s; ᾱ)`, with `X` the wealth of that path (the closed loop
   `α*(t, X_t)`);
4. consistency (2.8): for every `t ∈ [t0, T]`, `ᾱ_t = ∫∫ α*(t, X_t^{x₀}(E)) dclockLaw(E) dm0(x₀)`,
   i.e. `∫ α*(t, x) m(t, dx)` with `m(t, ·)` the law of `X_t` when the initial wealth has law `m0`
   and is independent of the reward clocks.

**Formalization Note.** The paper's density `m(t, ·)` is read as the law of the closed-loop wealth
`X_t`; the Fokker–Planck equation (2.11) is the equation this law satisfies and is not imposed
separately. The initial law `m0` is a measure (the theorems take a probability measure); the
paper's `m0` is a C¹ density with total mass one. `α*` is clipped below at `0` inside the
lower integral (`ENNReal.ofReal`); for an admissible `ᾱ` with `∂ₓv > 0` and `Δv > 0` it is
nonnegative, so nothing is clipped. -/
def IsEquilibrium (P : Model) (m0 : Measure ℝ) (abar : ℝ → ℝ) : Prop :=
  Admissible P abar ∧
  (∀ t ∈ Icc P.t0 P.T, ∀ x : ℝ, DifferentiableAt ℝ (fun y => value P t y abar) x) ∧
  ∃ ψ : ℝ → Control,
    (∀ x₀ : ℝ, ∀ᵐ E ∂clockLaw, ∀ᵐ s ∂(volume.restrict (Icc P.t0 P.T)),
      (ψ x₀).rateAt P abar P.t0 E s = optRate P abar s ((ψ x₀).wealth P abar P.t0 x₀ E s)) ∧
    ∀ t ∈ Icc P.t0 P.T, ENNReal.ofReal (abar t) =
      ∫⁻ x₀, ∫⁻ E, ENNReal.ofReal (optRate P abar t ((ψ x₀).wealth P abar P.t0 x₀ E t))
        ∂clockLaw ∂m0

end CryptoMiningMFG


