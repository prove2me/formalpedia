-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_linParams__05dfee
-- name    : IntroDelayAMDP_Supplement_linParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:49:44.18906+00:00
-- url     : https://prove2.me/theorems/05dfeec4-dc89-4c70-85b6-ba410a98294f
-- title:
--   The parameters of Algorithms 3 and 5 (App. B.1)
-- statement:
--   For universal constants $C$ and $C_0$, a delay cap $\bar d$, dimension $d$, horizon $H$, $A$ actions, $K$ episodes with $\sqrt K$ an integer and $\delta\in(0,1/2)$, let $\iota=\log(16KdHA/\delta)$, $\rho=2d\log(1+1/\lambda)$, $J_0=\lceil\log_2(2\sqrt K)\rceil$ and
--   $$\lambda=(KdH)^{-C},\quad m_0=\lceil C_0\rho\iota\rceil,\quad\nu=\lceil C_0m_0\iota\rceil,\quad\eta=\frac1{200H^3(\sqrt K+2\bar d)(\nu+4)},$$
--   $$d_{VC}=\bigl\lceil2(d+1)(d+2)(J_0+1)\log_2(J_0+2)\bigr\rceil,\qquad\theta=\frac{C_0}{\sqrt K}\bigl(\rho(d_{VC}\iota+\iota^2)+m_0^2\bigr).$$
--   These are the parameters of Theorem 4.1 (with $\bar d=0$) and of Theorem 5.2 (with $\bar d=\lceil\sqrt{D/(dH^2)}\rceil$).
--
--
--   **Formalization Note** $\log$ is natural and $\log_2$ is the base-$2$ logarithm.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), App. B.1, p.44

import Mathlib
import Definitions.Def_IntroDelayAMDP_Supplement_LinParams

namespace IntroDelayAMDP.Supplement

/-- **The parameters of Algorithms 3 and 5** (App. B.1, printed p.44, PDF p.46, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530)). Printed p.44: "Let `C₁`, `C`, and `C₀`
be universal constants, each large enough given the previous ones, and let `ι ≜ log(16KdHA/δ)`,
`ρ ≜ 2d log(1 + 1/λ)`, and `J₀ ≜ ⌈log₂(2√K)⌉` … We pick `λ = (KdH)^{−C}`, `m₀ = ⌈C₀ρι⌉`, `ν = ⌈C₀m₀ι⌉`,
`η = 1/(200H³(√K + 2d̄)(ν + 4))`, `d_VC = ⌈2(d + 1)(d + 2)(J₀ + 1) log₂(J₀ + 2)⌉`, and
`θ = (C₀/√K)(ρ(d_VC ι + ι²) + m₀²)`. Here … `d̄` is the cap on the delays, which is `0` in this appendix and
only kept for Appendix C."
`linParams C C₀ d̄ d H A K √K δ` has exactly these values (`A` the number of actions).

**Formalization Note.** `log` is natural, `log₂ = Real.logb 2`; `⌈·⌉ = Nat.ceil`; `(KdH)^{−C}` is `Real.rpow`. -/
noncomputable def linParams (C C0 : ℝ) (dbar d H A K sqrtK : ℕ) (δ : ℝ) : LinParams :=
  let ι : ℝ := Real.log (16 * K * d * H * A / δ)
  let lam : ℝ := ((K : ℝ) * d * H) ^ (-C)
  let ρ : ℝ := 2 * d * Real.log (1 + 1 / lam)
  let J0 : ℕ := ⌈Real.logb 2 (2 * sqrtK)⌉₊
  let m0 : ℕ := ⌈C0 * ρ * ι⌉₊
  let ν : ℕ := ⌈C0 * m0 * ι⌉₊
  let dVC : ℕ := ⌈2 * ((d : ℝ) + 1) * ((d : ℝ) + 2) * ((J0 : ℝ) + 1) * Real.logb 2 ((J0 : ℝ) + 2)⌉₊
  { lam := lam, m0 := m0, nu := ν,
    eta := 1 / (200 * (H : ℝ) ^ 3 * ((sqrtK : ℝ) + 2 * dbar) * ((ν : ℝ) + 4)),
    theta := C0 / sqrtK * (ρ * (dVC * ι + ι ^ 2) + (m0 : ℝ) ^ 2) }

end IntroDelayAMDP.Supplement


