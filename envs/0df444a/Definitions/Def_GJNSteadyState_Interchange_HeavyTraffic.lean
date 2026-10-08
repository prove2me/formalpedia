-- Prove2me | Definitions.Def_GJNSteadyState_Interchange_HeavyTraffic
-- name    : GJNSteadyState_Interchange_HeavyTraffic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:55.685724+00:00
-- url     : https://prove2.me/theorems/e1717f85-ed10-4664-9d43-4b94c2e10155
-- title:
--   §2.3, p. 12 and Theorem 4, p. 14 — the heavy-traffic sequence Ξⁿ, κ, the RBM drift β and covariance Γ
-- statement:
--   Fix a critically loaded generalized Jackson network $\Xi$ ($\rho_j=1$ for every station $j$, so $\lambda=\mu$) and a vector $\kappa^0=(\kappa^0_1,\dots,\kappa^0_J)$ of strictly positive constants. For $n\ge1$ the network $\Xi^n$ has the same service-time laws and routing as $\Xi$, while its interarrival times at station $j$ are
--   $$a^n_j(l) = \frac{a_j(l)}{1-\kappa^0_j/\sqrt n},$$
--   so that its external arrival rates are $\alpha^n_j = \alpha_j(1-\kappa^0_j/\sqrt n)$ (this is meaningful once $n>\max_j(\kappa^0_j)^2$). Its effective arrival rates are $\lambda^n = \lambda - n^{-1/2}[I-P']^{-1}(\alpha\circ\kappa^0)$, where $(\alpha\circ\kappa^0)_j=\alpha_j\kappa^0_j$, and its traffic intensities satisfy
--   $$\rho^n_j = 1-\frac{\kappa_j}{\sqrt n},\qquad \kappa_j := m_j\big([I-P']^{-1}(\alpha\circ\kappa^0)\big)_j. \tag{17}$$
--   The limiting reflected Brownian motion of Theorem 4 has drift $\beta = -(I-P')M^{-1}\kappa$ and covariance matrix
--   $$\Gamma_{k\ell} = \sum_{j=1}^J \mu_j\big[p_{jk}(\delta_{k\ell}-p_{j\ell}) + c^2_{s,j}(p_{jk}-\delta_{jk})(p_{j\ell}-\delta_{j\ell})\big] + \alpha_k c^2_{a,k}\delta_{k\ell},$$
--   all computed from the critical network $\Xi$.
--
--   These are the parameters of the heavy-traffic regime in which the paper's main theorem is stated.
--
--   **Formalization Note** The page writes $a^n_j = a_j(1-\kappa^0_j/\sqrt n)$, which would shorten interarrival times and make every $\Xi^n$ overloaded ($\rho^n_j>1$), contradicting (17), Theorem 2's use and the page's own "$\alpha^n_j<\alpha_j$" (p. 30); the reading $a_j/(1-\kappa^0_j/\sqrt n)$ is used. With it, (17) holds exactly with the $\kappa$ above; the page's "$\lambda^n=\lambda-n^{-1/2}\kappa$, $\kappa=[I-P']^{-1}\kappa^0$" is off by the factors $M^{-1}$ and $\alpha$. Then $\beta = -\alpha\circ\kappa^0$ and $[I-P']^{-1}\beta = -M^{-1}\kappa<0$ (Remark 4). "The residual interarrival times remain unchanged" is read as concerning the initial datum only: $\Xi^n$ is a GJN with parameters $(F^n_A,F_S,P)$ and its residual interarrival laws are those of $F^n_A$, which is what makes $\bar Q^n$ Markov. For small $n$ (factor $\le 0$) $\Xi^n$ is a meaningless network; every statement about it is for all sufficiently large $n$.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 12, Section 2.3 (Ξⁿ, (17)); p. 14, Theorem 4 (β, Γ) and Remark 4; p. 30 (αⁿ_j < α_j)

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Network

open MeasureTheory Filter Topology Matrix

namespace GJNSteadyState.Interchange

/-!
Gamarnik–Zeevi (2006), §2.3, p. 12, and Theorem 4, p. 14: the heavy-traffic sequence `Ξⁿ`
built from a critically loaded network `Ξ` and a vector `κ⁰ > 0`, and the drift `β` and the
covariance matrix `Γ` of the limiting reflected Brownian motion.
-/

/-- The `n`-th network `Ξⁿ` of the heavy-traffic sequence (§2.3, p. 12): service times and
routing as in `Ξ`, and interarrival times at station `j` slowed down by the factor
`1 − κ⁰_j/√n`, i.e. `aⁿ_j(l) = a_j(l)/(1 − κ⁰_j/√n)`, so that `αⁿ_j = α_j (1 − κ⁰_j/√n)`.
(Meaningful for `n > max_j (κ⁰_j)²`; every statement about `Ξⁿ` is for all large `n`.) -/
noncomputable def htNet {J : ℕ} (Ξ : Network J) (κ0 : Fin J → ℝ) (n : ℕ) : Network J where
  arrSet := Ξ.arrSet
  FA := fun j => (Ξ.FA j).map (fun a => a / (1 - κ0 j / Real.sqrt n))
  FS := Ξ.FS
  P := Ξ.P

/-- `κ_j = m_j ([I − P′]⁻¹ (α ∘ κ⁰))_j`, so that `ρⁿ_j = 1 − κ_j/√n` (17). -/
noncomputable def kappa {J : ℕ} (Ξ : Network J) (κ0 : Fin J → ℝ) (j : Fin J) : ℝ :=
  meanS Ξ j * ((1 - Ξ.Pᵀ)⁻¹ *ᵥ (fun i => alpha Ξ i * κ0 i)) j

/-- The RBM drift `β = −(I − P′) M⁻¹ κ` of Theorem 4 (p. 14), `M⁻¹ = diag(μ)`. -/
noncomputable def beta {J : ℕ} (Ξ : Network J) (κ0 : Fin J → ℝ) : Fin J → ℝ :=
  -((1 - Ξ.Pᵀ) *ᵥ (fun j => mu Ξ j * kappa Ξ κ0 j))

/-- The RBM covariance matrix of Theorem 4 (p. 14):
`Γ_{kℓ} = Σ_j μ_j [p_jk (δ_kℓ − p_jℓ) + c²_{s,j} (p_jk − δ_jk)(p_jℓ − δ_jℓ)] + α_k c²_{a,k} δ_kℓ`,
with the parameters of the critical network `Ξ`. -/
noncomputable def Gamma {J : ℕ} (Ξ : Network J) : Matrix (Fin J) (Fin J) ℝ :=
  fun k l =>
    (∑ j, mu Ξ j * (Ξ.P j k * ((if k = l then 1 else 0) - Ξ.P j l)
        + cs2 Ξ j * (Ξ.P j k - (if j = k then 1 else 0)) * (Ξ.P j l - (if j = l then 1 else 0))))
      + alpha Ξ k * ca2 Ξ k * (if k = l then 1 else 0)

end GJNSteadyState.Interchange


