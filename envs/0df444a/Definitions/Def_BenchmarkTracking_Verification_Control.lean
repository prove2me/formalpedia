-- Prove2me | Definitions.Def_BenchmarkTracking_Verification_Control
-- name    : BenchmarkTracking_Verification_Control
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:06.676348+00:00
-- url     : https://prove2.me/theorems/41d34731-37be-4ab6-a43e-40ce03bc4a33
-- title:
--   (1.2)–(1.4), (2.1)–(2.5), (4.3)–(4.4) — reflected wealth, admissible strategies $\mathbb U^r$, objective, and the feedback system
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb F,\mathbb P)$ be a filtered probability space satisfying the usual conditions and carrying a $d$-dimensional $\mathbb F$-Brownian motion $W$ (p. 2). Write $W^\gamma=\sum_j\gamma_jW^j$ and $W^\eta=\sum_j\eta_jW^j$.
--
--   1. **Benchmark and auxiliary state $I$** ((1.3), (2.4)). $Z_t=z\exp((\mu_Z-\frac12\sigma_Z^2)t+\sigma_ZW^\eta_t)$. With $h=I_0=m\vee b-b\ge0$, the increment of the running maximum $m_t=\max\{m,\sup_{s\le t}B_s\}$ is $m_t-m_0=(\sup_{s\le t}(\mu_Bs+\sigma_BW^\gamma_s)-h)^+$, and $I_t=h-\mu_Bt-\sigma_BW^\gamma_t+(m_t-m_0)$.
--   2. **Admissible strategies $\mathbb U^r$** (p. 4). Pairs $(\theta,c)$ of progressively measurable processes with values in $\mathbb R^d\times\mathbb R_+$, with $\int_0^T(|\theta_s|^2+c_s)ds<\infty$ for every $T$, together with a continuous version of the stochastic integral $\int_0^t\theta_s^\top\sigma\,dW_s$.
--   3. **Reflected wealth** ((2.2), (2.3)). With $Y_t=x+\int_0^t\theta_s^\top\mu\,ds+\int_0^t\theta_s^\top\sigma\,dW_s-\int_0^tc_sds-(Z_t-z)-(m_t-m_0)$, the regulator is $L^X_t=\sup_{s\le t}(-Y_s)^+$ and $X_t=Y_t+L^X_t\ge0$.
--   4. **Objective** (2.5). The utility part $\mathbb E[\int_0^\infty e^{-\rho t}c_t^p/p\,dt]$ and the cost part $\mathbb E[\int_0^\infty e^{-\rho t}dL^X_t]$, so that $J(x,h,z;\theta,c)$ is the first minus $\beta$ times the second.
--   5. **Feedback** (4.3): for a function $u$ on $\mathbb R^3_+$,
--   $$
--   \theta^*(x,h,z)=-(\sigma\sigma^\top)^{-1}\frac{\mu u_x-\sigma_B\sigma\gamma u_{xh}+\sigma_Z\sigma\eta z(u_{xx}-u_{xz})}{u_{xx}},\qquad c^*(x,h,z)=u_x^{\frac1{p-1}}.
--   $$
--   6. **The controlled reflected system (4.4).** A solution started at $(x,h,z)$ is an adapted continuous process $X^*$ such that $(\theta^*_t,c^*_t)=(\theta^*,c^*)(X^*_t,I_t,Z_t)$ is in $\mathbb U^r$ and $X^*$ is the reflected wealth of that strategy, with $L^{X^*}_0=0$.
--
--   These are the objects of the verification theorem: $u$ dominates the objective of every admissible strategy, and the feedback strategy attains it.
--
--   **Formalization Note** The usual conditions and the $\mathbb F$-Brownian motion are the published `RankBasedSDI.LoadBalancing.UsualConditions` and `IsFBrownian`; the stochastic integral is the published `EthierKurtz.HasBrownianItoIntegral` (square integrability of the integrand for every $\omega$, a mild strengthening of "a.s."), applied coordinatewise to $\sigma^\top\theta$ against $W^j$. Since $\int_0^t\mu_ZZ_sds+\int_0^t\sigma_ZZ_sdW^\eta_s=Z_t-z$ for the geometric Brownian motion, the only genuine stochastic integral in (2.3) is $\int\theta^\top\sigma dW$; $Z$, $m$ and $L^X$ are written in closed form. The paper's p. 6 prints $X_t:=L_t-D_t$; with $X_0=x$ and (2.3) the intended reading is $X_t=x-D_t+L_t$. The utility part is an extended real, $(1/p)$ times a `lintegral` of $e^{-\rho t}c_t^p$ with $c^p$ computed in $[0,\infty]$, so $0^p=+\infty$ for $p<0$ as in the paper; the cost part is a `lintegral` in $[0,\infty]$. The paper's clause "the SDE (1.2) admits a weak solution on $[0,T]$" is read as the integrability that makes (1.2) well defined.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, p. 2 (1.2)–(1.3), p. 4 (𝕌^r), pp. 5–6 (2.1)–(2.5), p. 19 (4.3)–(4.4)

import Mathlib
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Analysis
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

open MeasureTheory Set Matrix
open scoped ENNReal NNReal Matrix

namespace BenchmarkTracking.Verification

/-!
Bo, Huang & Yu, arXiv:2302.08302v4, §1 p. 2 and p. 4, §2 pp. 5–6, (4.3)–(4.4) p. 19: the
auxiliary control problem (2.5) with the reflected states `X` (2.3) and `I` (2.4), the benchmark
GBM `Z` (1.3), the objective, the admissible class `𝕌^r`, and the feedback control (4.3) with
the controlled reflected system (4.4).

The basis is `(Ω, F, 𝔽, P)` with a `d`-dimensional `𝔽`-Brownian motion `W`, in the path
convention of `RankBasedSDI.LoadBalancing.IsFBrownian` (`W ω t j`, real `t ≥ 0`). Strategies,
Itô integrals and states are indexed by `ℝ≥0`; paths used by the Skorokhod regulator are indexed
by `ℝ` and evaluated at `t ≥ 0`.
-/

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A filtered probability space satisfying the usual conditions and carrying a `d`-dimensional
`𝔽`-Brownian motion `W` (p. 2). -/
def IsControlBasis (Pr : Measure Ω) (F : Filtration ℝ≥0 mΩ) (W : Ω → ℝ → Fin d → ℝ) : Prop :=
  IsProbabilityMeasure Pr ∧ RankBasedSDI.LoadBalancing.UsualConditions Pr F ∧
    RankBasedSDI.LoadBalancing.IsFBrownian Pr F W

/-- `W^γ_t = Σ_j γ_j W^j_t` (p. 2). -/
def wGamma (M : Params d) (W : Ω → ℝ → Fin d → ℝ) (t : ℝ) (ω : Ω) : ℝ := M.gamma ⬝ᵥ W ω t

/-- `W^η_t = Σ_j η_j W^j_t` (p. 2). -/
def wEta (M : Params d) (W : Ω → ℝ → Fin d → ℝ) (t : ℝ) (ω : Ω) : ℝ := M.eta ⬝ᵥ W ω t

/-- The GBM `Z_t = z + ∫_0^t µ_Z Z_s ds + ∫_0^t σ_Z Z_s dW^η_s` of (1.3), in closed form
`z exp((µ_Z − σ_Z²/2)t + σ_Z W^η_t)`. -/
noncomputable def benchZ (M : Params d) (W : Ω → ℝ → Fin d → ℝ) (z t : ℝ) (ω : Ω) : ℝ :=
  z * Real.exp ((M.muZ - M.sigmaZ ^ 2 / 2) * t + M.sigmaZ * wEta M W t ω)

/-- `m_t − m_0` for the running maximum `m_t = max{m, sup_{s≤t} B_s}` of
`B_t = b + µ_B t + σ_B W^γ_t` (1.3), written through `h = I_0 = m ∨ b − b`:
`m_t − m_0 = (sup_{s≤t}(µ_B s + σ_B W^γ_s) − h)⁺`, the Skorokhod regulator of `h − µ_B s − σ_B W^γ_s`. -/
noncomputable def runMaxInc (M : Params d) (W : Ω → ℝ → Fin d → ℝ) (h t : ℝ) (ω : Ω) : ℝ :=
  RankBasedSDI.LoadBalancing.skorokhodReg (fun s => h - M.muB * s - M.sigmaB * wGamma M W s ω) t

/-- `I_t = h + ∫_0^t dm_s − ∫_0^t µ_B ds − ∫_0^t σ_B dW^γ_s`, (2.4), with `I_0 = h`. -/
noncomputable def stateI (M : Params d) (W : Ω → ℝ → Fin d → ℝ) (h t : ℝ) (ω : Ω) : ℝ :=
  h - M.muB * t - M.sigmaB * wGamma M W t ω + runMaxInc M W h t ω

/-- The admissible class `𝕌^r` (p. 4): `θ` (`ℝ^d`-valued) and `c ≥ 0` are progressively
measurable, `∫_0^T (|θ_s|² + c_s) ds < ∞` for every `T` and every `ω`, and `J j` is (a version
with continuous paths of) the Itô integral `∫_0^t (σᵀθ_s)_j dW^j_s`, so that the wealth equation
(1.2) is well defined on every `[0, T]`. -/
def IsAdmissible (M : Params d) (Pr : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (W : Ω → ℝ → Fin d → ℝ) (θ : ℝ≥0 → Ω → (Fin d → ℝ)) (c : ℝ≥0 → Ω → ℝ)
    (J : Fin d → ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive F θ ∧ IsStronglyProgressive F c ∧ (∀ t ω, 0 ≤ c t ω) ∧
  (∀ ω (T : ℝ), IntervalIntegrable (fun s : ℝ => θ s.toNNReal ω ⬝ᵥ θ s.toNNReal ω) volume 0 T) ∧
  (∀ ω (T : ℝ), IntervalIntegrable (fun s : ℝ => c s.toNNReal ω) volume 0 T) ∧
  (∀ j ω, Continuous fun t => J j t ω) ∧
  ∀ j, EthierKurtz.HasBrownianItoIntegral Pr (fun t => F t) (fun t ω => W ω t j)
    (fun t ω => (M.sigmaᵀ *ᵥ θ t ω) j) (J j)

/-- The free part of the auxiliary wealth (2.3), before reflection:
`x + ∫_0^t θ_sᵀµ ds + ∫_0^t θ_sᵀσ dW_s − ∫_0^t c_s ds − (Z_t − z) − (m_t − m_0)`, where
`Z_t − z = ∫_0^t µ_Z Z_s ds + ∫_0^t σ_Z Z_s dW^η_s` and `∫θᵀσ dW = Σ_j J j`. -/
noncomputable def freeWealth (M : Params d) (W : Ω → ℝ → Fin d → ℝ)
    (θ : ℝ≥0 → Ω → (Fin d → ℝ)) (c : ℝ≥0 → Ω → ℝ) (J : Fin d → ℝ≥0 → Ω → ℝ)
    (x h z t : ℝ) (ω : Ω) : ℝ :=
  x + (∫ s in (0 : ℝ)..t, θ s.toNNReal ω ⬝ᵥ M.mu) + (∑ j, J j t.toNNReal ω) -
    (∫ s in (0 : ℝ)..t, c s.toNNReal ω) - (benchZ M W z t ω - z) - runMaxInc M W h t ω

/-- `L^X_t = x ∨ sup_{s≤t} D_s − x` (2.2): the Skorokhod regulator of the free wealth, the
minimal nondecreasing process keeping `X ≥ 0`, with `L^X_0 = 0`. -/
noncomputable def regLX (M : Params d) (W : Ω → ℝ → Fin d → ℝ)
    (θ : ℝ≥0 → Ω → (Fin d → ℝ)) (c : ℝ≥0 → Ω → ℝ) (J : Fin d → ℝ≥0 → Ω → ℝ)
    (x h z t : ℝ) (ω : Ω) : ℝ :=
  RankBasedSDI.LoadBalancing.skorokhodReg (fun s => freeWealth M W θ c J x h z s ω) t

/-- The reflected auxiliary wealth `X_t = x − D_t + L^X_t` of (2.3), with `X_0 = x`. -/
noncomputable def wealth (M : Params d) (W : Ω → ℝ → Fin d → ℝ)
    (θ : ℝ≥0 → Ω → (Fin d → ℝ)) (c : ℝ≥0 → Ω → ℝ) (J : Fin d → ℝ≥0 → Ω → ℝ)
    (x h z t : ℝ) (ω : Ω) : ℝ :=
  freeWealth M W θ c J x h z t ω + regLX M W θ c J x h z t ω

/-- The utility part `E[∫_0^∞ e^{−ρt} c_t^p / p dt]` of the objective (2.5), as an extended real:
`(1/p)` times the `lintegral` of `e^{−ρt} c_t^p`, with `c^p` computed in `[0, ∞]` (so `0^p = ∞` for
`p < 0`, as in the paper). It lies in `[0, ∞]` for `p ∈ (0, 1)` and in `[−∞, 0]` for `p < 0`. -/
noncomputable def utilityTerm (M : Params d) (ρ : ℝ) (Pr : Measure Ω) (c : ℝ≥0 → Ω → ℝ) :
    EReal :=
  ((1 / M.p : ℝ) : EReal) *
    (((∫⁻ ω, (∫⁻ t in Ici (0 : ℝ),
      ENNReal.ofReal (Real.exp (-ρ * t)) * ENNReal.ofReal (c t.toNNReal ω) ^ M.p) ∂Pr) :
        ℝ≥0∞) : EReal)

/-- The capital-injection part `E[∫_0^∞ e^{−ρt} dL^X_t] ∈ [0, ∞]` of the objective (2.5), for the
state `(X, I, Z)` started at `(x, h, z)`. -/
noncomputable def costTerm (M : Params d) (ρ : ℝ) (Pr : Measure Ω) (W : Ω → ℝ → Fin d → ℝ)
    (θ : ℝ≥0 → Ω → (Fin d → ℝ)) (c : ℝ≥0 → Ω → ℝ) (J : Fin d → ℝ≥0 → Ω → ℝ)
    (x h z : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, stieltjesLIntegral (fun t => regLX M W θ c J x h z t ω)
    (fun t => ENNReal.ofReal (Real.exp (-ρ * t))) ∂Pr

/-- The feedback investment `θ*(x,h,z) := −(σσᵀ)⁻¹(µu_x − σ_Bσγu_xh + σ_Zσηz(u_xx − u_xz))/u_xx`
of (4.3), for a function `u` on `ℝ³₊` (partial derivatives within `[0, ∞)`). -/
noncomputable def thetaStar (M : Params d) (u : ℝ → ℝ → ℝ → ℝ) (x h z : ℝ) : Fin d → ℝ :=
  let S : Set ℝ := Ici 0
  let ux := pd3₁ u S x h z
  let uxx := pd3₁ (pd3₁ u S) S x h z
  let uxh := pd3₂ (pd3₁ u S) S x h z
  let uxz := pd3₃ (pd3₁ u S) S x h z
  (-(1 / uxx)) • (M.covInv *ᵥ (ux • M.mu - (M.sigmaB * uxh) • (M.sigma *ᵥ M.gamma) +
    (M.sigmaZ * z * (uxx - uxz)) • (M.sigma *ᵥ M.eta)))

/-- The feedback consumption `c*(x, h, z) := u_x^{1/(p−1)}` of (4.3). -/
noncomputable def cStar (M : Params d) (u : ℝ → ℝ → ℝ → ℝ) (x h z : ℝ) : ℝ :=
  pd3₁ u (Ici 0) x h z ^ (1 / (M.p - 1))

/-- The feedback investment process `θ*_t = θ*(X*_t, I_t, Z_t)` along a state process `X*`
started at `(h, z)` in the `I` and `Z` coordinates, p. 19. -/
noncomputable def thetaProc (M : Params d) (W : Ω → ℝ → Fin d → ℝ) (u : ℝ → ℝ → ℝ → ℝ)
    (h z : ℝ) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → (Fin d → ℝ) :=
  fun t ω => thetaStar M u (X t ω) (stateI M W h t ω) (benchZ M W z t ω)

/-- The feedback consumption process `c*_t = c*(X*_t, I_t, Z_t)`, p. 19. -/
noncomputable def cProc (M : Params d) (W : Ω → ℝ → Fin d → ℝ) (u : ℝ → ℝ → ℝ → ℝ)
    (h z : ℝ) (X : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => cStar M u (X t ω) (stateI M W h t ω) (benchZ M W z t ω)

/-- `(X*, J)` is a solution of the controlled reflected system (4.4) started at `(x, h, z)` on the
basis `(Ω, F, 𝔽, P, W)`: `X*` is adapted with continuous paths; the feedback strategy
`θ*_t = θ*(X*_t, I_t, Z_t)`, `c*_t = c*(X*_t, I_t, Z_t)` is in `𝕌^r` with Itô integrals `J`; and
`X*` is the reflected wealth (2.3) of that strategy (so `X* = x − D + L^{X*}`, `L^{X*}_0 = 0`),
with `I` of (2.4) and `Z` of (1.3). -/
def IsFeedbackSolution (M : Params d) (Pr : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (W : Ω → ℝ → Fin d → ℝ) (u : ℝ → ℝ → ℝ → ℝ) (x h z : ℝ) (X : ℝ≥0 → Ω → ℝ)
    (J : Fin d → ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t, Measurable[F t] (X t)) ∧ (∀ ω, Continuous fun t => X t ω) ∧
  IsAdmissible M Pr F W (thetaProc M W u h z X) (cProc M W u h z X) J ∧
  ∀ t ω, X t ω = wealth M W (thetaProc M W u h z X) (cProc M W u h z X) J x h z t ω

end BenchmarkTracking.Verification


