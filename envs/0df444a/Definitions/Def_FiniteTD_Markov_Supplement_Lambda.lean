-- Prove2me | Definitions.Def_FiniteTD_Markov_Supplement_Lambda
-- name    : FiniteTD_Markov_Supplement_Lambda
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:39:04.701088+00:00
-- url     : https://prove2.me/theorems/9c769421-1f6a-43b2-a386-01293cd0ac75
-- title:
--   §9, App. B, pp. 23–25, 38–39, 48 — Π_D, T^{(λ)} (28), x̄ (39), traces, projected TD(λ), ζ (40), κ, τmix_λ (30)
-- statement:
--   This file defines the objects of TD(λ) (§9 and Appendix B) on the finite Markov reward process of the published mission. Write $V_\theta(s)=\phi(s)^\top\theta$, $D=\mathrm{diag}(\pi)$, and $q=\gamma\lambda$.
--
--   1. **Steady-state seminorm of a value function** $V : S\to\mathbb R$: $\|V\|_D = \big(\sum_s\pi(s)V(s)^2\big)^{1/2}$.
--   2. **Weighted projection.** $\Sigma = \Phi^\top D\Phi = \sum_s\pi(s)\phi(s)\phi(s)^\top$ and $\Pi_D V = \Phi\,\Sigma^{-1}\Phi^\top D V$, the $\langle\cdot,\cdot\rangle_D$-orthogonal projection onto the span of the features when $\Sigma$ has full rank.
--   3. **Expected update of an operator** $H$ on value functions: $\bar g_H(\theta) = \Phi^\top D(H\Phi\theta-\Phi\theta)$ (Lemma 21).
--   4. **Averaged Bellman operator** (28), in resolvent form:
--   $$T^{(\lambda)}V = V + \sum_{k\ge0}(\gamma\lambda)^kP^k\big(r+\gamma PV-V\big),\qquad (r+\gamma PV-V)(s)=\sum_{s'}P(s,s')\big(R(s,s')+\gamma V(s')-V(s)\big).$$
--   5. **Stationary mean update** (39): $\bar x(\theta)=\Phi^\top D\big(T^{(\lambda)}\Phi\theta-\Phi\theta\big)$.
--   6. **TD error** of a transition: $\delta(\theta;s,s')=R(s,s')+\gamma\phi(s')^\top\theta-\phi(s)^\top\theta$.
--   7. **Eligibility traces.** Along a path $s_0,s_1,\dots$, $z_{0:t}=\sum_{k=0}^{t}q^k\phi(s_{t-k})$ (Algorithm 2 with $z_{-1}=0$). On a two-sided path $(\dots,s_{-1},s_0,s_1,\dots)$, $z_{l:t}=\sum_{k=0}^{t-l}q^k\phi(s_{t-k})$ for integers $l\le t$, and $z_{-\infty:t}=\sum_{k\ge0}q^k\phi(s_{t-k})$.
--   8. **Projected TD(λ)** (Algorithm 2): from $\theta_0$, $\theta_{t+1}=\Pi_{2,R}\big(\theta_t+\alpha_t\,\delta_t(\theta_t)\,z_{0:t}\big)$, where $\delta_t$ is the TD error of the transition $(s_t,s_{t+1})$ and $\Pi_{2,R}$ is the projection onto the ball of radius $R$ of the published mission.
--   9. **Update error** (40): $\zeta(\theta,z;s,s')=\big(\delta(\theta;s,s')\,z-\bar x(\theta)\big)^\top(\theta-\theta^*)$, so that $\zeta_t(\theta,z_{l:t})=\zeta(\theta,z_{l:t};s_t,s_{t+1})$.
--   10. **Constants.** $\kappa=\gamma(1-\lambda)/(1-\gamma\lambda)$ (Lemma 12); $\tau^{\mathrm{Algo}}(\epsilon)=\min\{t\in\mathbb N_0: q^t\le\epsilon\}$; and the mixing time (30) $\tau^{\mathrm{mix}}_\lambda(\epsilon)=\max\{\tau^{\mathrm{MC}}(\epsilon),\tau^{\mathrm{Algo}}(\epsilon)\}$, with $\tau^{\mathrm{MC}}=\tau_{\mathrm{mix}}$ of (21).
--
--   These are the objects in which Theorem 4 and Lemmas 16–21 are stated.
--
--   **Formalization Note** For $\lambda<1$ the resolvent form of $T^{(\lambda)}$ equals the sum in (28), after rearranging convergent geometric sums. At $\lambda=1$, which §9 and Algorithm 2 allow, (28) reads $0$ times a divergent series; the resolvent form is its limit and gives $T^{(1)}V=V_\mu$, in agreement with (38)–(39). The series converge because $0\le\gamma\lambda<1$ on the standing range and $P$ is stochastic. $\Pi_D$ uses the inverse of $\Sigma$, which exists under the standing full-rank assumption $\omega>0$; every statement that uses $\Pi_D$ assumes it. $\tau^{\mathrm{Algo}}$ keeps $q^0=1$, so for $q=0$ and $\epsilon>0$ it is $0$ if $\epsilon\ge1$ and $1$ otherwise; it is only evaluated at positive $\epsilon$.
-- source:
--   Bhandari, Russo & Singal, A Finite Time Analysis of Temporal Difference Learning With Linear Function Approximation, arXiv:1806.02450v2, p. 23 (Algorithm 2), p. 24 ((28), Lemma 12, κ), p. 25 ((30)), pp. 38–39 ((38), (39), (40), B, Θ_R), p. 48 (Lemma 21, ḡ)

import Mathlib
import Definitions.Def_FiniteTD_Markov_Chain
import Definitions.Def_FiniteTD_Markov_Setting

namespace FiniteTD.Markov.Supplement

open scoped InnerProductSpace
open Matrix

variable {S : Type} [Fintype S] {d : ℕ}

/-- The linear value function `V_θ = Φθ`, `V_θ(s) = φ(s)⊤θ`. -/
noncomputable def valFn (φ : S → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) : S → ℝ :=
  fun s => ⟪φ s, θ⟫_ℝ

/-- The steady-state seminorm of a value function: `‖V‖_D = (Σ_s π(s) V(s)²)^{1/2}`. -/
noncomputable def dNormV (π : S → ℝ) (v : S → ℝ) : ℝ :=
  Real.sqrt (∑ s, π s * v s ^ 2)

/-- The feature covariance matrix `Σ = Φ⊤DΦ = Σ_s π(s) φ(s) φ(s)⊤`. -/
noncomputable def gram (π : S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => ∑ s, π s * φ s i * φ s j

/-- Coefficients `Σ⁻¹Φ⊤Dv` of the `D`-weighted least-squares fit of `v` by the features. -/
noncomputable def projCoef (π : S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (v : S → ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 ((gram π φ)⁻¹ *ᵥ fun i => ∑ s, π s * v s * φ s i)

/-- `Π_D v = Φ(Φ⊤DΦ)⁻¹Φ⊤Dv`, the projection onto `span Φ` orthogonal for `⟨·,·⟩_D` (full-rank `Σ`). -/
noncomputable def projD (π : S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (v : S → ℝ) : S → ℝ :=
  valFn φ (projCoef π φ v)

/-- The expected update of an operator `H` on value functions: `ḡ_H(θ) = Φ⊤D(HΦθ − Φθ)`. -/
noncomputable def gbarH (π : S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (H : (S → ℝ) → (S → ℝ))
    (θ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  ∑ s, (π s * (H (valFn φ θ) s - valFn φ θ s)) • φ s

/-- The averaged Bellman operator `T_μ^{(λ)}` of (28), in its resolvent form
`T^{(λ)}V = V + Σ_{k≥0} (γλ)^k P^k (r + γPV − V)`, where `(r + γPV − V)(s) = Σ_{s'} P(s,s')(R(s,s') + γV(s') − V(s))`.
For `λ < 1` this is (28); at `λ = 1` it is the limit of (28), `T^{(1)}V = V_μ`. -/
noncomputable def Tlam [DecidableEq S] (P : S → S → ℝ) (γ lam : ℝ) (Rw : S → S → ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => v s + ∑' k : ℕ, (γ * lam) ^ k *
    ((Matrix.of P ^ k) *ᵥ fun u => ∑ u', P u u' * (Rw u u' + γ * v u' - v u)) s

/-- The steady-state TD(λ) mean update (39): `x̄(θ) = Φ⊤D(T^{(λ)}Φθ − Φθ)`. -/
noncomputable def xbar [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ) (γ lam : ℝ) (Rw : S → S → ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θ : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  gbarH π φ (Tlam P γ lam Rw) θ

/-- The TD error of a transition `(s, R(s, s'), s')`: `δ(θ) = R(s, s') + γφ(s')⊤θ − φ(s)⊤θ`. -/
noncomputable def tdErr (γ : ℝ) (Rw : S → S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) (s s' : S) : ℝ :=
  Rw s s' + γ * ⟪φ s', θ⟫_ℝ - ⟪φ s, θ⟫_ℝ

/-- The eligibility trace of Algorithm 2 along a path `w` (started with `z_{-1} = 0`):
`z_{0:t} = Σ_{k=0}^{t} q^k φ(s_{t-k})`, with `q = γλ`. -/
noncomputable def traceN (φ : S → EuclideanSpace ℝ (Fin d)) (q : ℝ) (w : ℕ → S) (t : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ k ∈ Finset.range (t + 1), q ^ k • φ (w (t - k))

/-- The trace window `z_{l:t} = Σ_{k=0}^{t-l} q^k φ(s_{t-k})` (`l ≤ t`) on a two-sided path `w : ℤ → S`. -/
noncomputable def traceWin (φ : S → EuclideanSpace ℝ (Fin d)) (q : ℝ) (w : ℤ → S) (l t : ℤ) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ k ∈ Finset.range ((t - l).toNat + 1), q ^ k • φ (w (t - k))

/-- The infinite-past trace `z_{-∞:t} = Σ_{k≥0} q^k φ(s_{t-k})` on a two-sided path `w : ℤ → S`. -/
noncomputable def traceInf (φ : S → EuclideanSpace ℝ (Fin d)) (q : ℝ) (w : ℤ → S) (t : ℤ) :
    EuclideanSpace ℝ (Fin d) :=
  ∑' k : ℕ, q ^ k • φ (w (t - k))

/-- Projected TD(λ) (Algorithm 2) along a path `w`: `θ₀` given and
`θ_{t+1} = Π_{2,R}(θ_t + α_t δ_t(θ_t) z_{0:t})`, with `δ_t` on the transition `(w t, w (t+1))`. -/
noncomputable def ptdLam (γ lam : ℝ) (Rw : S → S → ℝ) (φ : S → EuclideanSpace ℝ (Fin d)) (R : ℝ)
    (α : ℕ → ℝ) (θ0 : EuclideanSpace ℝ (Fin d)) (w : ℕ → S) : ℕ → EuclideanSpace ℝ (Fin d)
  | 0 => θ0
  | t + 1 =>
      projBall R (ptdLam γ lam Rw φ R α θ0 w t +
        α t • (tdErr γ Rw φ (ptdLam γ lam Rw φ R α θ0 w t) (w t) (w (t + 1)) • traceN φ (γ * lam) w t))

/-- The TD(λ) update error (40): `ζ(θ, z; s, s') = (δ(θ; s, s') z − x̄(θ))⊤(θ − θ*)`. -/
noncomputable def zetaLam [DecidableEq S] (π : S → ℝ) (P : S → S → ℝ) (γ lam : ℝ) (Rw : S → S → ℝ)
    (φ : S → EuclideanSpace ℝ (Fin d)) (θstar θ z : EuclideanSpace ℝ (Fin d)) (s s' : S) : ℝ :=
  ⟪tdErr γ Rw φ θ s s' • z - xbar π P γ lam Rw φ θ, θ - θstar⟫_ℝ

/-- The contraction modulus of `Π_D T^{(λ)}` (Lemma 12): `κ = γ(1 − λ)/(1 − γλ)`. -/
noncomputable def kappa (γ lam : ℝ) : ℝ :=
  γ * (1 - lam) / (1 - γ * lam)

/-- `τ^{Algo}(ε) = min {t ∈ ℕ₀ | q^t ≤ ε}`, with `q = γλ` (§9.3). -/
noncomputable def tauAlgo (q ε : ℝ) : ℕ :=
  sInf {t : ℕ | q ^ t ≤ ε}

/-- The TD(λ) mixing time (30): `τ^{mix}_λ(ε) = max {τ^{MC}(ε), τ^{Algo}(ε)}`, `τ^{MC} = τmix` of (21). -/
noncomputable def tauMixLam (m ρ q ε : ℝ) : ℕ :=
  max (tauMix m ρ ε) (tauAlgo q ε)

end FiniteTD.Markov.Supplement


