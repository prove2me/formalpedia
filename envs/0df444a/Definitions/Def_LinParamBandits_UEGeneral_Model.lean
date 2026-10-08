-- Prove2me | Definitions.Def_LinParamBandits_UEGeneral_Model
-- name    : LinParamBandits_UEGeneral_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:18.133086+00:00
-- url     : https://prove2.me/theorems/18fe1507-8cda-4618-9653-efa2d9a42371
-- title:
--   Sec. 1.1 and Assumption 1 — compact arm set 𝒰_r ⊂ ℝ^r, rewards u′z + W, sub-Gaussian noise, history law, regret and Bayes risk
-- statement:
--   This file fixes the model of Rusmevichientong and Tsitsiklis, *Linearly Parameterized Bandits* (Section 1.1 and Assumption 1).
--
--   **Arms and rewards.** Let $r \ge 2$ and let $\mathcal U_r \subset \mathbb R^r$ be a compact set of arms, with the Euclidean norm $\|v\| = \sqrt{v'v}$. Playing arm $u$ in period $t$ yields the reward
--   $$X^u_t = u'Z + W^u_t,$$
--   where $Z \in \mathbb R^r$ is an unknown parameter and the noises $W^u_t$ are independent of each other and of $Z$, identically distributed in $t$ for each arm, with mean zero.
--
--   **Policies and the law of the history.** A history of $t$ periods is $H_t = (U_1, X_1, \dots, U_t, X_t)$. A policy $\psi$ consists of measurable maps $\psi_{t+1} : H_t \mapsto U_{t+1}$. Given $Z = z$, the law of $H_t$ is built period by period: the policy chooses $U_{n+1}$ from the past, a fresh noise $W$ with law $\nu(U_{n+1})$ is drawn independently of the past, and $X_{n+1} = U_{n+1}'z + W$ is observed.
--
--   **Assumption 1.** For constants $\sigma_0, \bar u, \lambda_0 > 0$:
--
--   1. (a) $\mathbb E[e^{xW^u_t}] \le e^{x^2\sigma_0^2/2}$ for every arm $u$ and every $x \in \mathbb R$;
--   2. (b) $\max_{u \in \mathcal U_r}\|u\| \le \bar u$, and $\mathcal U_r$ contains $r$ linearly independent arms $b_1, \dots, b_r$ with $\lambda_{\min}\big(\sum_{k=1}^r b_k b_k'\big) \ge \lambda_0$.
--
--   **Regret and risk.** With $Q_t(z) = \max_{v \in \mathcal U_r} v'z - U_t'z$ the instantaneous regret,
--   $$\mathrm{Regret}(z, T, \psi) = \sum_{t=1}^T \mathbb E\Big[\max_{v \in \mathcal U_r} v'z - U_t'z \,\Big|\, Z = z\Big], \qquad \mathrm{Risk}(T, \psi) = \mathbb E\big[\mathrm{Regret}(Z, T, \psi)\big],$$
--   the last expectation being over the prior of $Z$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^r$ is `EuclideanSpace ℝ (Fin r)`, so `inner` is $u'z$; $\bar u$ and $\lambda_0$ are written `ubar` and `lam0`. Periods are 0-based: `ψ.act t h` is $U_{t+1}$ chosen from the history `h` of $t$ periods. The paper's field of noises $W^u_t$ is encoded by the law of the noise given the arm, a Markov kernel $\nu$; since only $W^{U_t}_t$ is observed and $U_t$ depends on the past only, the history `histMeasure ν z ψ t` has the law of the paper's history given $Z = z$ (fresh independent noise each period, the same law $\nu(u)$ in every period). Measurability of $u \mapsto \nu(u)$ and of each $\psi_t$ is implicit in the paper. The moment generating function bound is written with a lower Lebesgue integral, so it also asserts finiteness. $\lambda_{\min}(\sum_k b_kb_k') \ge \lambda_0$ is written as $x'(\sum_k b_kb_k')x \ge \lambda_0\|x\|^2$ for all $x$. The regret is $T\max_{v} v'z - \mathbb E[\sum_t U_t'z \mid Z = z]$; the integrand is bounded on the support of the history law, so it is integrable. The maximum is `sSup`, attained for compact nonempty $\mathcal U_r$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Sec. 1.1, pp. 3–4 (model, eq. (1), Regret, Risk); Assumption 1, p. 13; eq. (9), p. 35

import Mathlib
import Definitions.Def_LinParamBandits_LowerBound_Model

namespace LinParamBandits.UEGeneral

open MeasureTheory ProbabilityTheory

/-- A deterministic, history-dependent policy (p. 3: `ψ_t : H_{t-1} → 𝒰_r`): `act t h` is the arm
`U_{t+1}` chosen in period `t + 1` from the history `h` of the first `t` periods. Each selection
map is measurable, which the paper's expectations use implicitly. -/
structure Policy (r : ℕ) where
  /-- `act t h` is the arm chosen in period `t + 1` after the history `h` of `t` periods. -/
  act : (t : ℕ) → LinParamBandits.LowerBound.History r t → LinParamBandits.LowerBound.Vec r
  /-- Each selection rule is measurable. -/
  measurable_act : ∀ t, Measurable (act t)

variable {r : ℕ}

/-- The law of the history `(U_1, X_1, …, U_t, X_t)` given `Z = z` (eq. (1), p. 3).
`ν u` is the law of the noise `W^u_t` of arm `u` (the same for every period `t`). In period
`n + 1` the policy plays `U_{n+1} = ψ.act n h`, a fresh noise `W ~ ν U_{n+1}` is drawn
independently of the past, and the reward `X_{n+1} = U_{n+1}′ z + W` is appended. -/
noncomputable def histMeasure (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (z : LinParamBandits.LowerBound.Vec r) (ψ : Policy r) :
    (t : ℕ) → Measure (LinParamBandits.LowerBound.History r t)
  | 0 => Measure.dirac (Fin.elim0 : LinParamBandits.LowerBound.History r 0)
  | n + 1 =>
      ((histMeasure ν z ψ n) ⊗ₘ (ν.comap (ψ.act n) (ψ.measurable_act n))).map
        (fun p => Fin.snoc (α := fun _ => LinParamBandits.LowerBound.Vec r × ℝ) p.1
          (ψ.act n p.1, inner ℝ (ψ.act n p.1) z + p.2))

/-- Standing assumptions of Sec. 1.1 (p. 3) and Assumption 1 (p. 13) on the arm set `𝒰`, the
noise laws `ν`, and the arms `b_1, …, b_r` of Assumption 1(b), with constants `σ₀, ū = ubar, λ₀ = lam0`. -/
structure Assumption1 (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r)
    (σ₀ ubar lam0 : ℝ) : Prop where
  /-- `σ₀ > 0`. -/
  σ₀_pos : 0 < σ₀
  /-- `ū > 0`. -/
  ubar_pos : 0 < ubar
  /-- `λ₀ > 0`. -/
  lam0_pos : 0 < lam0
  /-- Sec. 1.1: the noise of every arm has mean zero, `E[W^u_t] = 0`. -/
  mean_zero : ∀ u ∈ 𝒰, ∫ w, w ∂(ν u) = 0
  /-- Assumption 1(a): `E[e^{x W^u_t}] ≤ e^{x² σ₀² / 2}` for every arm `u` and `x ∈ ℝ`
  (the expectation is a lower Lebesgue integral, so it is finite whenever the bound holds). -/
  mgf_le : ∀ u ∈ 𝒰, ∀ x : ℝ,
    ∫⁻ w, ENNReal.ofReal (Real.exp (x * w)) ∂(ν u) ≤ ENNReal.ofReal (Real.exp (x ^ 2 * σ₀ ^ 2 / 2))
  /-- Assumption 1(b): `max_{u ∈ 𝒰_r} ‖u‖ ≤ ū`. -/
  norm_le : ∀ u ∈ 𝒰, ‖u‖ ≤ ubar
  /-- Assumption 1(b): the arms `b_1, …, b_r` belong to `𝒰_r`. -/
  b_mem : ∀ k, b k ∈ 𝒰
  /-- Assumption 1(b): `b_1, …, b_r` are linearly independent. -/
  b_linearIndependent : LinearIndependent ℝ b
  /-- Assumption 1(b): `λ_min(∑_k b_k b_k′) ≥ λ₀`, i.e. `x′(∑_k b_k b_k′)x ≥ λ₀ ‖x‖²` for all `x`. -/
  b_minEig : ∀ x : LinParamBandits.LowerBound.Vec r, lam0 * ‖x‖ ^ 2 ≤ ∑ k, (inner ℝ (b k) x) ^ 2

/-- The best expected reward `max_{v ∈ 𝒰_r} v′z` (p. 3); for compact nonempty `𝒰` the supremum is
attained. -/
noncomputable def bestValue (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (z : LinParamBandits.LowerBound.Vec r) : ℝ :=
  sSup ((fun v => inner ℝ v z) '' 𝒰)

/-- The instantaneous regret of arm `u` given `Z = z`: `max_{v ∈ 𝒰_r} v′z − u′z`
(`Q_t(z)` of eq. (9), p. 35, with `u = U_t`). -/
noncomputable def instRegret (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (z u : LinParamBandits.LowerBound.Vec r) : ℝ :=
  bestValue 𝒰 z - inner ℝ u z

/-- The `T`-period cumulative regret given `Z = z` (p. 3):
`Regret(z, T, ψ) = ∑_{t=1}^T E[max_{v ∈ 𝒰_r} v′z − U_t′z | Z = z]
  = T · max_{v ∈ 𝒰_r} v′z − E[∑_{t=1}^T U_t′z | Z = z]`. -/
noncomputable def regret (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ψ : Policy r) (z : LinParamBandits.LowerBound.Vec r)
    (T : ℕ) : ℝ :=
  T * bestValue 𝒰 z - ∫ h, ∑ s, inner ℝ (h s).1 z ∂(histMeasure ν z ψ T)

/-- The `T`-period cumulative Bayes risk (p. 4): `Risk(T, ψ) = E[Regret(Z, T, ψ)]`, `Z ~ μ`. -/
noncomputable def risk (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ψ : Policy r)
    (μ : Measure (LinParamBandits.LowerBound.Vec r)) (T : ℕ) : ℝ :=
  ∫ z, regret ν 𝒰 ψ z T ∂μ

end LinParamBandits.UEGeneral


