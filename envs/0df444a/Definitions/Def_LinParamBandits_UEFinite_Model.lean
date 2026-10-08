-- Prove2me | Definitions.Def_LinParamBandits_UEFinite_Model
-- name    : LinParamBandits_UEFinite_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:54.972328+00:00
-- url     : https://prove2.me/theorems/ec774d7f-3e4c-42b2-9f76-70c394799625
-- title:
--   Sec. 1.1 and Assumption 1 — arms 𝒰_r ⊂ ℝ^r, rewards u′z + W, sub-Gaussian noise, history law, regret, Bayes risk, gaps and pull counts
-- statement:
--   This file fixes the model of Rusmevichientong and Tsitsiklis, *Linearly Parameterized Bandits* (Sec. 1.1 and Assumption 1), as used in Section 4 and Appendix B.
--
--   **Arms and rewards.** Let $r \ge 2$ and let $\mathcal U_r \subset \mathbb R^r$ be the set of arms. An unknown parameter $Z \in \mathbb R^r$ governs the rewards: playing arm $u$ in period $t$ yields
--   $$X^u_t = u'Z + W^u_t ,$$
--   where the noise variables $W^u_t$ are independent of each other and of $Z$, identically distributed in $t$ for each arm, and have mean zero.
--
--   **Histories and policies.** A history of $t$ periods is the list $H_t = (U_1, X_1, \dots, U_t, X_t)$ of arms played and rewards observed. A policy $\psi$ is a sequence of maps $\psi_{t+1} : H_t \mapsto U_{t+1}$ choosing the next arm from the past; policies are deterministic and history dependent.
--
--   **Law of the history given $Z = z$.** Write $\nu_u$ for the law of the noise of arm $u$. Given $Z = z$, the history is generated period by period: $U_{t+1} = \psi_{t+1}(H_t)$, then $X_{t+1} = U_{t+1}'z + W_{t+1}$ with $W_{t+1}$ drawn from $\nu_{U_{t+1}}$ independently of the past. This defines the law $\mathbb P_{z,\psi}$ of $H_T$ for every $T$.
--
--   **Regret, risk, gaps, pull counts.** The best expected reward is $\max_{v \in \mathcal U_r} v'z$. The $T$-period regret given $Z = z$ and the Bayes risk under a prior $\mu$ of $Z$ are
--   $$\mathrm{Regret}(z, T, \psi) = \sum_{t=1}^T \mathbb E\Big[\max_{v \in \mathcal U_r} v'z - U_t'z \,\Big|\, Z = z\Big], \qquad \mathrm{Risk}(T, \psi) = \mathbb E_{Z \sim \mu}\big[\mathrm{Regret}(Z, T, \psi)\big].$$
--   The gap of arm $u$ is $\Delta^u(z) = \max_{v \in \mathcal U_r} v'z - u'z$, and $N^u(z, T)$ is the number of periods $s \le T$ with $U_s = u$.
--
--   **Density condition (Theorem 4.2).** For a prior $\mu$, a constant $M_0$ and an arm $u$: the law of $\Delta^u(Z)$ consists of a point mass at $0$ and a density bounded above by $M_0$ on $\mathbb R_+$.
--
--   **Assumption 1.** (a) There is $\sigma_0 > 0$ with $\mathbb E[e^{xW^u_t}] \le e^{x^2\sigma_0^2/2}$ for every arm $u$ and every $x \in \mathbb R$. (b) There are $\bar u, \lambda_0 > 0$ with $\|u\| \le \bar u$ for every arm, and $\mathcal U_r$ contains $r$ linearly independent arms $b_1, \dots, b_r$ with $\lambda_{\min}\big(\sum_{k=1}^r b_kb_k'\big) \ge \lambda_0$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^r$ is `EuclideanSpace ℝ (Fin r)` (`Vec r`), so $\|\cdot\|$ is Euclidean and `inner ℝ u z` is $u'z$. Periods are indexed from $0$: `ψ.act t h`, with `h` a history of `t` periods, is $U_{t+1}$. The noise is a Markov kernel `ν` from arms to $\mathbb R$; the history law `histMeasure ν z ψ t` is built recursively with `Measure.compProd`, which is exactly the law of the paper's history (fresh noise each period, independent of the past and of $Z$, the same law in every period for a given arm). The measurability of $u \mapsto \nu_u$ and of each $\psi_t$ is implicit in the paper and is built into the types. Regret is written $T \max_v v'z - \mathbb E[\sum_t U_t'z]$; the max over a finite nonempty arm set is the real `sSup` of a finite set, which is attained. The mgf bound of Assumption 1(a) is a lower Lebesgue integral, so it also asserts that $\mathbb E[e^{xW}]$ is finite. $\lambda_{\min}(\sum_k b_kb_k') \ge \lambda_0$ is written as $\lambda_0\|x\|^2 \le \sum_k (b_k'x)^2$ for every $x$, the same condition. The density condition is written as: the law of $\Delta^u(Z)$ restricted to $(0,\infty)$ is at most $M_0$ times Lebesgue measure, which is equivalent because $\Delta^u \ge 0$. $\lambda_0$ is spelled `lam₀` in Lean (`λ` is a keyword).
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Sec. 1.1, pp. 3–4 (model, eq. (1), Regret, Risk); Assumption 1, p. 13; Δ^u(z), p. 21; N^u(z, T) and the density condition, Theorem 4.2 and its proof, pp. 21–22

import Mathlib
import Definitions.Def_LinParamBandits_LowerBound_Model
import Definitions.Def_LinParamBandits_UEGeneral_Model

namespace LinParamBandits.UEFinite

open MeasureTheory ProbabilityTheory

variable {r : ℕ}

/-- The gap `Δ^u(z) = max_{v ∈ 𝒰_r} v′z − u′z` of arm `u` (p. 21). -/
noncomputable def gap (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (u z : LinParamBandits.LowerBound.Vec r) : ℝ :=
  LinParamBandits.UEGeneral.bestValue 𝒰 z - inner ℝ u z

/-- `N^u(z, t)` as a function of the history: the number of periods among the first `t` in which
arm `u` was played (p. 22, p. 29). -/
noncomputable def pullCount (u : LinParamBandits.LowerBound.Vec r) {t : ℕ} (h : LinParamBandits.LowerBound.History r t) : ℕ :=
  open Classical in (Finset.univ.filter (fun s : Fin t => (h s).1 = u)).card

/-- The `T`-period regret given `Z = z` (p. 3):
`Regret(z, T, ψ) = ∑_{t=1}^T E[max_{v ∈ 𝒰_r} v′z − U_t′z | Z = z]
= T · max_{v ∈ 𝒰_r} v′z − E[∑_{t=1}^T U_t′z | Z = z]`. -/
noncomputable def Regret (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (ψ : LinParamBandits.UEGeneral.Policy r) (z : LinParamBandits.LowerBound.Vec r)
    (T : ℕ) : ℝ :=
  T * LinParamBandits.UEGeneral.bestValue 𝒰 z - ∫ h, ∑ s, inner ℝ (h s).1 z ∂(LinParamBandits.UEGeneral.histMeasure ν z ψ T)

/-- The `T`-period Bayes risk (p. 4): `Risk(T, ψ) = E[Regret(Z, T, ψ)]`, the expectation being
over the prior `μ` of `Z`. -/
noncomputable def Risk (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (ψ : LinParamBandits.UEGeneral.Policy r) (μ : Measure (LinParamBandits.LowerBound.Vec r))
    (T : ℕ) : ℝ :=
  ∫ z, Regret 𝒰 ν ψ z T ∂μ

/-- The density condition of Theorem 4.2 (pp. 21–22) for one arm `u`: the law of `Δ^u(Z)`, `Z ∼ μ`,
consists of a point mass at `0` and a density bounded above by `M₀` on `ℝ₊`. Since `Δ^u ≥ 0`, this
says exactly that on `(0, ∞)` the law of `Δ^u(Z)` is at most `M₀` times Lebesgue measure. -/
def GapDensityLe (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (μ : Measure (LinParamBandits.LowerBound.Vec r)) (M₀ : ℝ) (u : LinParamBandits.LowerBound.Vec r) : Prop :=
  (μ.map (fun z => gap 𝒰 u z)).restrict (Set.Ioi 0) ≤
    ENNReal.ofReal M₀ • (volume.restrict (Set.Ioi (0 : ℝ)))

/-- Assumption 1(a) (p. 13) together with the mean-zero condition of Sec. 1.1 (p. 3): for every
arm `u ∈ 𝒰_r` the noise law `ν u` has mean zero and moment generating function bounded by
`exp(x²σ₀²/2)`. The bound is stated with a lower Lebesgue integral, so it also asserts that
`E[e^{xW}]` is finite. -/
def NoiseAssumption (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (σ₀ : ℝ) : Prop :=
  ∀ u ∈ 𝒰, (∫ w, w ∂(ν u) = 0) ∧
    ∀ x : ℝ, ∫⁻ w, ENNReal.ofReal (Real.exp (x * w)) ∂(ν u) ≤
      ENNReal.ofReal (Real.exp (x ^ 2 * σ₀ ^ 2 / 2))

/-- Assumption 1(b) (p. 13): every arm has norm at most `ū`, and `𝒰_r` contains `r` linearly
independent arms `b_1, …, b_r` with `λ_min(∑_k b_k b_k′) ≥ λ₀`, written as
`λ₀‖x‖² ≤ ∑_k (b_k′x)² = x′(∑_k b_k b_k′)x` for all `x`. -/
def ArmAssumption (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (b : Fin r → LinParamBandits.LowerBound.Vec r) (ū lam₀ : ℝ) : Prop :=
  (∀ u ∈ 𝒰, ‖u‖ ≤ ū) ∧ (∀ k, b k ∈ 𝒰) ∧ LinearIndependent ℝ b ∧
    ∀ x : LinParamBandits.LowerBound.Vec r, lam₀ * ‖x‖ ^ 2 ≤ ∑ k, (inner ℝ (b k) x) ^ 2

end LinParamBandits.UEFinite


