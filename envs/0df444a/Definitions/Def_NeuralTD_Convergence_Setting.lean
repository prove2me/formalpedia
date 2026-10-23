-- Prove2me | Definitions.Def_NeuralTD_Convergence_Setting
-- name    : NeuralTD_Convergence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:32.832156+00:00
-- url     : https://prove2.me/theorems/aa02a4eb-f254-4403-ab76-b6d8bb4725cd
-- title:
--   §2–§4, (3.2), Algorithm 1, (4.6)–(4.9), Assumption 4.3 — sampling law, two-layer ReLU network, its linearization, neural TD with projection and averaging, approximate stationary point
-- statement:
--   This file fixes every object of the neural temporal-difference (TD) analysis of Cai, Yang, Lee and Wang.
--
--   **Samples.** A transition is a tuple $\xi = (x, r, x')$ with $x, x' \in \mathbb{R}^d$ (feature vectors of the current and next state–action pair) and a reward $r \in \mathbb{R}$. A *sampling law* with reward bound $\bar r$ is a probability measure $\mu$ on such tuples with $\|x\|_2 = \|x'\|_2 = 1$ and $|r| \le \bar r$ almost surely, under which $x$ and $x'$ have the same distribution (stationarity of the policy's state–action distribution). **Assumption 4.3** with constant $c_0$ requires
--   $$\mu\big(|w^\top x| \le \tau\big) \le c_0\,\tau \qquad \text{for every unit } w \in \mathbb{R}^d \text{ and every } \tau \ge 0.$$
--
--   **Network.** For width $m$, output weights $b \in \mathbb{R}^m$ and hidden weights $W = (W_1,\dots,W_m) \in \mathbb{R}^{md}$ (with the Euclidean norm $\|W\|_2^2 = \sum_r \|W_r\|_2^2$),
--   $$\widehat Q(x; W) = \frac{1}{\sqrt m}\sum_{r=1}^m b_r\,\sigma(W_r^\top x), \qquad \sigma(y) = \max\{0, y\},$$
--   with semigradient $\nabla_{W_r}\widehat Q(x;W) = m^{-1/2} b_r \mathbb 1\{W_r^\top x > 0\}\,x$. The initialization draws $b_r \sim \mathrm{Unif}\{-1,1\}$ and $W_r(0) \sim N(0, I_d/d)$, all independent. The local linearization at $W(0)$ is
--   $$\widehat Q_0(x; W) = \frac{1}{\sqrt m}\sum_{r=1}^m b_r\,\mathbb 1\{W_r(0)^\top x > 0\}\,W_r^\top x,$$
--   and the Bellman residuals are $\delta(x,r,x';W) = \widehat Q(x;W) - r - \gamma \widehat Q(x';W)$ and $\delta_0(x,r,x';W) = \widehat Q_0(x;W) - r - \gamma\widehat Q_0(x';W)$.
--
--   **Algorithm 1 (neural TD).** With $S_B = \{W : \|W - W(0)\|_2 \le B\}$ and $\Pi_{S_B}$ the Euclidean projection onto it, the iterates are $W(0)$ and
--   $$W(t+1) = \Pi_{S_B}\big(W(t) - \eta\,\delta(x_t, r_t, x_t'; W(t))\,\nabla_W \widehat Q(x_t; W(t))\big),$$
--   where $(x_t, r_t, x'_t)$ is the tuple sampled at step $t$. The output after $T$ iterations is $\widehat Q_{\mathrm{out}} = \widehat Q(\cdot\,; \overline W)$ with $\overline W = \frac1T\sum_{t=0}^{T-1} W(t)$ and step size $\eta = \min\{(1-\gamma)/8,\, 1/\sqrt T\}$.
--
--   **Population semigradients and $W^*$.** $\bar g(W) = \mathbb E_\mu[\delta(x,r,x';W)\nabla_W\widehat Q(x;W)]$ and $\bar g_0(W) = \mathbb E_\mu[\delta_0(x,r,x';W)\nabla_W\widehat Q_0(x;W)]$. A point $W^*$ is an **approximate stationary point** (Definition 4.1) if $W^* \in S_B$ and
--   $$\bar g_0(W^*)^\top (W - W^*) \ge 0 \qquad \text{for every } W \in S_B.$$
--
--   These are the objects of every statement in the mission: the goal compares $\widehat Q_{\mathrm{out}}$ with $\widehat Q_0(\cdot\,;W^*)$.
--
--   **Formalization Note.** The MDP, the policy and the feature map are not modelled: statements see only the sampling law $\mu$ on tuples $(x, r, x')$. Points are `EuclideanSpace ℝ (Fin d)` and parameters are `PiLp 2` over `Fin m`, so every norm on $\mathbb R^{md}$ is the $\ell_2$ norm. The projection is written in closed form ($V$ if $\|V - W(0)\| \le B$, else $W(0) + \frac{B}{\|V - W(0)\|}(V - W(0))$). The iterates take the tuples as a sequence indexed by $\mathbb N$ (the tuple of step $t$ moves $W(t)$ to $W(t+1)$; only steps $0,\dots,T-2$ affect $\overline W$). The definition of an approximate stationary point includes $W^* \in S_B$, which the paper's proof uses ((C.12), (C.28)) but Definition 4.1's wording leaves implicit. $N(0, I_d/d)$ is Mathlib's `multivariateGaussian 0 ((1/d) • I)`.
-- source:
--   Cai, Yang, Lee, Wang, Neural temporal-difference and Q-learning provably converge to global optima, arXiv:1905.10027v2, pp. 5–10, §2.2, §3, (3.2), Algorithm 1 (p. 7), §4 p. 8, Definition 4.1 and (4.6)–(4.8) (p. 9), Assumption 4.3 and (4.9) (p. 10), (5.1)–(5.2) (p. 12)

import Mathlib

namespace NeuralTD.Convergence

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

/-- A point (feature vector) `x ∈ ℝᵈ`. -/
abbrev Pt (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The trained parameter `W = (W₁, …, W_m) ∈ ℝ^{md}` with the Euclidean norm
`‖W‖₂² = ∑_r ‖W_r‖₂²` (an `L²` product, not the sup norm). -/
abbrev Param (m d : ℕ) := PiLp 2 (fun _ : Fin m => Pt d)

/-- The random initialization `(b, W(0))`. -/
abbrev Init (m d : ℕ) := (Fin m → ℝ) × Param m d

/-- A sampled transition `(x, r, x′)`. -/
abbrev Sample (d : ℕ) := Pt d × ℝ × Pt d

/-- The law `Unif({−1, 1})` of an output weight `b_r`. -/
noncomputable def signLaw : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 1 + Measure.dirac (-1))

/-- The Gaussian law `N(0, I_d / d)` of a hidden weight `W_r(0)`. -/
noncomputable def gaussLaw (d : ℕ) : Measure (Pt d) :=
  multivariateGaussian 0 ((d : ℝ)⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ))

/-- The initialization law: `b_r ∼ Unif({−1, 1})` and `W_r(0) ∼ N(0, I_d / d)`, all independent. -/
noncomputable def initLaw (m d : ℕ) : Measure (Init m d) :=
  (Measure.pi fun _ : Fin m => signLaw).prod
    ((Measure.pi fun _ : Fin m => gaussLaw d).map (WithLp.toLp 2))

/-- Standing sampling assumptions (§2.2 and §3, p. 6): `μ` is a probability law of tuples
`(x, r, x′)` with `‖x‖₂ = ‖x′‖₂ = 1` and `|r| ≤ r̄` almost surely, and `x`, `x′` have the same
(stationary) marginal law. -/
structure IsSamplingLaw (d : ℕ) (rbar : ℝ) (μ : Measure (Sample d)) : Prop where
  isProb : IsProbabilityMeasure μ
  norm_x : ∀ᵐ ξ ∂μ, ‖ξ.1‖ = 1
  norm_x' : ∀ᵐ ξ ∂μ, ‖ξ.2.2‖ = 1
  reward_le : ∀ᵐ ξ ∂μ, |ξ.2.1| ≤ rbar
  same_marginal : μ.map (fun ξ => ξ.1) = μ.map (fun ξ => ξ.2.2)

/-- Assumption 4.3 (p. 10): `P(|wᵀx| ≤ τ) ≤ c₀ τ` for every unit `w` and every `τ ≥ 0`, `x ∼ μ`. -/
def Assumption43 {d : ℕ} (c0 : ℝ) (μ : Measure (Sample d)) : Prop :=
  ∀ w : Pt d, ‖w‖ = 1 → ∀ τ : ℝ, 0 ≤ τ → μ {ξ | |⟪w, ξ.1⟫| ≤ τ} ≤ ENNReal.ofReal (c0 * τ)

/-- The ReLU activation `σ(y) = max{0, y}`. -/
noncomputable def relu (y : ℝ) : ℝ := max 0 y

/-- The two-layer network (3.2): `Q̂(x; W) = m^{−1/2} ∑_r b_r σ(W_rᵀx)`. -/
noncomputable def Qhat {m d : ℕ} (b : Fin m → ℝ) (W : Param m d) (x : Pt d) : ℝ :=
  (Real.sqrt m)⁻¹ * ∑ r, b r * relu ⟪W r, x⟫

/-- The semigradient `∇_{W_r} Q̂(x; W) = m^{−1/2} b_r 1{W_rᵀx > 0} x`. -/
noncomputable def gradQ {m d : ℕ} (b : Fin m → ℝ) (W : Param m d) (x : Pt d) : Param m d :=
  WithLp.toLp 2 (fun r => ((Real.sqrt m)⁻¹ * b r * (if 0 < ⟪W r, x⟫ then 1 else 0)) • x)

/-- The local linearization (4.7): `Q̂₀(x; W) = m^{−1/2} ∑_r b_r 1{W_r(0)ᵀx > 0} W_rᵀx`. -/
noncomputable def Qlin {m d : ℕ} (b : Fin m → ℝ) (W0 W : Param m d) (x : Pt d) : ℝ :=
  (Real.sqrt m)⁻¹ * ∑ r, b r * (if 0 < ⟪W0 r, x⟫ then 1 else 0) * ⟪W r, x⟫

/-- The gradient `∇_W Q̂₀(x; W)` of (4.7), which does not depend on `W`. -/
noncomputable def gradQlin {m d : ℕ} (b : Fin m → ℝ) (W0 : Param m d) (x : Pt d) : Param m d :=
  WithLp.toLp 2 (fun r => ((Real.sqrt m)⁻¹ * b r * (if 0 < ⟪W0 r, x⟫ then 1 else 0)) • x)

/-- The Bellman residual `δ(x, r, x′; W) = Q̂(x; W) − r − γ Q̂(x′; W)`. -/
noncomputable def delta {m d : ℕ} (γ : ℝ) (b : Fin m → ℝ) (W : Param m d) (ξ : Sample d) : ℝ :=
  Qhat b W ξ.1 - ξ.2.1 - γ * Qhat b W ξ.2.2

/-- The linearized Bellman residual (4.8): `δ₀(x, r, x′; W) = Q̂₀(x; W) − r − γ Q̂₀(x′; W)`. -/
noncomputable def deltaLin {m d : ℕ} (γ : ℝ) (b : Fin m → ℝ) (W0 W : Param m d) (ξ : Sample d) :
    ℝ :=
  Qlin b W0 W ξ.1 - ξ.2.1 - γ * Qlin b W0 W ξ.2.2

/-- Euclidean projection onto the ball `S_B = {W : ‖W − W(0)‖₂ ≤ B}` (closed form). -/
noncomputable def projBall {m d : ℕ} (W0 : Param m d) (B : ℝ) (V : Param m d) : Param m d :=
  if ‖V - W0‖ ≤ B then V else W0 + (B / ‖V - W0‖) • (V - W0)

/-- The step size of Theorem 4.6: `η = min{(1 − γ)/8, 1/√T}`. -/
noncomputable def stepSize (γ : ℝ) (T : ℕ) : ℝ := min ((1 - γ) / 8) (1 / Real.sqrt T)

/-- Lines 5–7 of Algorithm 1: Bellman residual, semigradient step, projection onto `S_B`. -/
noncomputable def tdStep {m d : ℕ} (γ η B : ℝ) (b : Fin m → ℝ) (W0 W : Param m d)
    (ξ : Sample d) : Param m d :=
  projBall W0 B (W - (η * delta γ b W ξ) • gradQ b W ξ.1)

/-- The iterates `W(t)` of Algorithm 1 from the initialization `ι = (b, W(0))`; the tuple
sampled at step `t` is `ξs t`. -/
noncomputable def iterate {m d : ℕ} (γ η B : ℝ) (ι : Init m d) (ξs : ℕ → Sample d) :
    ℕ → Param m d
  | 0 => ι.2
  | t + 1 => tdStep γ η B ι.1 ι.2 (iterate γ η B ι ξs t) (ξs t)

/-- The running average of Line 8 after `T − 1` steps: `W̄ = (1/T) ∑_{t<T} W(t)`. -/
noncomputable def avgIterate {m d : ℕ} (γ η B : ℝ) (ι : Init m d) (ξs : ℕ → Sample d) (T : ℕ) :
    Param m d :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, iterate γ η B ι ξs t

/-- The output of Algorithm 1 (Line 10) with `T` iterations and step size `stepSize γ T`:
`Q̂_out(x) = Q̂(x; W̄)`. -/
noncomputable def Qout {m d : ℕ} (γ B : ℝ) (ι : Init m d) (ξs : ℕ → Sample d) (T : ℕ) (x : Pt d) :
    ℝ :=
  Qhat ι.1 (avgIterate γ (stepSize γ T) B ι ξs T) x

/-- The population semigradient `ḡ(W) = E_μ[δ(x, r, x′; W) ∇_W Q̂(x; W)]` ((4.9), (5.1)). -/
noncomputable def gbar {m d : ℕ} (γ : ℝ) (μ : Measure (Sample d)) (b : Fin m → ℝ)
    (W : Param m d) : Param m d :=
  ∫ ξ, delta γ b W ξ • gradQ b W ξ.1 ∂μ

/-- The linearized population semigradient `ḡ₀(W) = E_μ[δ₀(x, r, x′; W) ∇_W Q̂₀(x; W)]` (5.2). -/
noncomputable def gbarLin {m d : ℕ} (γ : ℝ) (μ : Measure (Sample d)) (b : Fin m → ℝ)
    (W0 W : Param m d) : Param m d :=
  ∫ ξ, deltaLin γ b W0 W ξ • gradQlin b W0 ξ.1 ∂μ

/-- Definition 4.1: `W*` is an approximate stationary point, i.e. `W* ∈ S_B` and
`ḡ₀(W*)ᵀ(W − W*) ≥ 0` for every `W ∈ S_B` (4.6). -/
def IsApproxStationary {m d : ℕ} (γ : ℝ) (μ : Measure (Sample d)) (B : ℝ) (b : Fin m → ℝ)
    (W0 Wst : Param m d) : Prop :=
  ‖Wst - W0‖ ≤ B ∧ ∀ W : Param m d, ‖W - W0‖ ≤ B → 0 ≤ ⟪gbarLin γ μ b W0 Wst, W - Wst⟫

end NeuralTD.Convergence


