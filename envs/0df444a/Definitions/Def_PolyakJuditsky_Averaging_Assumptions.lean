-- Prove2me | Definitions.Def_PolyakJuditsky_Averaging_Assumptions
-- name    : PolyakJuditsky_Averaging_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:37:49.618989+00:00
-- url     : https://prove2.me/theorems/c570d4d3-1dfb-4a13-bbbc-1ed71ee3d199
-- title:
--   Assumptions 2.3–2.5(a) and 3.1–3.4 of Polyak–Juditsky
-- statement:
--   This file states the standing assumptions of Theorems 1(a) and 2. Throughout, $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},P)$ is a filtered probability space, the disturbances $\xi_t$ ($t\ge1$) take values in $\mathbb R^N$, and $E(\cdot\mid\mathcal F_{t-1})$ is conditional expectation.
--
--   **Assumptions 2.3, 2.4, 2.5(a)** (noise of the linear algorithm, matrix $S$):
--   1. $\xi_t$ is $\mathcal F_t$-measurable and $E|\xi_t|^2<\infty$;
--   2. $E(\xi_t\mid\mathcal F_{t-1})=0$ a.s. and $\sup_{t\ge1}E(|\xi_t|^2\mid\mathcal F_{t-1})<\infty$ a.s.;
--   3. $\lim_{C\to\infty}\limsup_{t\to\infty}E(|\xi_t|^2I(|\xi_t|>C)\mid\mathcal F_{t-1})=0$ in probability, i.e. for all $\eta,\delta>0$ there is $C_0$ with
--   $$P\bigl(E(|\xi_t|^2I(|\xi_t|>C)\mid\mathcal F_{t-1})>\eta\ \text{for infinitely many } t\bigr)\le\delta\quad\text{for all } C\ge C_0;$$
--   4. $E(\xi_t\xi_t^T\mid\mathcal F_{t-1})\to S$ in probability, and $S$ is symmetric positive definite.
--
--   **Assumption 3.1** (Lyapunov function $V$ for the root $x^*$ of $R$): $V:\mathbb R^N\to\mathbb R$ is differentiable, and for some $\lambda_1>0$, $\alpha>0$, $\varepsilon>0$, $L>0$ and all $x,y$: $V(x)\ge\alpha|x|^2$, $|\nabla V(x)-\nabla V(y)|\le L|x-y|$, $V(0)=0$, $\nabla V(x-x^*)^TR(x)>0$ for $x\ne x^*$, and $\nabla V(x-x^*)^TR(x)\ge\lambda_1V(x-x^*)$ for $|x-x^*|\le\varepsilon$.
--
--   **Assumption 3.2** (linearisation at $x^*$ with matrix $G$ and exponent $\lambda$): $0<\lambda\le1$, and for some $K_1$ and $\varepsilon>0$,
--   $$|R(x)-G(x-x^*)|\le K_1|x-x^*|^{1+\lambda}\qquad(|x-x^*|\le\varepsilon),$$
--   and $\operatorname{Re}\lambda_i(G)>0$ for all $i$.
--
--   **Assumption 3.3** (noise of algorithm (7), with $x_t$ the iterate of (7)): $\xi_t$ is adapted with $E|\xi_t|^2<\infty$, $E(\xi_t\mid\mathcal F_{t-1})=0$ a.s., and for some $K_2$ and all $t\ge1$
--   $$E(|\xi_t|^2\mid\mathcal F_{t-1})+|R(x_{t-1})|^2\le K_2(1+|x_{t-1}|^2)\quad\text{a.s.}$$
--   Moreover $\xi_t=\xi_t(0)+\zeta_t$, where $\xi_t(0)$ is adapted and square integrable, $E(\xi_t(0)\mid\mathcal F_{t-1})=0$ a.s., $E(\xi_t(0)\xi_t(0)^T\mid\mathcal F_{t-1})\to S$ in probability with $S$ symmetric positive definite, $\sup_tE(|\xi_t(0)|^2I(|\xi_t(0)|>C)\mid\mathcal F_{t-1})\to0$ in probability as $C\to\infty$ (for all $\eta,\delta>0$ there is $C_0$ with $P(\exists t\ge1:\ E(\cdots)>\eta)\le\delta$ for $C\ge C_0$), and for some $\delta:\mathbb R^N\to\mathbb R$ with $\delta(x)\to0$ as $x\to0$ and all $t$ large enough, $E(|\zeta_t|^2\mid\mathcal F_{t-1})\le\delta(x_{t-1}-x^*)$ a.s.
--
--   **Assumption 3.4** (steps, with exponent $\lambda$ of 3.2): $\gamma_t>0$ for $t\ge1$, $(\gamma_t-\gamma_{t+1})/\gamma_t=o(\gamma_t)$, and
--   $$\sum_{t=1}^\infty\gamma_t^{(1+\lambda)/2}t^{-1/2}<\infty;$$
--   in addition $\gamma_t\to0$ and $\sum_{t\ge1}\gamma_t^2<\infty$.
--
--   These are the hypotheses of Theorem 2 and of the proof steps that lead to it; Theorem 1(a) uses the first block.
--
--   **Formalization Note** Corrections of the printed text, each used in the paper's proof: (i) Assumption 3.1 prints $V(x^*)=0$ and $\nabla V(x-x^*)^TR(x)\ge\lambda V(x)$; together with $V(x)\ge\alpha|x|^2$ these force $x^*=0$, and the proof evaluates $V$ only at the error $\Delta_t=x_t-x^*$ (p. 849), so the conditions are stated at $0$ and at $x-x^*$ (the two readings agree when $x^*=0$). (ii) The paper uses $\lambda$ for both the drift rate of 3.1 and the exponent of 3.2; the former is renamed $\lambda_1$. (iii) Eq. (10) prints $\sum(1+\lambda)/\gamma_t^2t^{-1/2}<\infty$, a typesetting garble; Assumptions 4.7, 5.6 and the proof on p. 851 use $\sum\gamma_t^{(1+\lambda)/2}t^{-1/2}<\infty$. (iv) Assumption 3.3 prints $\delta(x_{t-1})$; the proof of Part 3 (p. 850) uses $\delta(\Delta_{t-1})=\delta(x_{t-1}-x^*)$. (v) $\gamma_t\to0$ and $\sum\gamma_t^2<\infty$ are used by the proof of Theorem 2 (p. 849: "$\sum\gamma_t^2<\infty$" and the Robbins–Siegmund theorem; Part 3 applies Theorem 1(a) under condition (4)) but do not follow from Assumption 3.4; they are added as hypotheses. Encodings: conditioning on $\mathcal F_{t-1}$ is written as $\xi_{t+1}$ given $\mathcal F_t$ for $t\ge0$, which avoids natural-number subtraction; square integrability is required so that the conditional moments are the paper's (Lean's conditional expectation of a non-integrable function is $0$); convergence of matrices in probability is entrywise; "$\to0$ in probability" of a supremum or a limsup is unfolded into its $\eta$–$\delta$ definition instead of using a real supremum, which would be $0$ for an unbounded family; the decomposition (9) is encoded by a second process $\xi_t(0)$ with $\zeta_t:=\xi_t-\xi_t(0)$; "$\delta(x)\to0$ as $x\to0$" is the unpunctured limit, which also gives $\delta(0)=0$.
-- source:
--   Polyak, Juditsky, Acceleration of stochastic approximation by averaging, SIAM J. Control Optim. 30 (1992), p. 839, Assumptions 2.3, 2.4, 2.5(a); p. 840, Assumptions 3.1, 3.2; p. 841, Assumptions 3.3, 3.4, Eq. (9), (10)

import Mathlib
import Definitions.Def_PolyakJuditsky_Averaging_Model

open MeasureTheory Filter Topology

namespace PolyakJuditsky.Averaging

/-- Assumptions 2.3, 2.4 and 2.5(a) on a noise process `ξ_t` (`t ≥ 1`) in `ℝ^N`, on a filtered
probability space `(Ω, ℱ, ℱ_t, P)`. Conditioning on `ℱ_{t-1}` is written with the shifted index:
the noise `ξ (t+1)` given `ℱ t`.
* `ξ_t` is adapted and square integrable (so that the conditional moments below are defined);
* martingale difference: `E(ξ_t | ℱ_{t-1}) = 0` a.s. (Assumption 2.3);
* `sup_{t ≥ 1} E(|ξ_t|² | ℱ_{t-1}) < ∞` a.s. (Assumption 2.3);
* conditional Lindeberg (Assumption 2.4): `lim_{C→∞} limsup_{t→∞} E(|ξ_t|² I(|ξ_t| > C) | ℱ_{t-1}) = 0`
  in probability, unfolded as: for all `η, δ > 0` there is `C₀` such that for every `C ≥ C₀`,
  `P(E(|ξ_t|² I(|ξ_t| > C) | ℱ_{t-1}) > η for infinitely many t) ≤ δ`;
* conditional covariance (Assumption 2.5(a)): `E(ξ_t ξ_tᵀ | ℱ_{t-1}) → S` in probability,
  entrywise, and `S` is symmetric positive definite. -/
structure LinearNoiseAssumptions {N : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (ξ : ℕ → Ω → EuclideanSpace ℝ (Fin N))
    (S : Matrix (Fin N) (Fin N) ℝ) : Prop where
  adapted : Adapted ℱ ξ
  memLp : ∀ t, MemLp (ξ t) 2 P
  mds : ∀ t, P[ξ (t + 1) | ℱ t] =ᵐ[P] 0
  condVar_bdd : ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ t, P[fun ω' => ‖ξ (t + 1) ω'‖ ^ 2 | ℱ t] ω ≤ M
  lindeberg : ∀ η > 0, ∀ δ > 0, ∃ C₀ : ℝ, ∀ C ≥ C₀,
    P {ω | ∃ᶠ t in atTop, η < P[Set.indicator {ω' | C < ‖ξ (t + 1) ω'‖}
      (fun ω' => ‖ξ (t + 1) ω'‖ ^ 2) | ℱ t] ω} ≤ ENNReal.ofReal δ
  condCov : ∀ i j, TendstoInMeasure P
    (fun t ω => P[fun ω' => ξ (t + 1) ω' i * ξ (t + 1) ω' j | ℱ t] ω) atTop (fun _ => S i j)
  posDef : S.PosDef

/-- Assumption 3.1 (Lyapunov function), in the corrected form used by the proof of Theorem 2:
`V : ℝ^N → ℝ` is differentiable and there are `lam₁ > 0` (the paper's `λ`), `α > 0`, `ε > 0`,
`L > 0` with `V(x) ≥ α|x|²`, `|∇V(x) - ∇V(y)| ≤ L|x - y|`, `V(0) = 0` (printed `V(x*) = 0`),
`∇V(x - x*)ᵀ R(x) > 0` for `x ≠ x*`, and `∇V(x - x*)ᵀ R(x) ≥ lam₁ V(x - x*)` for `|x - x*| ≤ ε`
(printed `λ V(x)`). -/
def LyapunovAssumption {N : ℕ} (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (xstar : EuclideanSpace ℝ (Fin N)) (V : EuclideanSpace ℝ (Fin N) → ℝ) : Prop :=
  Differentiable ℝ V ∧
  ∃ lam₁ α ε L : ℝ, 0 < lam₁ ∧ 0 < α ∧ 0 < ε ∧ 0 < L ∧
    (∀ x, α * ‖x‖ ^ 2 ≤ V x) ∧
    (∀ x y, ‖gradient V x - gradient V y‖ ≤ L * ‖x - y‖) ∧
    V 0 = 0 ∧
    (∀ x, x ≠ xstar → 0 < inner ℝ (gradient V (x - xstar)) (R x)) ∧
    (∀ x, ‖x - xstar‖ ≤ ε → lam₁ * V (x - xstar) ≤ inner ℝ (gradient V (x - xstar)) (R x))

/-- Assumption 3.2 (local linearisation): `0 < lam ≤ 1`, and there are `K₁` and `ε > 0` with
`|R(x) - G(x - x*)| ≤ K₁ |x - x*|^{1+lam}` for `|x - x*| ≤ ε`, and `Re λ_i(G) > 0` for every
eigenvalue of `G`. -/
def LinearizationAssumption {N : ℕ} (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (xstar : EuclideanSpace ℝ (Fin N)) (G : Matrix (Fin N) (Fin N) ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧ lam ≤ 1 ∧
  (∃ K₁ ε : ℝ, 0 < ε ∧ ∀ x, ‖x - xstar‖ ≤ ε →
    ‖R x - matApply G (x - xstar)‖ ≤ K₁ * ‖x - xstar‖ ^ (1 + lam)) ∧
  EigenRePos G

/-- Assumption 3.3 (noise), with the decomposition (9) `ξ_t = ξ_t(0) + ζ_t` where
`ξ0 t` is the paper's `ξ_t(0)` and `ζ_t = ξ_t - ξ0_t`. Here `x t = saIterate x₀ γ R ξ t` is the
iterate of Eq. (7), and conditioning on `ℱ_{t-1}` is written with the shifted index (`ξ (t+1)`
given `ℱ t`, next to the iterate `x t`).
* `ξ` and `ξ0` are adapted and square integrable;
* `E(ξ_t | ℱ_{t-1}) = 0` a.s. and, for some `K₂`,
  `E(|ξ_t|² | ℱ_{t-1}) + |R(x_{t-1})|² ≤ K₂ (1 + |x_{t-1}|²)` a.s., for all `t ≥ 1`;
* `E(ξ_t(0) | ℱ_{t-1}) = 0` a.s.; `E(ξ_t(0) ξ_t(0)ᵀ | ℱ_{t-1}) → S` in probability (entrywise),
  `S` symmetric positive definite;
* `sup_t E(|ξ_t(0)|² I(|ξ_t(0)| > C) | ℱ_{t-1}) → 0` in probability as `C → ∞`, unfolded as:
  for all `η, δ > 0` there is `C₀` such that for all `C ≥ C₀`,
  `P(∃ t ≥ 1, E(|ξ_t(0)|² I(|ξ_t(0)| > C) | ℱ_{t-1}) > η) ≤ δ`;
* for some `δ : ℝ^N → ℝ` with `δ(x) → 0` as `x → 0` and all `t` large enough,
  `E(|ζ_t|² | ℱ_{t-1}) ≤ δ(x_{t-1} - x*)` a.s. (printed `δ(x_{t-1})`). -/
structure NoiseAssumption {N : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (x₀ : EuclideanSpace ℝ (Fin N)) (γ : ℕ → ℝ)
    (R : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N))
    (ξ ξ0 : ℕ → Ω → EuclideanSpace ℝ (Fin N)) (xstar : EuclideanSpace ℝ (Fin N))
    (S : Matrix (Fin N) (Fin N) ℝ) : Prop where
  adapted : Adapted ℱ ξ
  memLp : ∀ t, MemLp (ξ t) 2 P
  mds : ∀ t, P[ξ (t + 1) | ℱ t] =ᵐ[P] 0
  growth : ∃ K₂ : ℝ, ∀ t, ∀ᵐ ω ∂P,
    P[fun ω' => ‖ξ (t + 1) ω'‖ ^ 2 | ℱ t] ω + ‖R (saIterate x₀ γ R ξ t ω)‖ ^ 2
      ≤ K₂ * (1 + ‖saIterate x₀ γ R ξ t ω‖ ^ 2)
  adapted0 : Adapted ℱ ξ0
  memLp0 : ∀ t, MemLp (ξ0 t) 2 P
  mds0 : ∀ t, P[ξ0 (t + 1) | ℱ t] =ᵐ[P] 0
  condCov0 : ∀ i j, TendstoInMeasure P
    (fun t ω => P[fun ω' => ξ0 (t + 1) ω' i * ξ0 (t + 1) ω' j | ℱ t] ω) atTop (fun _ => S i j)
  posDef : S.PosDef
  lindeberg0 : ∀ η > 0, ∀ δ > 0, ∃ C₀ : ℝ, ∀ C ≥ C₀,
    P {ω | ∃ t, η < P[Set.indicator {ω' | C < ‖ξ0 (t + 1) ω'‖}
      (fun ω' => ‖ξ0 (t + 1) ω'‖ ^ 2) | ℱ t] ω} ≤ ENNReal.ofReal δ
  remainder : ∃ δ : EuclideanSpace ℝ (Fin N) → ℝ, Tendsto δ (𝓝 0) (𝓝 0) ∧
    ∃ t₀ : ℕ, ∀ t ≥ t₀, ∀ᵐ ω ∂P,
      P[fun ω' => ‖ξ (t + 1) ω' - ξ0 (t + 1) ω'‖ ^ 2 | ℱ t] ω ≤ δ (saIterate x₀ γ R ξ t ω - xstar)

/-- Assumption 3.4 (step sizes), with Eq. (10) in its intended form and two hypotheses the
proof of Theorem 2 uses added: `γ_t > 0` for `t ≥ 1`; `(γ_t - γ_{t+1})/γ_t = o(γ_t)`;
`∑_{t ≥ 1} γ_t^{(1+lam)/2} t^{-1/2} < ∞` (Eq. (10), printed `∑ (1+λ)/γ_t² t^{-1/2}`);
added: `γ_t → 0` and `∑_{t ≥ 1} γ_t² < ∞`. -/
def StepAssumption (γ : ℕ → ℝ) (lam : ℝ) : Prop :=
  (∀ t, 1 ≤ t → 0 < γ t) ∧
  (fun t => (γ t - γ (t + 1)) / γ t) =o[atTop] γ ∧
  Summable (fun t : ℕ => γ (t + 1) ^ ((1 + lam) / 2) * ((t + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ∧
  Tendsto γ atTop (𝓝 0) ∧
  Summable (fun t : ℕ => γ (t + 1) ^ 2)

end PolyakJuditsky.Averaging


