-- Prove2me | Definitions.Def_DriftLinBandit_BOB_Model
-- name    : DriftLinBandit_BOB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:15.99027+00:00
-- url     : https://prove2.me/theorems/dec0b26f-f487-49be-a05c-b64798853411
-- title:
--   §3, §5–§6, pp. 7–12 — drifting linear bandit, Assumption 1, sliding-window ridge estimator (2), β (3), SW-UCB (Algorithm 1), dynamic regret
-- statement:
--   This file sets up the **drifting linear bandit** of Cheung, Simchi-Levi and Zhu and the **SW-UCB** algorithm.
--
--   **Instance.** An instance consists of a horizon $T$, decision sets $D_t\subseteq\mathbb R^d$ (finite) and parameter vectors $\theta_t\in\mathbb R^d$, for rounds $t=1,\dots,T$, all fixed in advance by an oblivious adversary. In round $t$ the decision maker chooses $X_t\in D_t$ and observes the reward $Y_t=\langle X_t,\theta_t\rangle+\eta_t$. The *standing assumptions* with known constants $L,S>0$ are: each $D_t$ is nonempty, $\|X\|_2\le L$ and $|\langle X,\theta_t\rangle|\le 1$ for all $X\in D_t$, and $\|\theta_t\|_2\le S$. **Assumption 1** asks for an orthonormal basis $\psi_1,\dots,\psi_d$ such that every action of every round is of the form $z\,\psi_i$ with $z\in\mathbb R$. The **total variation** of the instance is
--   $$
--   \sum_{t=1}^{T-1}\|\theta_{t+1}-\theta_t\|_2 ,
--   $$
--   the left side of the variation-budget constraint (1).
--
--   **Noise.** The noises $\eta_t$ are measurable, mutually independent, identically distributed, centred and $R$-sub-Gaussian: $\mathbb E[e^{s\eta_t}]\le e^{s^2R^2/2}$ for every real $s$. An action sequence is *non-anticipatory* when $X_s$ is a measurable function of the earlier noises only.
--
--   **Sliding-window estimator.** For a window size $w$, round $t$ uses the rounds $s=1\vee(t-w),\dots,t-1$ (more generally $s=\max(t_0,t-w),\dots,t-1$ for a run started at round $t_0$). With $\lambda>0$,
--   $$
--   V_{t-1}=\lambda I+\sum_{s}X_sX_s^\top,\qquad \hat\theta_t=V_{t-1}^{-1}\sum_{s}X_sY_s,\qquad \beta=R\sqrt{d\ln\Big(\frac{1+wL^2/\lambda}{\delta}\Big)}+\sqrt\lambda\,S ,
--   $$
--   the estimator (2) and the confidence radius (3); $\|x\|_{A^{-1}}=\sqrt{x^\top A^{-1}x}$.
--
--   **SW-UCB** (Algorithm 1) plays in round $t$ a maximiser over $x\in D_t$ of $x^\top\hat\theta_t+\beta\|x\|_{V_{t-1}^{-1}}$, computed from its own past actions and rewards. The **dynamic regret** of an action sequence is $\mathcal R_T=\mathbb E\big[\sum_{t=1}^T\langle x_t^*-X_t,\theta_t\rangle\big]$ with $x_t^*\in\arg\max_{x\in D_t}\langle x,\theta_t\rangle$.
--
--   These objects are shared by every statement of the mission: Theorem 2 and Lemmas 3–5 concern the estimator, Theorem 3 the SW-UCB algorithm.
--
--   **Formalization Note.** Vectors are functions `Fin d → ℝ`; rounds are numbered from $1$. `win t0 w t` is the window $[\max(t_0,t-w),\,t-1]$, empty for $t=t_0$. `swucb … δ t0 η t ω` is the action of round $t$ of SW-UCB started at round $t_0$ on the noise realisation $\omega$; ties in the argmax are broken by the first maximiser in a fixed enumeration of $D_t$ (the paper fixes no rule). `optVal` is the maximum of $\langle x,\theta_t\rangle$ over the finite set $D_t$, and `regret` is the realised regret $\sum_{t=1}^T(\langle x_t^*,\theta_t\rangle-\langle X_t,\theta_t\rangle)$.
-- source:
--   Cheung, Simchi-Levi & Zhu, arXiv:1903.01461v4, pp. 7–12, §3.2, (1)–(3), Assumption 1, (5), Algorithm 1

import Mathlib

namespace DriftLinBandit.BOB

open MeasureTheory ProbabilityTheory Matrix

noncomputable section

/-! # Drifting linear bandits and the SW-UCB algorithm

Cheung, Simchi-Levi & Zhu, *Hedging the Drift*, arXiv:1903.01461v4, §3.2 (p. 8), §5 (p. 10),
§6 (pp. 11–12). Vectors of `ℝ^d` are functions `Fin d → ℝ`; rounds are numbered `1, …, T` as in
the paper. -/

/-- The Euclidean norm `‖x‖₂ = √(xᵀx)`. -/
def l2 {d : ℕ} (x : Fin d → ℝ) : ℝ := Real.sqrt (x ⬝ᵥ x)

/-- The weighted norm `‖x‖_{A⁻¹} = √(xᵀ A⁻¹ x)`. -/
def wnorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.sqrt (x ⬝ᵥ (A⁻¹ *ᵥ x))

/-- A drifting linear bandit instance (§3.2, p. 8): the horizon `T`, the decision sets `D t ⊆ ℝ^d`
and the parameter vectors `θ t ∈ ℝ^d`, all fixed in advance by an oblivious adversary. Only rounds
`t ∈ [1, T]` matter. -/
structure Instance (d : ℕ) where
  /-- The horizon `T`. -/
  T : ℕ
  /-- The decision set `D_t` of round `t` (finite). -/
  D : ℕ → Finset (Fin d → ℝ)
  /-- The unknown parameter vector `θ_t` of round `t`. -/
  θ : ℕ → Fin d → ℝ

/-- The standing assumptions of §3.2 (p. 8) for the known constants `L, S`: in every round
`t ∈ [T]` the decision set is nonempty, `‖X‖₂ ≤ L` and `|⟨X, θ_t⟩| ≤ 1` for every `X ∈ D_t`, and
`‖θ_t‖₂ ≤ S`. -/
def Instance.Standing {d : ℕ} (I : Instance d) (L S : ℝ) : Prop :=
  ∀ t ∈ Finset.Icc 1 I.T,
    (I.D t).Nonempty ∧ (∀ x ∈ I.D t, l2 x ≤ L ∧ |x ⬝ᵥ I.θ t| ≤ 1) ∧ l2 (I.θ t) ≤ S

/-- Assumption 1 (p. 10): there is an orthonormal basis `ψ_1, …, ψ_d` (the columns of a matrix `Ψ`
with `ΨᵀΨ = I`) such that every action of every round is a multiple `z · ψ_i` of one basis vector. -/
def Assumption1 {d : ℕ} (I : Instance d) : Prop :=
  ∃ Ψ : Matrix (Fin d) (Fin d) ℝ, Ψᵀ * Ψ = 1 ∧
    ∀ t ∈ Finset.Icc 1 I.T, ∀ x ∈ I.D t, ∃ (z : ℝ) (i : Fin d), x = z • (fun k => Ψ k i)

/-- The total variation `∑_{t=1}^{T-1} ‖θ_{t+1} − θ_t‖₂`, the left side of (1). -/
def variation {d : ℕ} (I : Instance d) : ℝ :=
  ∑ t ∈ Finset.Ico 1 I.T, l2 (I.θ (t + 1) - I.θ t)

/-- The noise model of §3.2 (p. 8): the noises `η t` are measurable, mutually independent and
identically distributed, centred, and `R`-sub-Gaussian: `E[exp(s η_t)] ≤ exp(s²R²/2)` for every
real `s` (with the exponential moment integrable). -/
structure IsSubGNoise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (η : ℕ → Ω → ℝ) (R : ℝ) :
    Prop where
  measurable : ∀ t, Measurable (η t)
  indep : iIndepFun η P
  identDistrib : ∀ t, IdentDistrib (η t) (η 0) P P
  mean_zero : ∀ t, ∫ ω, η t ω ∂P = 0
  mgf_integrable : ∀ t (s : ℝ), Integrable (fun ω => Real.exp (s * η t ω)) P
  mgf_le : ∀ t (s : ℝ), ∫ ω, Real.exp (s * η t ω) ∂P ≤ Real.exp (s ^ 2 * R ^ 2 / 2)

/-- A non-anticipatory action sequence: the action `X s` of round `s` is a measurable function of the
noises `η 0, …, η (s-1)` only (the noises of the earlier rounds; `η 0` is an auxiliary independent
variable that may serve as the policy's own randomisation). -/
def IsPredictable {Ω : Type*} {d : ℕ} (η : ℕ → Ω → ℝ) (X : ℕ → Ω → (Fin d → ℝ)) : Prop :=
  ∀ s, ∃ f : (Fin s → ℝ) → (Fin d → ℝ), Measurable f ∧ ∀ ω, X s ω = f (fun r => η r ω)

/-- The sliding window of round `t` for a run started at round `t0`: the rounds
`s ∈ [max t0 (t − w), t − 1]` (for `t0 = 1` this is the paper's `s = 1 ∨ (t − w), …, t − 1`;
it is empty at `t = t0`). -/
def win (t0 w t : ℕ) : Finset ℕ := Finset.Icc (max t0 (t - w)) (t - 1)

/-- The regularised Gram matrix `λI + ∑_{s ∈ W} X_s X_sᵀ` (the matrix `V_{t−1}` of p. 10 when `W`
is the window of round `t`). -/
def gram {d : ℕ} (lam : ℝ) (X : ℕ → Fin d → ℝ) (W : Finset ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  lam • (1 : Matrix (Fin d) (Fin d) ℝ) + ∑ s ∈ W, vecMulVec (X s) (X s)

/-- The sliding-window regularised least-squares estimate (2): `θ̂ = V⁻¹ ∑_{s ∈ W} X_s Y_s`. -/
def est {d : ℕ} (lam : ℝ) (X : ℕ → Fin d → ℝ) (Y : ℕ → ℝ) (W : Finset ℕ) : Fin d → ℝ :=
  (gram lam X W)⁻¹ *ᵥ ∑ s ∈ W, Y s • X s

/-- The confidence radius (3): `β = R √(d ln((1 + wL²/λ)/δ)) + √λ S`. -/
def beta (R L S lam : ℝ) (d w : ℕ) (δ : ℝ) : ℝ :=
  R * Real.sqrt ((d : ℝ) * Real.log ((1 + (w : ℝ) * L ^ 2 / lam) / δ)) + Real.sqrt lam * S

/-- The first maximiser of `f` along the list `l` (ties broken in favour of the earlier element);
`0` on the empty list. -/
def firstArgmax {d : ℕ} (l : List (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ) : Fin d → ℝ :=
  match l with
  | [] => 0
  | x :: xs => xs.foldl (fun b y => if f b < f y then y else b) x

/-- One SW-UCB step (Algorithm 1, lines 4–5; rule (5)). Given the actions `X` taken so far, the
realised noises `e` (so that the rewards are `Y_s = ⟨X_s, θ_s⟩ + e_s`), the window size `w`, the
confidence parameter `δ` and the round `t0` at which this run of SW-UCB was started, the action of
round `t` is the first (in the fixed order `(I.D t).toList`) maximiser over `x ∈ D_t` of
`xᵀθ̂_t + β ‖x‖_{V_{t−1}^{−1}}`, with `θ̂_t`, `V_{t−1}` computed over the window `win t0 w t`. -/
def ucbStep {d : ℕ} (I : Instance d) (R L S lam : ℝ) (w : ℕ) (δ : ℝ) (t0 : ℕ)
    (X : ℕ → Fin d → ℝ) (e : ℕ → ℝ) (t : ℕ) : Fin d → ℝ :=
  let W := win t0 w t
  let Y : ℕ → ℝ := fun s => X s ⬝ᵥ I.θ s + e s
  let θh := est lam X Y W
  let V := gram lam X W
  firstArgmax (I.D t).toList (fun x => x ⬝ᵥ θh + beta R L S lam d w δ * wnorm V x)

/-- The action history of SW-UCB on the realised noise sequence `e`: `swucbHist … e t s` is the
action of round `s ≤ t` (and `0` for `s = 0` or `s > t`). -/
def swucbHist {d : ℕ} (I : Instance d) (R L S lam : ℝ) (w : ℕ) (δ : ℝ) (t0 : ℕ) (e : ℕ → ℝ) :
    ℕ → ℕ → Fin d → ℝ
  | 0 => fun _ => 0
  | t + 1 =>
      Function.update (swucbHist I R L S lam w δ t0 e t) (t + 1)
        (ucbStep I R L S lam w δ t0 (swucbHist I R L S lam w δ t0 e t) e (t + 1))

/-- The SW-UCB algorithm (Algorithm 1) with window size `w`, regularisation `λ`, confidence
parameter `δ` in (3), started afresh at round `t0`: `swucb … η t ω` is the action `X_t` it plays in
round `t` when the noise realisation is `ω`. Plain SW-UCB is `t0 = 1`. -/
def swucb {d : ℕ} {Ω : Type*} (I : Instance d) (R L S lam : ℝ) (w : ℕ) (δ : ℝ) (t0 : ℕ)
    (η : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  swucbHist I R L S lam w δ t0 (fun s => η s ω) t t

/-- The optimal reward of round `t`, `max_{x ∈ D_t} ⟨x, θ_t⟩` (a maximum over a finite set). -/
def optVal {d : ℕ} (I : Instance d) (t : ℕ) : ℝ :=
  sSup ((fun x => x ⬝ᵥ I.θ t) '' (I.D t : Set (Fin d → ℝ)))

/-- The realised dynamic regret `Regret_T = ∑_{t=1}^T ⟨x*_t − X_t, θ_t⟩` of the action sequence `X`
(p. 8); the dynamic regret `R_T` is its expectation. -/
def regret {d : ℕ} {Ω : Type*} (I : Instance d) (X : ℕ → Ω → (Fin d → ℝ)) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 I.T, (optVal I t - X t ω ⬝ᵥ I.θ t)

end

end DriftLinBandit.BOB


