-- Prove2me | Definitions.Def_TwoSidedExp_DemandLimit_Setting
-- name    : TwoSidedExp_DemandLimit_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:57.159755+00:00
-- url     : https://prove2.me/theorems/d4456624-bf54-43a5-a8ae-5e507c769200
-- title:
--   §3–§5 — the mean-field two-sided marketplace: MNL choice (7), steady state (9), W (10), the TSR experimental system (13)–(16), Q_ij(∞) (18), GTE and the naive CR/LR estimators (19)–(20)
-- statement:
--   This file sets up the mean-field model of a two-sided marketplace of Johari, Li, Liskovich and Weintraub, and the two-sided randomized (TSR) experiments run on it.
--
--   **Mean-field system.** There are finitely many listing types $\theta\in\Theta$ and customer types $\gamma\in\Gamma$. Listings of type $\theta$ have total mass $\rho(\theta)$; a share $\phi_\gamma$ of arriving customers is of type $\gamma$; customers arrive at total rate $\lambda$. A type-$\gamma$ customer considers an available type-$\theta$ listing with probability $\alpha_\gamma(\theta)$, has utility $v_\gamma(\theta)$ for it and an outside option of value $\epsilon_\gamma$. A booked type-$\theta$ listing stays occupied for an exponential time of rate $\tau\nu(\theta)$. For a vector $s=(s(\theta))_\theta$ of available masses, the choice probability (7) is
--   $$p_\gamma(\theta\mid s)=\frac{\alpha_\gamma(\theta)v_\gamma(\theta)s(\theta)}{\epsilon_\gamma+\sum_{\theta'}\alpha_\gamma(\theta')v_\gamma(\theta')s(\theta')}.$$
--   The state space (6) is $\mathcal S=\{s:0\le s(\theta)\le\rho(\theta)\}$, and $s$ is a **steady state** for $(\lambda,\tau)$ if $s\in\mathcal S$ and the flow balance (9) holds:
--   $$(\rho(\theta)-s(\theta))\,\tau\nu(\theta)=\lambda\sum_\gamma\phi_\gamma\,p_\gamma(\theta\mid s)\qquad(\theta\in\Theta).$$
--   The objective of (10) is
--   $$W(s)=\sum_\gamma\lambda\phi_\gamma\log\Big(\epsilon_\gamma+\sum_\theta\alpha_\gamma(\theta)v_\gamma(\theta)s(\theta)\Big)-\sum_\theta\tau\nu(\theta)\rho(\theta)\log s(\theta)+\sum_\theta\tau\nu(\theta)s(\theta).$$
--
--   **Base model and standing assumptions.** A model is a mean-field system together with the treatment parameters $\tilde\alpha_\gamma(\theta)$, $\tilde v_\gamma(\theta)$. The standing assumptions are: $\rho(\theta)>0$ with $\sum_\theta\rho(\theta)=1$; $\phi_\gamma>0$ with $\sum_\gamma\phi_\gamma=1$; $0<\alpha_\gamma(\theta)\le1$ and $0<\tilde\alpha_\gamma(\theta)\le1$; $v_\gamma(\theta)>0$, $\tilde v_\gamma(\theta)>0$; $\epsilon_\gamma>0$; $\nu(\theta)>0$.
--
--   **TSR experimental system (13)–(16).** A fraction $a_C$ of customers and a fraction $a_L$ of listings are treated. The experimental system is the mean-field system with customer types $(\gamma,i)$ and listing types $(\theta,j)$, $i,j\in\{0,1\}$ ($0$ = control, $1$ = treatment), with
--   $$\phi_{\gamma,1}=a_C\phi_\gamma,\quad\phi_{\gamma,0}=(1-a_C)\phi_\gamma,\quad\rho(\theta,1)=a_L\rho(\theta),\quad\rho(\theta,0)=(1-a_L)\rho(\theta),$$
--   $\alpha_{\gamma,i}(\theta,j)=\tilde\alpha_\gamma(\theta)$ and $v_{\gamma,i}(\theta,j)=\tilde v_\gamma(\theta)$ if $i=j=1$ and $\alpha_\gamma(\theta)$, $v_\gamma(\theta)$ otherwise, $\epsilon_{\gamma,i}=\epsilon_\gamma$, $\nu(\theta,j)=\nu(\theta)$. Its choice probability $p_{\gamma,i}(\theta,j\mid s)$ (44) does not depend on $(a_C,a_L)$; the mass vector is written $\rho(a_L)$.
--
--   **Booking rates and estimators.** At a state $s$ of the design $(a_C,a_L)$,
--   $$Q_{ij}(\infty\mid a_C,a_L)=\lambda\sum_\theta\sum_\gamma\phi_{\gamma,i}\,p_{\gamma,i}(\theta,j\mid s)\qquad(18).$$
--   The global treatment effect is $\mathrm{GTE}=Q_{11}(\infty\mid1,1)-Q_{00}(\infty\mid0,0)$, each evaluated at a state of its own design, and the naive estimators are
--   $$\widehat{\mathrm{GTE}}^{\mathrm{CR}}(\infty\mid a_C)=\frac{Q_{11}(\infty\mid a_C,1)}{a_C}-\frac{Q_{01}(\infty\mid a_C,1)}{1-a_C},\qquad \widehat{\mathrm{GTE}}^{\mathrm{LR}}(\infty\mid a_L)=\frac{Q_{11}(\infty\mid1,a_L)}{a_L}-\frac{Q_{10}(\infty\mid1,a_L)}{1-a_L}.$$
--
--   These are the objects of Theorem 1, Proposition 2 and Theorem 3.
--
--   **Formalization Note** `MFSystem` carries `ρ, φ, α, v, eps, ν` (`eps` is $\epsilon$); $\lambda$ and $\tau$ are arguments `lam`, `tau`. `Model.expt aC aL` is the experimental system, `Model.rhoL aL` its mass vector $\rho(a_L)$, `Model.pE` its design-independent choice probability (the `rfl` lemma `expt_choice` records this), and `Model.withVt M w` replaces $\tilde v$ by $w$. `Q`, `gte`, `crEst`, `lrEst` take the state as an argument; theorems feed them steady states. (18) defines $Q_{ij}(\infty)$ as the long-run time average of the ODE trajectory and equates it with the steady-state formula via global stability; the formalization uses the steady-state formula (the right side of (18)). In (10) the printed $\tau(\theta)$ outside $\sum_\theta$ is read inside the sum, as in (30), p. A1, and $\lambda_\gamma=\lambda\phi_\gamma$. The bounds $\alpha,\tilde\alpha\le1$ and $\nu>0$ are implicit in the paper (probabilities, an exponential rate) and are stated explicitly. Nonemptiness of $\Theta$ and $\Gamma$ follows from the normalisations.
-- source:
--   Johari, Li, Liskovich, Weintraub, Experimental Design in Two-Sided Platforms: An Analysis of Bias, arXiv:2002.05670v5, pp. 7–17 and A1, A6, §3–§5, (6)–(10), (13)–(20), (30), (44)–(45)

import Mathlib

namespace TwoSidedExp.DemandLimit

/-- §3–§4, pp. 7–11: a mean-field two-sided marketplace over finite listing types `Θ` and customer
types `Γ`. `ρ θ` is the mass of type-`θ` listings, `φ γ` the share of type-`γ` customers among
arrivals, `α γ θ` the probability that a type-`γ` customer includes an available type-`θ` listing in
its consideration set, `v γ θ` its utility for it, `eps γ` the value `ϵ_γ` of its outside option, and
`ν θ` the holding-rate factor (a booked type-`θ` listing stays occupied for an exponential time of
rate `τ ν(θ)`). The arrival rate `λ` and the holding scale `τ` are not fields: they vary. -/
structure MFSystem (Γ Θ : Type) where
  ρ : Θ → ℝ
  φ : Γ → ℝ
  α : Γ → Θ → ℝ
  v : Γ → Θ → ℝ
  eps : Γ → ℝ
  ν : Θ → ℝ

namespace MFSystem

variable {Γ Θ : Type} [Fintype Γ] [Fintype Θ]

/-- (7), p. 11 (and (44), p. A6, for the experimental system): the mean-field choice probability
`p_γ(θ|s) = α_γ(θ) v_γ(θ) s(θ) / (ϵ_γ + Σ_θ' α_γ(θ') v_γ(θ') s(θ'))`. -/
noncomputable def choice (S : MFSystem Γ Θ) (γ : Γ) (θ : Θ) (s : Θ → ℝ) : ℝ :=
  S.α γ θ * S.v γ θ * s θ / (S.eps γ + ∑ θ', S.α γ θ' * S.v γ θ' * s θ')

/-- (6), p. 11: the state space `S = {s : 0 ≤ s(θ) ≤ ρ(θ)}`. -/
def InS (S : MFSystem Γ Θ) (s : Θ → ℝ) : Prop :=
  ∀ θ, 0 ≤ s θ ∧ s θ ≤ S.ρ θ

/-- (9), p. 12 (and (45), p. A6): `s` is a steady state of the mean-field system with arrival rate
`lam` and holding scale `tau` if `s ∈ S` and
`(ρ(θ) − s(θ)) τ ν(θ) = λ Σ_γ φ_γ p_γ(θ|s)` for every `θ`. -/
def IsSteady (S : MFSystem Γ Θ) (lam tau : ℝ) (s : Θ → ℝ) : Prop :=
  S.InS s ∧ ∀ θ, (S.ρ θ - s θ) * (tau * S.ν θ) = lam * ∑ γ, S.φ γ * S.choice γ θ s

/-- (10), p. 12, as in (30), p. A1: the objective
`W(s) = Σ_γ λ φ_γ log(ϵ_γ + Σ_θ α_γ(θ) v_γ(θ) s(θ)) − Σ_θ τ ν(θ) ρ(θ) log s(θ) + Σ_θ τ ν(θ) s(θ)`
(the printed `τ(θ)` outside `Σ_θ` read inside it, and `λ_γ = λ φ_γ`). -/
noncomputable def W (S : MFSystem Γ Θ) (lam tau : ℝ) (s : Θ → ℝ) : ℝ :=
  ∑ γ, lam * S.φ γ * Real.log (S.eps γ + ∑ θ, S.α γ θ * S.v γ θ * s θ)
    - ∑ θ, tau * S.ν θ * S.ρ θ * Real.log (s θ)
    + ∑ θ, tau * S.ν θ * s θ

end MFSystem

/-- §3 and §5.1, pp. 7–9, 14: the base model, a mean-field system `sys` together with the
consideration probabilities `αt = α̃` and utilities `vt = ṽ` that apply when a treated customer meets
a treated listing. -/
structure Model (Γ Θ : Type) where
  sys : MFSystem Γ Θ
  αt : Γ → Θ → ℝ
  vt : Γ → Θ → ℝ

namespace Model

variable {Γ Θ : Type} [Fintype Γ] [Fintype Θ]

/-- §3, pp. 7–9, and §5.1, p. 14: the standing assumptions. `ρ(θ) > 0` with `Σ_θ ρ(θ) = 1`,
`φ_γ > 0` with `Σ_γ φ_γ = 1`, `0 < α_γ(θ) ≤ 1`, `0 < α̃_γ(θ) ≤ 1`, `v_γ(θ) > 0`, `ṽ_γ(θ) > 0`,
`ϵ_γ > 0`, and `ν(θ) > 0`. (The upper bounds on `α`, `α̃` and the positivity of `ν` are implicit in
the page: they are probabilities and an exponential rate.) -/
structure Standing (M : Model Γ Θ) : Prop where
  rho_pos : ∀ θ, 0 < M.sys.ρ θ
  rho_sum : ∑ θ, M.sys.ρ θ = 1
  phi_pos : ∀ γ, 0 < M.sys.φ γ
  phi_sum : ∑ γ, M.sys.φ γ = 1
  alpha_pos : ∀ γ θ, 0 < M.sys.α γ θ
  alpha_le_one : ∀ γ θ, M.sys.α γ θ ≤ 1
  alphat_pos : ∀ γ θ, 0 < M.αt γ θ
  alphat_le_one : ∀ γ θ, M.αt γ θ ≤ 1
  v_pos : ∀ γ θ, 0 < M.sys.v γ θ
  vt_pos : ∀ γ θ, 0 < M.vt γ θ
  eps_pos : ∀ γ, 0 < M.sys.eps γ
  nu_pos : ∀ θ, 0 < M.sys.ν θ

/-- §5.1, item 1, p. 15, and p. 20: the listing masses of the experimental system with a fraction
`aL` of listings treated, `ρ(θ,1|aL) = aL ρ(θ)` and `ρ(θ,0|aL) = (1 − aL) ρ(θ)`. -/
def rhoL (M : Model Γ Θ) (aL : ℝ) : Θ × Fin 2 → ℝ :=
  fun p => if p.2 = 1 then aL * M.sys.ρ p.1 else (1 - aL) * M.sys.ρ p.1

/-- §5.1, (13)–(16) and items 1–3, pp. 14–16: the two-sided randomization (TSR) experimental system
with customer treatment fraction `aC` and listing treatment fraction `aL`. Its customer types are
`(γ, i)` and its listing types `(θ, j)`, with `0` = control and `1` = treatment;
`φ_{γ,1} = aC φ_γ`, `φ_{γ,0} = (1 − aC) φ_γ`, `ρ(θ,j)` as in `rhoL`; the treatment parameters
`α̃, ṽ` apply only when both `i = 1` and `j = 1`; `ϵ_{γ,i} = ϵ_γ` and `ν(θ,j) = ν(θ)`. -/
def expt (M : Model Γ Θ) (aC aL : ℝ) : MFSystem (Γ × Fin 2) (Θ × Fin 2) where
  ρ := M.rhoL aL
  φ := fun q => if q.2 = 1 then aC * M.sys.φ q.1 else (1 - aC) * M.sys.φ q.1
  α := fun q p => if q.2 = 1 ∧ p.2 = 1 then M.αt q.1 p.1 else M.sys.α q.1 p.1
  v := fun q p => if q.2 = 1 ∧ p.2 = 1 then M.vt q.1 p.1 else M.sys.v q.1 p.1
  eps := fun q => M.sys.eps q.1
  ν := fun p => M.sys.ν p.1

/-- (44), p. A6: the experimental choice probability `p_{γ,i}(θ,j|s)`. It does not depend on the
design `(aC, aL)` (see `expt_choice`), so it is written once. -/
noncomputable def pE (M : Model Γ Θ) (q : Γ × Fin 2) (p : Θ × Fin 2) (s : Θ × Fin 2 → ℝ) : ℝ :=
  (M.expt 1 1).choice q p s

omit [Fintype Γ] in
/-- The experimental choice probability is the same for every design `(aC, aL)`. -/
theorem expt_choice (M : Model Γ Θ) (aC aL : ℝ) : (M.expt aC aL).choice = M.pE := rfl

/-- (18), p. 16: the steady-state booking rate of treatment-condition-`i` customers for
treatment-condition-`j` listings under the design `(aC, aL)`,
`Q_ij(∞|aC,aL) = λ Σ_θ Σ_γ φ_{γ,i} p_{γ,i}(θ,j|s)`, evaluated at the state `s` (every theorem feeds it
a steady state `s = s*(aC,aL)`). -/
noncomputable def Q (M : Model Γ Θ) (lam aC aL : ℝ) (s : Θ × Fin 2 → ℝ) (i j : Fin 2) : ℝ :=
  lam * ∑ θ, ∑ γ, (M.expt aC aL).φ (γ, i) * (M.expt aC aL).choice (γ, i) (θ, j) s

/-- p. 16: the global treatment effect `GTE = Q_11(∞|1,1) − Q_00(∞|0,0)`, with `sGT` a state of the
global-treatment system `(1,1)` and `sGC` a state of the global-control system `(0,0)`. -/
noncomputable def gte (M : Model Γ Θ) (lam : ℝ) (sGT sGC : Θ × Fin 2 → ℝ) : ℝ :=
  M.Q lam 1 1 sGT 1 1 - M.Q lam 0 0 sGC 0 0

/-- (19), p. 17: the steady-state naive CR estimator
`ĜTE^CR(∞|aC) = Q_11(∞|aC,1)/aC − Q_01(∞|aC,1)/(1 − aC)`, at a state `s` of the design `(aC, 1)`. -/
noncomputable def crEst (M : Model Γ Θ) (lam aC : ℝ) (s : Θ × Fin 2 → ℝ) : ℝ :=
  M.Q lam aC 1 s 1 1 / aC - M.Q lam aC 1 s 0 1 / (1 - aC)

/-- (20), p. 17: the steady-state naive LR estimator
`ĜTE^LR(∞|aL) = Q_11(∞|1,aL)/aL − Q_10(∞|1,aL)/(1 − aL)`, at a state `s` of the design `(1, aL)`. -/
noncomputable def lrEst (M : Model Γ Θ) (lam aL : ℝ) (s : Θ × Fin 2 → ℝ) : ℝ :=
  M.Q lam 1 aL s 1 1 / aL - M.Q lam 1 aL s 1 0 / (1 - aL)

/-- The model `M` with its treatment utilities `ṽ` replaced by `w`. -/
def withVt (M : Model Γ Θ) (w : Γ → Θ → ℝ) : Model Γ Θ :=
  { M with vt := w }

end Model

end TwoSidedExp.DemandLimit


