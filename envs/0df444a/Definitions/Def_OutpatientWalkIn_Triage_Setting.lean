-- Prove2me | Definitions.Def_OutpatientWalkIn_Triage_Setting
-- name    : OutpatientWalkIn_Triage_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:05:17.09725+00:00
-- url     : https://prove2.me/theorems/e89ec55a-4f8e-467e-9596-28a91e7f40c9
-- title:
--   §3–§5.2 — parameters, Assumptions 1–2, the observable equilibrium (6)–(10), the strategic cost (Ob.P), the triage cost (T.Ob.P) and the thresholds α̲, ᾱ
-- statement:
--   This file sets up the observable setting of the outpatient model of Liu, van Jaarsveld, Wang and Xiao and the two provider models compared in §5.2.
--
--   **Parameters.** Strategic patients arrive at rate $\lambda>0$; exogenous walk-ins arrive at rate $\lambda_E\ge0$ and are always served on the day. A served patient gains $R>0$; a scheduled patient pays $C_D>0$ per day of delay; a walk-in pays $C_W>0$ times the expected in-clinic wait. The provider pays $C_L\ge0$ per lost (balking) patient and $C_O\ge0$ times the overtime $o(\cdot)$. The total capacity $\mu>0$ is split into appointment hours $\mu_S$ and walk-in hours $\mu_W=\mu-\mu_S$. The in-clinic wait $w$ is convex and strictly increasing on $[0,\infty)$ with $w(0)=0$ (Assumption 1), and the overtime $o$ is convex and strictly increasing on $[0,\infty)$ (Assumption 2).
--
--   **Utilities** (observable setting, $C_G=0$). At observed delay $d$, scheduling is worth $u^2_S(d)=R-C_D d$ (1). If a fraction $p_W$ of strategic patients walks in, walking in is worth
--   $$u^2_W(p_W)=R-C_W\,w\Big(\frac{\lambda_E+p_W\lambda}{\mu_W}\Big),$$
--   which is (2) with (5); balking is worth $0$.
--
--   **Equilibrium.** A strategy is a triple $(\delta,p_W,p_B)$ with $\delta,p_W,p_B\ge0$: schedule if the observed delay is at most $\delta$, otherwise walk in or balk with probabilities proportional to $p_W$, $p_B$. It is an *observable equilibrium* at allocation $\mu_S$ when $p_W+p_B>0$ and
--   $$\begin{aligned}
--   &u^2_S(d)\ge \tfrac{p_W}{p_W+p_B}u^2_W(p_W)+\tfrac{p_B}{p_W+p_B}\cdot0 \quad (0\le d\le\delta), &&(6)\\
--   &u^2_S(d)< \tfrac{p_W}{p_W+p_B}u^2_W(p_W)+\tfrac{p_B}{p_W+p_B}\cdot0 \quad (d>\delta), &&(7)\\
--   &p_W+p_B=\pi(\delta,\mu_S), &&(8)\\
--   &p_W=0\ \text{or}\ u^2_W(p_W)\ge0, &&(9)\\
--   &p_B=0\ \text{or}\ u^2_W(p_W)\le0. &&(10)
--   \end{aligned}$$
--
--   **Costs.** The *strategic model* (patients choose freely) costs, at allocation $\mu_S$ and equilibrium $(\delta,p_W,p_B)$,
--   $$Z^s(\mu_S)=C_L\,p_B\lambda+C_O\,o\Big(\frac{p_W\lambda+\lambda_E}{\mu-\mu_S}\Big) \tag{Ob.P}$$
--   and the *triage model* (walk-in hours closed to strategic patients) costs
--   $$Z^t(\mu_S)=C_L\,\pi(R/C_D,\mu_S)\,\lambda+C_O\,o\Big(\frac{\lambda_E}{\mu-\mu_S}\Big). \tag{T.Ob.P}$$
--
--   **Thresholds** (p. 27). With $\underline\mu_W$ the solution of (15) and $o'$ the derivative of $o$,
--   $$\underline\alpha=\frac{o'(\lambda_E/\mu)}{\mu},\qquad \overline\alpha=\frac{o'(\lambda_E/\underline\mu_W)}{\underline\mu_W}\cdot\max\Big\{\frac{\lambda_E}{\lambda\,\pi(R/C_D,\mu-\underline\mu_W)},1\Big\}.$$
--
--   These objects are the vocabulary of Proposition 6 and of every milestone of the mission.
--
--   **Formalization Note** The observable setting is defined directly (the paper reaches it as $C_G=0$, $\lambda_S=\lambda$, $\lambda_W=0$ through Lemma 4 and Appendix D.3); $C_G$ is not a parameter. The signs $\lambda>0$, $\lambda_E\ge0$, $C_L,C_O\ge0$, $\mu>0$ are implicit in the paper and stated in the standing assumptions. The guard $p_W+p_B>0$ makes the mixture weights of (6)–(7) well defined; by (8) it says $\pi(\delta,\mu_S)>0$, which holds for every $\delta\ge0$, so it excludes no equilibrium of the paper. The delays $d$ in (6) range over $d\ge0$. Costs are defined for any $\mu_S$, but every theorem of the mission uses them only for $\mu_S\in[0,\mu)$, so that $\mu_W>0$. $o'$ is Mathlib's `deriv`, which is $0$ where $o$ is not differentiable; the theorems that use $\underline\alpha$, $\overline\alpha$ assume differentiability at the two points $\lambda_E/\mu$ and $\lambda_E/\underline\mu_W$. $\underline\mu_W$ enters $\overline\alpha$ as a parameter.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), pp. 9–14, 19, 21–22, 27, (1), (2), (5)–(10), (15), Assumptions 1–2, (Ob.P), (T.Ob.P), definitions of α̲ and ᾱ; Online Appendix p. 10, D.3

import Mathlib
import Definitions.Def_OutpatientWalkIn_Triage_Queue

namespace OutpatientWalkIn.Triage

/-- The model parameters (§3, pp. 9–19): strategic arrival rate `lam` (= λ), exogenous walk-in
rate `lamE` (= λ_E), reward `R`, delay cost per day `CD`, in-clinic waiting cost `CW`, lost-demand
cost `CL`, overtime cost `CO`, total capacity `mu` (= μ), in-clinic wait function `w` and overtime
function `o`. -/
structure Model where
  lam : ℝ
  lamE : ℝ
  R : ℝ
  CD : ℝ
  CW : ℝ
  CL : ℝ
  CO : ℝ
  mu : ℝ
  w : ℝ → ℝ
  o : ℝ → ℝ

namespace Model

/-- Standing assumptions: signs of the parameters (pp. 9–12), Assumption 1 (p. 13) on `w` and
Assumption 2 (p. 19) on `o`, both on `[0, ∞)`. -/
def Standing (M : Model) : Prop :=
  0 < M.lam ∧ 0 ≤ M.lamE ∧ 0 < M.R ∧ 0 < M.CD ∧ 0 < M.CW ∧ 0 ≤ M.CL ∧ 0 ≤ M.CO ∧ 0 < M.mu ∧
  ConvexOn ℝ (Set.Ici 0) M.w ∧ StrictMonoOn M.w (Set.Ici 0) ∧ M.w 0 = 0 ∧
  ConvexOn ℝ (Set.Ici 0) M.o ∧ StrictMonoOn M.o (Set.Ici 0)

/-- Second-stage utility of scheduling at observed delay `d`, (1): `u²_S(d) = R - C_D d`. -/
def u2S (M : Model) (d : ℝ) : ℝ := M.R - M.CD * d

/-- Second-stage utility of walking in, (2) with (5), in the observable setting (`C_G = 0`,
`λ_S = λ`, `λ_W = 0`) at allocation `μS`, walk-in hours `μ_W = μ - μ_S`:
`u²_W(p_W) = R - C_W w((λ_E + p_W λ)/μ_W)`. -/
noncomputable def u2W (M : Model) (μS pW : ℝ) : ℝ :=
  M.R - M.CW * M.w ((M.lamE + pW * M.lam) / (M.mu - μS))

end Model

/-- A strategy of the strategic patients in the observable setting: delay threshold `δ`,
probabilities `pW` of walking in and `pB` of balking. -/
structure ObsStrategy where
  δ : ℝ
  pW : ℝ
  pB : ℝ

namespace Model

/-- Observable equilibrium at allocation `μS`: conditions (6)–(10) (p. 14) with `C_G = 0`,
together with `δ, p_W, p_B ≥ 0` and the guard `p_W + p_B > 0`, so that the mixture weights in
(6)–(7) are well defined (by (8) the guard says `π(δ, μ_S) > 0`). -/
def IsObsEq (M : Model) (μS : ℝ) (e : ObsStrategy) : Prop :=
  0 ≤ e.δ ∧ 0 ≤ e.pW ∧ 0 ≤ e.pB ∧ 0 < e.pW + e.pB ∧
  (∀ d : ℝ, 0 ≤ d → d ≤ e.δ →
      M.u2S d ≥ e.pW / (e.pW + e.pB) * M.u2W μS e.pW + e.pB / (e.pW + e.pB) * 0) ∧
  (∀ d : ℝ, e.δ < d →
      M.u2S d < e.pW / (e.pW + e.pB) * M.u2W μS e.pW + e.pB / (e.pW + e.pB) * 0) ∧
  e.pW + e.pB = blockProb M.lam e.δ μS ∧
  (e.pW = 0 ∨ M.u2W μS e.pW ≥ 0) ∧
  (e.pB = 0 ∨ M.u2W μS e.pW ≤ 0)

/-- Provider cost of the strategic model at allocation `μS` and equilibrium `e`, (Ob.P), p. 22:
`C_L p_B λ + C_O o((p_W λ + λ_E)/μ_W)`. -/
noncomputable def obsCost (M : Model) (μS : ℝ) (e : ObsStrategy) : ℝ :=
  M.CL * e.pB * M.lam + M.CO * M.o ((e.pW * M.lam + M.lamE) / (M.mu - μS))

/-- Provider cost of the triage model at allocation `μS`, (T.Ob.P), p. 27:
`C_L π(R/C_D, μ_S) λ + C_O o(λ_E/(μ - μ_S))`. -/
noncomputable def triageCost (M : Model) (μS : ℝ) : ℝ :=
  M.CL * blockProb M.lam (M.R / M.CD) μS * M.lam + M.CO * M.o (M.lamE / (M.mu - μS))

/-- The threshold `α̲ = o'(λ_E/μ)/μ` (p. 27). -/
noncomputable def alphaLow (M : Model) : ℝ :=
  deriv M.o (M.lamE / M.mu) / M.mu

/-- The threshold `ᾱ = (o'(λ_E/μ̲_W)/μ̲_W) · max{λ_E/(λ π(R/C_D, μ - μ̲_W)), 1}` (p. 27), where
`μWl` is `μ̲_W` of (15). -/
noncomputable def alphaHigh (M : Model) (μWl : ℝ) : ℝ :=
  deriv M.o (M.lamE / μWl) / μWl *
    max (M.lamE / (M.lam * blockProb M.lam (M.R / M.CD) (M.mu - μWl))) 1

end Model

end OutpatientWalkIn.Triage


