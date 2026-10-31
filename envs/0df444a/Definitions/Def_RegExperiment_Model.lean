-- Prove2me | Definitions.Def_RegExperiment_Model
-- name    : RegExperiment_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:43:54.062602+00:00
-- url     : https://prove2.me/theorems/6c0fc26f-7a58-4c5d-85e7-7ece6311aa44
-- title:
--   Primitives, beliefs and the ex post value $u^2(S,z)$ with withdrawal standard $z^*$
-- statement:
--   A firm and a social planner learn about a binary state $\theta\in\{G,B\}$ in two phases: costly ex ante experimentation (ended by rejection or adoption) and costless ex post learning on the market (ended by withdrawal).
--
--   **Primitives.** The planner earns the flow $v^G_p>0$ in the good state and $v^B_p<0$ in the bad state while the product is on the market; experimentation costs $c>0$ per unit of time; payoffs are discounted at rate $r>0$. Information arrives as a Brownian signal with drift $\pm\mu_n$ and variance $\rho^2$ in phase $n\in\{1,2\}$ ($n=1$ ex ante, $n=2$ ex post). At externality rate $e$ the firm earns $v_i=(1-e)v^G_p$ on the market.
--
--   **Beliefs** are log-odds $\sigma=\log\frac{q}{1-q}$, with $\pi_G(\sigma)=\frac{e^\sigma}{1+e^\sigma}$, $\pi_B(\sigma)=\frac{1}{1+e^\sigma}$. With $\lambda_n=2\mu_n^2/\rho^2$,
--   $$
--   r_{1,2}=\tfrac12\Bigl(1\mp\sqrt{1+4r/\lambda_2}\Bigr),\qquad R_{1,2}=\tfrac12\Bigl(1\mp\sqrt{1+4r/\lambda_1}\Bigr).
--   $$
--
--   **Ex post value.** After adoption at belief $S$ with withdrawal standard $z\le S$, the expected discounted probability of withdrawal is $\psi(S,G,z)=e^{-r_2(S-z)}$ and $\psi(S,B,z)=e^{r_1(S-z)}$ ($\psi=1$ if $S<z$). A player with flows $(a_G,a_B)$ obtains
--   $$
--   u^2(S,z)=\pi_G(S)\,\frac{a_G}{r}\bigl(1-\psi(S,G,z)\bigr)+\pi_B(S)\,\frac{a_B}{r}\bigl(1-\psi(S,B,z)\bigr).
--   $$
--   The planner's withdrawal standard is
--   $$
--   z^*=-\ln\frac{v^G_p\,r_2}{v^B_p\,r_1}.
--   $$
--
--   **Liabilities.** Strong liability is $\bar L(e)=v_i-v^B_p$, the top of the range $L\in[0,v_i-v^B_p]$ (p.15), and $\hat L(e)=v_i(v^G_p-v^B_p)/v^G_p$ (p.36).
--
--   These objects are the primitives of every statement of the mission.
--
--   **Formalization Note** Beliefs are log-odds throughout. The page's $\mu'_2$ and the roots $R_{1,2}$ are not defined in the paper; $\lambda_n$ is their value derived from the model. The page's discount rate allows $r=0$, at which every value is undefined; $r>0$ is assumed.
-- source:
--   Henry–Loseto–Ottaviani, working paper (Nov. 2018): §2 Model, pp.7–8, display (1); §3.1, p.9; Proof of Proposition 1, Step 1, p.33; §5, p.15 (liability range); Proof of Proposition 2, Step 3, p.36 (L̂)

import Mathlib

namespace RegExperiment

/-- The primitives of the model of Henry–Loseto–Ottaviani, *Regulation with Experimentation:
Ex Ante Approval, Ex Post Withdrawal, and Liability*, working paper (Nov. 2018), §2 "Model",
pp.7–8.

* `vG > 0`, `vB < 0`: the planner's (social) flow payoffs `v^G_p`, `v^B_p` in the good and the
  bad state while the product is on the market (p.8: "`v^G_p ≥ v_i > 0` in the good state and
  `v^B_p < 0` in the bad state");
* `c > 0`: the cost of ex ante experimentation per unit of time (p.7; positivity as in fn.39,
  p.37, "research cost `c > 0`");
* `r > 0`: the common discount rate (p.8);
* `μ₁, μ₂ > 0`: the drift magnitudes of the signal `dΣ` in the ex ante (`n = 1`) and the ex post
  (`n = 2`) phase (drift `+μ_n` in state G, `−μ_n` in state B, p.8);
* `ρ > 0`: the standard deviation of the signal (variance `ρ²`, p.8).

**Formalization Note** The page writes `r ≥ 0`, but every value of the model divides by `r`
(`v/r`, `c/r`), so `r = 0` is undefined and excluded. -/
structure Params where
  vG : ℝ
  vB : ℝ
  c : ℝ
  r : ℝ
  μ₁ : ℝ
  μ₂ : ℝ
  ρ : ℝ
  vG_pos : 0 < vG
  vB_neg : vB < 0
  c_pos : 0 < c
  r_pos : 0 < r
  μ₁_pos : 0 < μ₁
  μ₂_pos : 0 < μ₂
  ρ_pos : 0 < ρ

/-- The state of the world: good `G` or bad `B` (p.7). -/
inductive State where
  | G
  | B
  deriving DecidableEq

/-- The speed of learning in the ex ante phase, `λ₁ = 2μ₁²/ρ²`: in log-odds the belief
`σ = log(q/(1−q))` (display (1), p.8) moves with drift `±λ₁` and variance `2λ₁`.

**Formalization Note** The page leaves the parameter of the ex ante roots `R₁, R₂` undefined
(fn.37, p.34); this is its value derived from the model of p.8. -/
noncomputable def lam₁ (P : Params) : ℝ := 2 * P.μ₁ ^ 2 / P.ρ ^ 2

/-- The speed of learning in the ex post phase, `λ₂ = 2μ₂²/ρ²` (the page's `μ'₂`, Proof of
Proposition 1, Step 1, p.33). -/
noncomputable def lam₂ (P : Params) : ℝ := 2 * P.μ₂ ^ 2 / P.ρ ^ 2

/-- `r₁ = ½(1 − √(1 + 4r/λ₂)) < 0` (Proof of Proposition 1, Step 1, p.33). -/
noncomputable def r1 (P : Params) : ℝ := (1 - Real.sqrt (1 + 4 * P.r / lam₂ P)) / 2

/-- `r₂ = ½(1 + √(1 + 4r/λ₂)) > 0` (Proof of Proposition 1, Step 1, p.33). -/
noncomputable def r2 (P : Params) : ℝ := (1 + Real.sqrt (1 + 4 * P.r / lam₂ P)) / 2

/-- `R₁ = ½(1 − √(1 + 4r/λ₁)) < 0`, the ex ante analogue of `r₁` (fn.37, p.34). -/
noncomputable def R1 (P : Params) : ℝ := (1 - Real.sqrt (1 + 4 * P.r / lam₁ P)) / 2

/-- `R₂ = ½(1 + √(1 + 4r/λ₁)) > 1`, the ex ante analogue of `r₂` (fn.37, p.34). -/
noncomputable def R2 (P : Params) : ℝ := (1 + Real.sqrt (1 + 4 * P.r / lam₁ P)) / 2

/-- The firm's flow payoff `v_i = (1 − e) v^G_p` at externality rate `e` (p.8). -/
def vi (P : Params) (e : ℝ) : ℝ := (1 - e) * P.vG

/-- Strong liability `L̄ = v_i − v^B_p`, the upper end of the liability range
`L ∈ [0, v_i − v^B_p]` (§5, p.15). -/
def Lbar (P : Params) (e : ℝ) : ℝ := vi P e - P.vB

/-- `L̂ = v_i (v^G_p − v^B_p) / v^G_p`, the liability under which the firm's own withdrawal
standard equals `z*` (Proof of Proposition 2, Step 3, p.36). -/
noncomputable def Lhat (P : Params) (e : ℝ) : ℝ := vi P e * (P.vG - P.vB) / P.vG

/-- The probability of the good state at log-odds belief `σ`: `e^σ/(1 + e^σ)` (inverse of (1),
p.8). -/
noncomputable def piG (σ : ℝ) : ℝ := Real.exp σ / (1 + Real.exp σ)

/-- The probability of the bad state at log-odds belief `σ`: `1/(1 + e^σ)`. -/
noncomputable def piB (σ : ℝ) : ℝ := 1 / (1 + Real.exp σ)

/-- The expected discounted probability `ψ(S, θ, z) = E[e^{−rτ} | θ, S]` of reaching the
withdrawal standard `z` in state `θ` in the ex post phase, starting from the adoption belief `S`
(Proof of Proposition 1, Step 1, p.33): `ψ(S, G, z) = e^{−r₂(S−z)}`, `ψ(S, B, z) = e^{r₁(S−z)}`.

**Formalization Note** The page's formulas are for `z ≤ S`. For `S < z` the product is withdrawn
at once, so the value is `1`; both formulas also give `1` at `S = z`. -/
noncomputable def psiPost (P : Params) : State → ℝ → ℝ → ℝ
  | .G, S, z => if S < z then 1 else Real.exp (-(r2 P) * (S - z))
  | .B, S, z => if S < z then 1 else Real.exp (r1 P * (S - z))

/-- The state-conditional ex post value `u²(S, θ, z) = (a_θ/r)(1 − ψ(S, θ, z))` of a player with
flow payoff `a_θ` in state `θ`, adoption at belief `S` and withdrawal at standard `z`
(Proof of Proposition 1, Step 1, p.33, and Step 2, p.34). -/
noncomputable def u2 (P : Params) (aθ : ℝ) (θ : State) (S z : ℝ) : ℝ :=
  aθ / P.r * (1 - psiPost P θ S z)

/-- The ex post value of a player with flow payoffs `a = (a_G, a_B)` who adopts at belief `S`
under withdrawal standard `z` (§3.1, p.9, and Proof of Proposition 1, Step 1, p.33):
`u²(S, z) = e^S/(1+e^S)·(a_G/r)(1 − ψ(S,G,z)) + 1/(1+e^S)·(a_B/r)(1 − ψ(S,B,z))`. -/
noncomputable def U2 (P : Params) (a : ℝ × ℝ) (S z : ℝ) : ℝ :=
  piG S * u2 P a.1 .G S z + piB S * u2 P a.2 .B S z

/-- The planner's optimal withdrawal standard `z* = −ln(v^G_p r₂ / (v^B_p r₁))` (Proof of
Proposition 1, Step 1, p.33). The argument of the logarithm is positive, since `v^G_p > 0`,
`r₂ > 0`, `v^B_p < 0` and `r₁ < 0`. -/
noncomputable def zstar (P : Params) : ℝ := -Real.log (P.vG * r2 P / (P.vB * r1 P))

end RegExperiment


