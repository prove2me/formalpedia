-- Prove2me | Definitions.Def_ProdHedgeCVaR_Joint_Model
-- name    : ProdHedgeCVaR_Joint_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:23.12773+00:00
-- url     : https://prove2.me/theorems/beeb1a93-15f5-4990-a90e-d3c1f2c3cb01
-- title:
--   §§3–5, pp. 10–20 — terminal-time model, static hedging problem (28), s(m, Q), D̂_T (30), V*_T (33)–(35), β, ψ, ∆, 𝒟, problem (36), (45), C° (46), m° (50), (53)
-- statement:
--   This module fixes the objects of §§3–5 of Wang and Yao, *Production Planning with Risk Hedging under a CVaR Objective*, at the horizon $T$.
--
--   1. **Parameters.** Unit profit $p$ and net unit cost $c$ (p. 5), demand-noise volatility $\tilde\sigma$, horizon $T$, market price of risk $\eta=\mu/\sigma$, hedging budget $C$; valid parameters have $p,c,\tilde\sigma,T,C>0$ and $\eta\ne0$.
--   2. **Model.** A probability measure $\mathbb P$ on $\Omega$, a sub-σ-algebra $\mathcal G$ (the hedger's information, the paper's $\sigma(A_T,X_T)$), and random variables $A_T\ge0$ and $W=B_T$, both $\mathcal G$-measurable, with $W\sim N(0,T)$, and $\xi\sim N(0,1)$ independent of $\mathcal G$ (so that $\tilde B_T=\sqrt T\xi$).
--   3. **Derived quantities.** $Z_T=e^{-\eta W-\eta^2T/2}$ (26); $D_T=A_T+\tilde\sigma\sqrt T\,\xi$ and $H_T(Q)=pQ-(p+c)(Q-D_T^+)^+$ (19); $\mathsf E^M[Y]=\mathsf E[Z_TY]$ and $\mathsf P^M(S)=\mathsf E[Z_T\mathbf 1_S]$.
--   4. **The static hedging problem (28).** A payoff $V$ is feasible if it is $\mathcal G$-measurable, $V\ge-C$, $Z_TV$ is integrable and $\mathsf E^M[V]\le0$. The shortfall is $\mathsf E[(m-H_T(Q)-V)^+]$ and
--   $$s(m,Q)=\inf\{\mathsf E[(m-H_T(Q)-V)^+] : V \text{ feasible}\},$$
--   the optimal value of (28) (the set is nonempty, $V\equiv-C$ being feasible, and bounded below by $0$).
--   5. **Theorem 1 objects.** $\Phi^{-1}$ is the order inverse of the standard normal CDF $\Phi$, with $\Phi^{-1}(u)=-\infty$ for $u\le0$ and $+\infty$ for $u\ge1$. $\hat D_T(\lambda)=A_T+\tilde\sigma\sqrt T\,\Phi^{-1}(\lambda Z_T)$ in the extended reals, so $\hat D_T=+\infty$ when $\lambda Z_T\ge1$ (30). $K=(m+C+cQ)/(p+c)$,
--   $$V_T^*=(p+c)\big[(K-Q)\mathbf 1\{\lambda Z_T\le1\}+(Q-\hat D_T^+)^+\big]-C\quad(33),$$
--   equation (35) $(p+c)\big[(K-Q)\mathsf P^M(\lambda Z_T\le1)+\mathsf E^M[(Q-\hat D_T^+(\lambda))^+]\big]=C$ with $\lambda\ge0$, and the right-hand side of (34), $(p+c)\big[(K-Q)\mathsf P(\lambda Z_T\ge1)+\mathsf E[(Q\wedge\hat D_T^+-D_T^+)^+]\big]$.
--   6. **§5 objects.** $\beta=\mathsf E[(1-\lambda Z_T)^+]$, $\psi=\mathsf E[(\lambda Z_T-1)^+]$ (37); $\Delta(Q)=\Phi\big((Q-A_T)/(\tilde\sigma\sqrt T)\big)$ (29); $\mathcal D=\{D_T\le Q\wedge\hat D_T\}$; the feasible set $\{m\ge0,\,Q\ge0,\,m-pQ+C\ge0\}$ and objective $m-s(m,Q)/(1-\alpha)$ of (36) and its optimal points; the optimality equations (45) $\beta=\alpha$ and $(p+c)\mathsf E[(\lambda Z_T)\wedge\Delta(Q)]=p(1-\alpha)$; $C^\circ=(p+c)\mathsf E^M[(Q^\circ-\hat D_T^+(\lambda^\circ))^+]$ (46); $m^\circ=p(Q^\circ)^+-C+(C-C^\circ)/\mathsf P^M(\lambda^\circ Z_T\le1)$ (50); and equation (53) $(p+c)\mathsf E^M[(Q-\hat D_T^+(\lambda))^+]=C$.
--
--   These are the objects in which Theorems 1 and 2 and the results of §5 are stated.
--
--   **Formalization Note** The dynamic model (GBM asset, demand diffusion, hedging integrals) is replaced by its terminal values, and the information σ-algebra is any $\mathcal G$ carrying $A_T$ and $B_T$ with $\xi$ independent of it; the paper's $\sigma(A_T,X_T)$ is an instance. $s$ is defined as the value of (28), never by the closed form (34), which is the content of Theorem 1. $\Phi$ is the published `BlackScholesModel.stdNormalCDF`. $(Q-\hat D_T^+)^+$ and $Q\wedge\hat D_T^+$ are computed in the extended reals and are finite. $C^\circ$ and $m^\circ$ are defined as functions of $(\lambda,Q)$ and evaluated at $(\lambda^\circ,Q^\circ)$ in the theorems.
-- source:
--   Wang, Yao, Production Planning with Risk Hedging under a CVaR Objective, SSRN 3875464 (April 2020), pp. 5, 10–20, (1)–(2), (17)–(19), (26), (28)–(30), (33)–(37), (45), (46), (50), (53), Lemma 5

import Mathlib
import Definitions.Def_BlackScholesModel_Core

namespace ProdHedgeCVaR.Joint

open MeasureTheory ProbabilityTheory BlackScholesModel

/-- Parameters of Wang–Yao (SSRN 3875464, April 2020): unit profit `p` and net unit cost `c`
(§2, p. 5, (1)–(2)), demand-noise volatility `sigT` = σ̃ (18), horizon `T` (p. 5), market price of
risk `eta` = η = µ/σ (17), and hedging budget `C` (21). -/
structure Params where
  p : ℝ
  c : ℝ
  sigT : ℝ
  T : ℝ
  eta : ℝ
  C : ℝ

/-- Standing assumptions on the parameters: p, c, σ̃, T, C > 0 (§§2–3) and η ≠ 0 (p. 13). -/
structure Params.Valid (θ : Params) : Prop where
  p_pos : 0 < θ.p
  c_pos : 0 < θ.c
  sigT_pos : 0 < θ.sigT
  T_pos : 0 < θ.T
  eta_ne : θ.eta ≠ 0
  C_pos : 0 < θ.C

/-- The model at the horizon `T`: a probability measure `P`, the hedger's information `G`
(the paper's σ(A_T, X_T)), `A` = A_T, `W` = B_T and `xi` = B̃_T / √T (§3, pp. 10–12). -/
structure Model (Ω : Type*) [MeasurableSpace Ω] where
  θ : Params
  P : Measure Ω
  G : MeasurableSpace Ω
  A : Ω → ℝ
  W : Ω → ℝ
  xi : Ω → ℝ

/-- Standing assumptions on the model: `P` is a probability measure; `G` is a sub-σ-algebra;
`A ≥ 0` and `W` are `G`-measurable; `W ~ N(0, T)`; `xi ~ N(0, 1)` is independent of `G`. -/
structure Model.Valid {Ω : Type*} [mΩ : MeasurableSpace Ω] (M : Model Ω) : Prop where
  params : M.θ.Valid
  isProb : IsProbabilityMeasure M.P
  G_le : M.G ≤ mΩ
  A_meas : Measurable[M.G] M.A
  W_meas : Measurable[M.G] M.W
  A_nonneg : ∀ ω, 0 ≤ M.A ω
  W_law : M.P.map M.W = gaussianReal 0 M.θ.T.toNNReal
  xi_meas : Measurable M.xi
  xi_law : M.P.map M.xi = gaussianReal 0 1
  xi_indep : Indep (MeasurableSpace.comap M.xi inferInstance) M.G M.P

/-- Φ⁻¹ on (0, 1) as the order inverse of the standard normal CDF Φ = `stdNormalCDF`
(Φ is continuous and strictly increasing onto (0, 1)); its value outside (0, 1) is not used. -/
noncomputable def stdNormalInv (u : ℝ) : ℝ :=
  sSup {x : ℝ | stdNormalCDF x ≤ u}

/-- Φ⁻¹ with the paper's endpoint conventions (p. 15): Φ⁻¹(u) = −∞ for u ≤ 0, +∞ for u ≥ 1. -/
noncomputable def stdNormalInvE (u : ℝ) : EReal :=
  if u ≤ 0 then ⊥ else if 1 ≤ u then ⊤ else ((stdNormalInv u : ℝ) : EReal)

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω)

/-- Radon–Nikodym density (26): Z_T = dP^M/dP = exp(−η B_T − η² T / 2). -/
noncomputable def Z (ω : Ω) : ℝ :=
  Real.exp (-M.θ.eta * M.W ω - M.θ.eta ^ 2 * M.θ.T / 2)

/-- Terminal demand (19): D_T = A_T + σ̃ B̃_T = A_T + σ̃ √T ξ. -/
noncomputable def D (ω : Ω) : ℝ :=
  M.A ω + M.θ.sigT * Real.sqrt M.θ.T * M.xi ω

/-- Production payoff (19): H_T(Q) = pQ − (p + c)(Q − D_T⁺)⁺. -/
noncomputable def H (Q : ℝ) (ω : Ω) : ℝ :=
  M.θ.p * Q - (M.θ.p + M.θ.c) * max (Q - max (M.D ω) 0) 0

/-- Expectation under the martingale measure: E^M[Y] = E[Z_T Y]. -/
noncomputable def EM (Y : Ω → ℝ) : ℝ :=
  ∫ ω, M.Z ω * Y ω ∂M.P

/-- Probability under the martingale measure: P^M(S) = E[Z_T 1_S]. -/
noncomputable def PM (S : Set Ω) : ℝ :=
  ∫ ω in S, M.Z ω ∂M.P

/-- Feasible terminal hedging payoffs of (28), p. 14: `V` is a function of the hedger's
information `G`, `V ≥ −C`, and E^M(V) ≤ 0 (with `Z V` integrable, so that E^M(V) is defined). -/
def Feasible (V : Ω → ℝ) : Prop :=
  Measurable[M.G] V ∧ (∀ ω, -M.θ.C ≤ V ω) ∧ Integrable (fun ω => M.Z ω * V ω) M.P ∧ M.EM V ≤ 0

/-- The shortfall E[(m − H_T(Q) − V)⁺], the objective of (28). -/
noncomputable def shortfall (m Q : ℝ) (V : Ω → ℝ) : ℝ :=
  ∫ ω, max (m - M.H Q ω - V ω) 0 ∂M.P

/-- s(m, Q): the optimal value of the static hedging problem (28), the infimum of the shortfall
over feasible payoffs. (The set is nonempty, V ≡ −C being feasible, and bounded below by 0, so
`sInf` is the true infimum.) It is the value function, not the closed form (34). -/
noncomputable def s (m Q : ℝ) : ℝ :=
  sInf (M.shortfall m Q '' {V | M.Feasible V})

/-- D̂_T(λ) of (30), p. 15, in `EReal`: A_T + σ̃√T Φ⁻¹(λZ_T) when 0 < λZ_T < 1, `+∞` when
λZ_T ≥ 1, and `−∞` when λZ_T ≤ 0 (Φ⁻¹(0) = −∞). -/
noncomputable def Dhat (lam : ℝ) (ω : Ω) : EReal :=
  if lam * M.Z ω ≤ 0 then ⊥
  else if 1 ≤ lam * M.Z ω then ⊤
  else ((M.A ω + M.θ.sigT * Real.sqrt M.θ.T * stdNormalInv (lam * M.Z ω) : ℝ) : EReal)

/-- D̂_T⁺ = max(D̂_T, 0), in `EReal`. -/
noncomputable def DhatPos (lam : ℝ) (ω : Ω) : EReal :=
  max (M.Dhat lam ω) 0

/-- (Q − D̂_T⁺)⁺, the put payoff with strike Q (finite: it lies in [0, max(Q, 0)]). -/
noncomputable def putHat (lam Q : ℝ) (ω : Ω) : ℝ :=
  (max ((Q : EReal) - M.DhatPos lam ω) 0).toReal

/-- Q ∧ D̂_T⁺ (finite, since Q is). -/
noncomputable def capHat (lam Q : ℝ) (ω : Ω) : ℝ :=
  (min (Q : EReal) (M.DhatPos lam ω)).toReal

/-- K := (m + C + cQ)/(p + c), (33). -/
noncomputable def K (m Q : ℝ) : ℝ :=
  (m + M.θ.C + M.θ.c * Q) / (M.θ.p + M.θ.c)

/-- The candidate optimal payoff (33): V*_T = (p + c)[(K − Q)1{λZ_T ≤ 1} + (Q − D̂_T⁺)⁺] − C. -/
noncomputable def Vstar (m Q lam : ℝ) (ω : Ω) : ℝ :=
  (M.θ.p + M.θ.c) * ((M.K m Q - Q) * (if lam * M.Z ω ≤ 1 then 1 else 0) + M.putHat lam Q ω)
    - M.θ.C

/-- Equation (35) for the multiplier λ ≥ 0:
(p + c)[(K − Q)P^M(λZ_T ≤ 1) + E^M[(Q − D̂_T⁺(λ))⁺]] = C. -/
def Eq35 (m Q lam : ℝ) : Prop :=
  0 ≤ lam ∧
    (M.θ.p + M.θ.c) * ((M.K m Q - Q) * M.PM {ω | lam * M.Z ω ≤ 1} + M.EM (M.putHat lam Q))
      = M.θ.C

/-- The right-hand side of (34): (p + c)[(K − Q)P(λZ_T ≥ 1) + E[(Q ∧ D̂_T⁺ − D_T⁺)⁺]]. -/
noncomputable def formula34 (m Q lam : ℝ) : ℝ :=
  (M.θ.p + M.θ.c) * ((M.K m Q - Q) * M.P.real {ω | 1 ≤ lam * M.Z ω}
    + ∫ ω, max (M.capHat lam Q ω - max (M.D ω) 0) 0 ∂M.P)

/-- β := E[(1 − λZ_T)⁺], (37). -/
noncomputable def beta (lam : ℝ) : ℝ :=
  ∫ ω, max (1 - lam * M.Z ω) 0 ∂M.P

/-- ψ := E[(λZ_T − 1)⁺], (37). -/
noncomputable def psi (lam : ℝ) : ℝ :=
  ∫ ω, max (lam * M.Z ω - 1) 0 ∂M.P

/-- ∆(Q) := Φ((Q − A_T)/(σ̃√T)), (29). -/
noncomputable def Delta (Q : ℝ) (ω : Ω) : ℝ :=
  stdNormalCDF ((Q - M.A ω) / (M.θ.sigT * Real.sqrt M.θ.T))

/-- 𝒟 := {D_T ≤ Q ∧ D̂_T} (Lemma 5, p. 17), compared in `EReal`. -/
def Dset (lam Q : ℝ) : Set Ω :=
  {ω | ((M.D ω : ℝ) : EReal) ≤ min (Q : EReal) (M.Dhat lam ω)}

/-- The feasible set of (36): m ≥ 0, Q ≥ 0, m − pQ + C ≥ 0; a point is `x = (m, Q)`. -/
def Feasible36 (x : ℝ × ℝ) : Prop :=
  0 ≤ x.1 ∧ 0 ≤ x.2 ∧ 0 ≤ x.1 - M.θ.p * x.2 + M.θ.C

/-- The objective of (36): m − s(m, Q)/(1 − α). -/
noncomputable def obj (α : ℝ) (x : ℝ × ℝ) : ℝ :=
  x.1 - M.s x.1 x.2 / (1 - α)

/-- `x` is an optimal solution of (36). -/
def IsOptimal36 (α : ℝ) (x : ℝ × ℝ) : Prop :=
  M.Feasible36 x ∧ ∀ y, M.Feasible36 y → M.obj α y ≤ M.obj α x

/-- The first optimality equation of (45): β(λ) = α (it defines λ°). -/
def IsLamC (α lam : ℝ) : Prop :=
  M.beta lam = α

/-- The second optimality equation of (45) (equally of (52)): (p + c)E[(λZ_T) ∧ ∆(Q)] = p(1 − α). -/
def IsQC (α lam Q : ℝ) : Prop :=
  (M.θ.p + M.θ.c) * ∫ ω, min (lam * M.Z ω) (M.Delta Q ω) ∂M.P = M.θ.p * (1 - α)

/-- C° := (p + c)E^M[(Q − D̂_T⁺(λ))⁺], (46), evaluated at (λ, Q) = (λ°, Q°). -/
noncomputable def CC (lam Q : ℝ) : ℝ :=
  (M.θ.p + M.θ.c) * M.EM (M.putHat lam Q)

/-- m° := p Q⁺ − C + (C − C°)/P^M(λZ_T ≤ 1), (50), evaluated at (λ, Q) = (λ°, Q°). -/
noncomputable def mC (lam Q : ℝ) : ℝ :=
  M.θ.p * max Q 0 - M.θ.C + (M.θ.C - M.CC lam Q) / M.PM {ω | lam * M.Z ω ≤ 1}

/-- Equation (53): (p + c)E^M[(Q − D̂_T⁺(λ))⁺] = C. -/
def Eq53 (lam Q : ℝ) : Prop :=
  (M.θ.p + M.θ.c) * M.EM (M.putHat lam Q) = M.θ.C

end Model

end ProdHedgeCVaR.Joint


