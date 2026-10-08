-- Prove2me | Definitions.Def_MFGLiquidation_Equilibrium_Setting
-- name    : MFGLiquidation_Equilibrium_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:00.492031+00:00
-- url     : https://prove2.me/theorems/dcde305a-2872-4bcc-be69-f9d987e8f5a2
-- title:
--   Liquidation MFG setting: W̃ = (W⁰, W), 𝒳, filtrations 𝔽⁰ ⊂ 𝔽, Assumption 2.3, the spaces of §1.2.2 and Definition 2.1, the Riccati BSDE and the FBSDE (2.3)
-- statement:
--   Fix a horizon $T>0$ and a probability space $(\Omega,\mathcal G,\mathbb P)$ carrying an $m$-dimensional standard Brownian motion $\widetilde W=(W^0,W)$, where $W^0$ (coordinate $0$) is one-dimensional and $W$ (the other $m-1=k$ coordinates) is independent of $W^0$, and a real random variable $\mathcal X$ (the initial portfolio) independent of the whole path of $\widetilde W$. The **common-noise filtration** is $\mathbb F^0=(\mathcal F^0_t)$ with $\mathcal F^0_t=\sigma(W^0_s,\ s\le t)$, and the **full filtration** is $\mathbb F=(\mathcal F_t)$ with $\mathcal F_t=\sigma(\mathcal X, W^0_s, W_s,\ s\le t)$; both are augmented by the null sets. The cost coefficients are processes $\kappa$ (interaction), $\lambda$ (risk aversion) and $\eta$ (temporary price impact).
--
--   **Assumption 2.3.** (i) $\kappa,\lambda,\eta$ are $\mathbb F$-progressively measurable, nonnegative and essentially bounded on $[0,T]\times\Omega$; $1/\lambda$ and $1/\eta$ are bounded, i.e. $\lambda,\eta\ge c>0$ a.e.; $\mathcal X\in L^2(\Omega)$. (ii) There is $\theta>0$ with
--   $$\frac{\kappa_{\max}}{4\eta_\star}<\theta<4\frac{\lambda_\star}{\kappa_{\max}},$$
--   where $\kappa_{\max}=\operatorname{ess\,sup}\kappa$, $\eta_\star=\operatorname{ess\,inf}\eta$, $\lambda_\star=\operatorname{ess\,inf}\lambda$, all with respect to $dt\otimes d\mathbb P$ on $[0,T]\times\Omega$. One sets $\alpha:=\eta_\star/\|\eta\|$ with $\|\eta\|=\operatorname{ess\,sup}|\eta|$.
--
--   **Spaces.** For a filtration $\mathbb G$: $L^2_{\mathbb G}([0,T])$ (progressive, $\mathbb E\int_0^T|u_t|^2dt<\infty$); $S^2_{\mathbb G}([0,T])$ (progressive, $\mathbb E\sup_{t\le T}|u_t|^2<\infty$); $S^2_{\mathbb G}([0,T-])$ and $L^2_{\mathbb G}([0,T-])$ (the same property on every $[0,\tau]$, $\tau<T$); $D^2_{\mathbb G}=L^2_{\mathbb G}([0,T])\cap S^2_{\mathbb G}([0,T-])$. For $l\in\mathbb R$ (Definition 2.1),
--   $$\|Y\|_{\mathcal H_l}^2=\mathbb E\Big[\sup_{0\le t\le T}\Big|\frac{Y_t}{(T-t)^l}\Big|^2\Big],\qquad \|Y\|_{\mathcal M_l}=\operatorname*{ess\,sup}_{(t,\omega)\in[0,T]\times\Omega}\frac{|Y_t|}{(T-t)^l},$$
--   and $\mathcal H_l$, $\mathcal M_l$ are the progressive processes with finite norm.
--
--   **Equations.** A scalar BSDE $-dy_t=F(t,y_t,z_t)\,dt-z_t\,d\widetilde W_t$ on $[0,\tau]$ means $y_t=y_\tau+\int_t^\tau F\,ds-\sum_j\int_t^\tau z^j\,d\widetilde W^j$ a.s. for each $t\le\tau$, with $y,z^j\in L^2([0,\tau])$. The **singular Riccati BSDE** (Lemma A.1) asks for $A\in S^2_{\mathbb F}([0,T-])$, $Z^A\in L^2_{\mathbb F}([0,T-];\mathbb R^m)$ with
--   $$-dA_t=\Big(2\lambda_t-\frac{A_t^2}{2\eta_t}\Big)dt-Z^A_t\,d\widetilde W_t\ \text{ on every }[0,\tau],\ \tau<T,\qquad A_t\to+\infty\ (t\uparrow T)\text{ a.s.}$$
--   The **conditional mean-field FBSDE (2.3)** asks for $(X,Y,Z)$ with
--   $$X_t=\mathcal X-\int_0^t\frac{Y_s}{2\eta_s}ds\ (t\le T),\quad X_T=0,\quad -dY_t=\Big(\kappa_t\,\mathbb E\Big[\frac{Y_t}{2\eta_t}\Big|\mathcal F^0_t\Big]+2\lambda_tX_t\Big)dt-Z_t\,d\widetilde W_t\ \text{ on }[0,T).$$
--
--   These objects are the common language of every statement of the mission.
--
--   **Formalization Note** Time is `ℝ≥0`, $m=k+1$, $\lambda$ is named `lam`. Augmentation adds the measurable null sets (Mathlib σ-algebras are not completed). $\kappa_{\max},\eta_\star,\lambda_\star,\|\eta\|$ are essential bounds over $dt\otimes d\mathbb P$ (the paper's notation section, p. 6), and (2.4) is written without division, $\kappa_{\max}<4\eta_\star\theta$ and $\theta\kappa_{\max}<4\lambda_\star$, which agrees with the printed form when $\kappa_{\max}>0$ and stays meaningful when $\kappa_{\max}=0$. "$1/\lambda,1/\eta\in L^\infty$" is stated as positive essential lower bounds (Lean has $1/0=0$). Norms are computed in $[0,\infty]$ with the weight $(T-t)^{-l}$ in `ℝ≥0∞`, so for $l>0$ finiteness of $\|Y\|_{\mathcal H_l}$ forces $Y_T=0$ a.s., as the paper's convention with values in $\mathbb R\cup\{\infty\}$ does. Backward equations "on $[0,T)$" are imposed on every $[0,\tau]$, $\tau<T$, with terminal value $Y_\tau$. Processes are real valued: $A_T=\infty$ is encoded as $\lim_{t\uparrow T}A_t=+\infty$ a.s., which is what p. 9 states. The conditional expectation $\mathbb E[Y_t/(2\eta_t)\mid\mathcal F^0_t]$ in a driver is evaluated through an $\mathbb F^0$-progressive process $\mu$ that equals it a.s. for a.e. $t$ (`IsCondExpVersion`, which also requires the integrability of $Y_t/(2\eta_t)$); any two such versions agree $dt\otimes d\mathbb P$-a.e., so the equations do not depend on the choice.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, pp. 2 (footnote 1), 4–9, §1.2.1, §1.2.2, (2.3), Definition 2.1, Assumption 2.3, (2.5), (2.8); p. 31, Lemma A.1

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

/-- The data of the representative player's problem (§1.2.1, pp. 4–5): horizon `T`, the
`m = k + 1`-dimensional Brownian motion `W̃ = (W⁰, W)` (coordinate `0` is the common noise `W⁰`,
coordinates `1, …, k` are the idiosyncratic `W`), the initial portfolio `𝒳`, and the cost
coefficients `κ` (interaction), `lam` (risk aversion `λ`), `η` (temporary impact). -/
structure Data (Ω : Type*) [MeasurableSpace Ω] (k : ℕ) where
  T : ℝ≥0
  W : ℝ≥0 → Ω → Fin (k + 1) → ℝ
  𝒳 : Ω → ℝ
  κ : ℝ≥0 → Ω → ℝ
  lam : ℝ≥0 → Ω → ℝ
  η : ℝ≥0 → Ω → ℝ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}

/-- Standing structure of §1.2.1: `T > 0`, `W̃` a standard `m`-dimensional Brownian motion
(independent coordinates, so `W⁰` and `W` are independent), `𝒳` a random variable independent
of the whole path of `W̃`. -/
structure Data.Standing (D : Data Ω k) (P : Measure Ω) : Prop where
  T_pos : 0 < D.T
  brownian : IsStdBrownian P D.W
  init_meas : Measurable D.𝒳
  init_indep : IndepFun D.𝒳 (fun ω t => D.W t ω) P

/-- The σ-field generated by the measurable `P`-null sets (used to augment filtrations,
footnote 1, p. 2). -/
abbrev nullSigma (P : Measure Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {N | MeasurableSet N ∧ P N = 0}

lemma nullSigma_le (P : Measure Ω) : nullSigma P ≤ mΩ :=
  MeasurableSpace.generateFrom_le fun _ hN => hN.1

/-- The common-noise filtration `𝔽⁰`, `𝓕⁰_t = σ(W⁰_s, s ≤ t)`, augmented by the null sets. -/
noncomputable def filtF0 {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) :
    Filtration ℝ≥0 mΩ where
  seq t := Filtration.natural (fun t ω => D.W t ω 0)
      (fun t => ((measurable_pi_apply 0).comp (hD.brownian.meas t)).stronglyMeasurable) t ⊔
    nullSigma P
  mono' _ _ hst := sup_le_sup_right (Filtration.mono _ hst) _
  le' t := sup_le (Filtration.le _ t) (nullSigma_le P)

/-- The full filtration `𝔽`, `𝓕_t = σ(𝒳, W⁰_s, W_s, s ≤ t)`, augmented by the null sets. -/
noncomputable def filtF {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) :
    Filtration ℝ≥0 mΩ where
  seq t := MeasurableSpace.comap D.𝒳 inferInstance ⊔ brownianFiltration hD.brownian t ⊔
    nullSigma P
  mono' _ _ hst :=
    sup_le_sup_right (sup_le_sup_left ((brownianFiltration hD.brownian).mono hst) _) _
  le' t := sup_le (sup_le hD.init_meas.comap_le ((brownianFiltration hD.brownian).le t))
    (nullSigma_le P)

/-- The product measure `dt ⊗ dP` on `[0, T] × Ω` (time read in `ℝ`). -/
noncomputable def dtP (T : ℝ≥0) (P : Measure Ω) [SFinite P] : Measure (ℝ × Ω) :=
  (volume.restrict (Set.Icc (0 : ℝ) T)).prod P

/-- Two processes agree `dt ⊗ dP`-a.e. on `[0, T] × Ω`. -/
def AEEqT (T : ℝ≥0) (P : Measure Ω) [SFinite P] (u v : ℝ≥0 → Ω → ℝ) : Prop :=
  (fun p : ℝ × Ω => u p.1.toNNReal p.2) =ᵐ[dtP T P] (fun p => v p.1.toNNReal p.2)

/-- Essential supremum of a process over `dt ⊗ dP` on `[0, T] × Ω`. -/
noncomputable def esssupT (D : Data Ω k) (P : Measure Ω) [SFinite P] (u : ℝ≥0 → Ω → ℝ) : ℝ :=
  essSup (fun p : ℝ × Ω => u p.1.toNNReal p.2) (dtP D.T P)

/-- Essential infimum of a process over `dt ⊗ dP` on `[0, T] × Ω`. -/
noncomputable def essinfT (D : Data Ω k) (P : Measure Ω) [SFinite P] (u : ℝ≥0 → Ω → ℝ) : ℝ :=
  essInf (fun p : ℝ × Ω => u p.1.toNNReal p.2) (dtP D.T P)

/-- `κ_max := ess sup κ`. -/
noncomputable def Data.kappaMax (D : Data Ω k) (P : Measure Ω) [SFinite P] : ℝ :=
  esssupT D P D.κ

/-- `η_⋆ := ess inf η`. -/
noncomputable def Data.etaLow (D : Data Ω k) (P : Measure Ω) [SFinite P] : ℝ :=
  essinfT D P D.η

/-- `‖η‖ := ess sup |η|`. -/
noncomputable def Data.etaNorm (D : Data Ω k) (P : Measure Ω) [SFinite P] : ℝ :=
  esssupT D P (fun t ω => |D.η t ω|)

/-- `λ_⋆ := ess inf λ`. -/
noncomputable def Data.lamLow (D : Data Ω k) (P : Measure Ω) [SFinite P] : ℝ :=
  essinfT D P D.lam

/-- `α := η_⋆ / ‖η‖`, (2.5). -/
noncomputable def Data.alpha (D : Data Ω k) (P : Measure Ω) [SFinite P] : ℝ :=
  D.etaLow P / D.etaNorm P

/-- Assumption 2.3 (p. 8). (i) `κ, λ, η` are `𝔽`-progressive, nonnegative and essentially
bounded on `[0, T] × Ω`; `1/λ, 1/η` bounded is stated as positive essential lower bounds of
`λ, η`; `𝒳 ∈ L²` (its independence is in `Standing`). (ii) the weak-interaction condition (2.4),
`κ_max/(4η_⋆) < θ < 4λ_⋆/κ_max`, written without division. -/
structure Data.Assumption23 (D : Data Ω k) (P : Measure Ω) [SFinite P] (hD : D.Standing P) :
    Prop where
  prog_κ : IsStronglyProgressive (filtF hD) D.κ
  prog_lam : IsStronglyProgressive (filtF hD) D.lam
  prog_η : IsStronglyProgressive (filtF hD) D.η
  bdd_κ : ∃ c : ℝ, ∀ᵐ p ∂(dtP D.T P), 0 ≤ D.κ p.1.toNNReal p.2 ∧ D.κ p.1.toNNReal p.2 ≤ c
  bdd_lam : ∃ c : ℝ, ∀ᵐ p ∂(dtP D.T P), 0 ≤ D.lam p.1.toNNReal p.2 ∧ D.lam p.1.toNNReal p.2 ≤ c
  bdd_η : ∃ c : ℝ, ∀ᵐ p ∂(dtP D.T P), 0 ≤ D.η p.1.toNNReal p.2 ∧ D.η p.1.toNNReal p.2 ≤ c
  low_lam : ∃ c : ℝ, 0 < c ∧ ∀ᵐ p ∂(dtP D.T P), c ≤ D.lam p.1.toNNReal p.2
  low_η : ∃ c : ℝ, 0 < c ∧ ∀ᵐ p ∂(dtP D.T P), c ≤ D.η p.1.toNNReal p.2
  init_sq : MemLp D.𝒳 2 P
  weak : ∃ θ : ℝ, 0 < θ ∧ D.kappaMax P < 4 * D.etaLow P * θ ∧
    θ * D.kappaMax P < 4 * D.lamLow P

/-- `S²_𝔾([0, T])`: progressive with `E sup_{t ≤ T} |u_t|² < ∞`. -/
def IsS2 (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G u ∧ ∫⁻ ω, ⨆ t ∈ Set.Iic T, ‖u t ω‖ₑ ^ 2 ∂P < ⊤

/-- `S²_𝔾([0, T−])`: progressive with `E sup_{t ≤ τ} |u_t|² < ∞` for every `τ < T`. -/
def IsS2Minus (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G u ∧ ∀ τ < T, ∫⁻ ω, ⨆ t ∈ Set.Iic τ, ‖u t ω‖ₑ ^ 2 ∂P < ⊤

/-- `D²_𝔾([0, T]) := L²_𝔾([0, T]) ∩ S²_𝔾([0, T−])`. -/
def IsD2 (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ) : Prop :=
  L2F G P T u ∧ IsS2Minus G P T u

/-- `L²_𝔾([0, T]; ℝ^m)` for a vector process given by its columns. -/
def IsL2Vec (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (Z : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ j, L2F G P T (Z j)

/-- `L²_𝔾([0, T−]; ℝ^m)`: in `L²_𝔾([0, τ]; ℝ^m)` for every `τ < T`. -/
def IsL2VecMinus (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (Z : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ τ < T, ∀ j, L2F G P τ (Z j)

/-- `‖Y‖²_{ℋ_l} = E[sup_{0 ≤ t ≤ T} |Y_t / (T − t)^l|²]` (Definition 2.1), computed in `[0, ∞]`
with the weight `(T − t)^{−l}` in `ℝ≥0∞` (so `0^{−l} = ∞` for `l > 0`, `= 1` for `l = 0`). -/
noncomputable def hNormSq (T : ℝ≥0) (P : Measure Ω) (l : ℝ) (Y : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (⨆ t ∈ Set.Iic T, ENNReal.ofReal ((T : ℝ) - t) ^ (-l) * ‖Y t ω‖ₑ) ^ 2 ∂P

/-- `ℋ_l` (Definition 2.1): progressive with finite `‖·‖_{ℋ_l}`. -/
def MemH (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (l : ℝ) (Y : ℝ≥0 → Ω → ℝ) :
    Prop :=
  IsStronglyProgressive G Y ∧ hNormSq T P l Y < ⊤

/-- `‖Y‖_{ℳ_l} = ess sup_{(t, ω) ∈ [0, T] × Ω} |Y_t| / (T − t)^l` (Definition 2.1). -/
noncomputable def mNorm (T : ℝ≥0) (P : Measure Ω) [SFinite P] (l : ℝ) (Y : ℝ≥0 → Ω → ℝ) :
    ℝ≥0∞ :=
  essSup (fun p : ℝ × Ω => ENNReal.ofReal ((T : ℝ) - p.1) ^ (-l) * ‖Y p.1.toNNReal p.2‖ₑ)
    (dtP T P)

/-- `ℳ_l` (Definition 2.1): progressive with finite `‖·‖_{ℳ_l}`. -/
def MemM (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) [SFinite P] (T : ℝ≥0) (l : ℝ)
    (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G Y ∧ mNorm T P l Y < ⊤

/-- `(y, z)` solves the scalar BSDE `y_t = ξ + ∫_t^τ F(s, y_s, z_s) ds − Σ_j ∫_t^τ z^j_s dW̃^j_s`
on `[0, τ]` (a wrapper of `Peng1990.SMP.SolvesBSDE` with one component). -/
def SolvesScalarBSDE (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (τ : ℝ≥0)
    (W : ℝ≥0 → Ω → Fin (k + 1) → ℝ) (ξ : Ω → ℝ)
    (F : ℝ≥0 → Ω → ℝ → (Fin (k + 1) → ℝ) → ℝ) (y : ℝ≥0 → Ω → ℝ)
    (z : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  SolvesBSDE (ι := Unit) G P τ W (fun ω _ => ξ ω)
    (fun s ω yv zv _ => F s ω (yv ()) (fun j => zv j ()))
    (fun t ω _ => y t ω) (fun j t ω _ => z j t ω)

/-- `μ` is a `𝔾`-progressive version of `t ↦ E[ξ_t | 𝒢_t]`: for a.e. `t ∈ [0, T]`, `ξ_t` is
integrable and `μ_t = E[ξ_t | 𝒢_t]` a.s. -/
def IsCondExpVersion (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (ξ μ : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G μ ∧
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Integrable (ξ t.toNNReal) P ∧ μ t.toNNReal =ᵐ[P] P[ξ t.toNNReal | G t.toNNReal]

/-- `(A, Z^A)` solves the singular stochastic Riccati BSDE of Lemma A.1 (first equation of
(2.8)): `A ∈ S²_𝔽([0, T−])`, `Z^A ∈ L²_𝔽([0, T−]; ℝ^m)`,
`−dA_t = (2λ_t − A_t²/(2η_t)) dt − Z^A_t dW̃_t` on every `[0, τ]`, `τ < T`, and
`A_t → +∞` as `t ↑ T` a.s. (the terminal condition `A_T = ∞`). -/
def IsSingularRiccati {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  IsS2Minus (filtF hD) P D.T A ∧ IsL2VecMinus (filtF hD) P D.T ZA ∧
    (∀ τ < D.T, SolvesScalarBSDE (filtF hD) P τ D.W (A τ)
      (fun s ω a _ => 2 * D.lam s ω - a ^ 2 / (2 * D.η s ω)) A ZA) ∧
    ∀ᵐ ω ∂P, Tendsto (fun t => A t ω) (𝓝[<] D.T) atTop

/-- `(X, Y, Z)` solves the conditional mean-field FBSDE (2.3):
`X_t = 𝒳 − ∫_0^t Y_s/(2η_s) ds` on `[0, T]`, `X_T = 0`, and on every `[0, τ]`, `τ < T`,
`−dY_t = (κ_t E[Y_t/(2η_t) | 𝓕⁰_t] + 2λ_t X_t) dt − Z_t dW̃_t`, the conditional expectation
being evaluated through an `𝔽⁰`-progressive version `μ`. -/
def SolvesFBSDE23 {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (X Y : ℝ≥0 → Ω → ℝ) (Z : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ∀ t ≤ D.T,
      IntegrableOn (fun s : ℝ => Y s.toNNReal ω / (2 * D.η s.toNNReal ω)) (Set.Icc 0 (t : ℝ)) ∧
      X t ω = D.𝒳 ω - ∫ s in Set.Icc (0 : ℝ) t, Y s.toNNReal ω / (2 * D.η s.toNNReal ω)) ∧
    (∀ᵐ ω ∂P, X D.T ω = 0) ∧
    (∃ μ : ℝ≥0 → Ω → ℝ,
      IsCondExpVersion (filtF0 hD) P D.T (fun t ω => Y t ω / (2 * D.η t ω)) μ ∧
      ∀ τ < D.T, SolvesScalarBSDE (filtF hD) P τ D.W (Y τ)
        (fun s ω _ _ => D.κ s ω * μ s ω + 2 * D.lam s ω * X s ω) Y Z) ∧
    IsStronglyProgressive (filtF hD) X

end MFGLiquidation.Equilibrium


