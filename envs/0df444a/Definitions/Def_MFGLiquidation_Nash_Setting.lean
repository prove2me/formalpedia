-- Prove2me | Definitions.Def_MFGLiquidation_Nash_Setting
-- name    : MFGLiquidation_Nash_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:50.26522+00:00
-- url     : https://prove2.me/theorems/b1f9563f-9b14-4aec-88df-ec21eecd4acd
-- title:
--   Representative player's data, filtrations 𝔽⁰ and 𝔽, Assumption 2.3, the spaces of §1.2.2 and Definition 2.1, and the FBSDE (2.3)
-- statement:
--   This file fixes the single-player setting of the liquidation mean field game of Fu, Graewe, Horst and Popier.
--
--   **Data.** A horizon $T>0$; an $m=k+1$-dimensional Brownian motion $\widetilde W=(W^0,W)$ whose coordinate $0$ is the one-dimensional common noise $W^0$ and whose coordinates $1,\dots,k$ form the private noise $W$; an initial portfolio $\mathcal X$; and three cost coefficients: $\kappa$ (permanent price impact), $\lambda$ (risk aversion) and $\eta$ (temporary price impact). The *standing setting* requires $\widetilde W$ to be a standard Brownian motion with independent coordinates (so $W^0$ and $W$ are independent) and $\mathcal X$ to be measurable and independent of the whole path of $\widetilde W$.
--
--   **Filtrations.** $\mathbb F^0=(\mathcal F^0_t)$ with $\mathcal F^0_t=\sigma(W^0_s,\ s\le t)$ and $\mathbb F=(\mathcal F_t)$ with $\mathcal F_t=\sigma(\mathcal X, W^0_s, W_s,\ s\le t)$, both augmented by the $\mathbb P$-null sets.
--
--   **Essential bounds.** With $dt\otimes d\mathbb P$ on $[0,T]\times\Omega$: $\kappa_{\max}=\operatorname{ess\,sup}\kappa$, $\eta_\star=\operatorname{ess\,inf}\eta$, $\|\eta\|=\operatorname{ess\,sup}|\eta|$, $\lambda_\star=\operatorname{ess\,inf}\lambda$ and $\alpha=\eta_\star/\|\eta\|$.
--
--   **Assumption 2.3.** (i) $\kappa,\lambda,\eta$ are $\mathbb F$-progressively measurable, nonnegative and essentially bounded; $\lambda$ and $\eta$ are essentially bounded below by a positive constant; $\mathcal X\in L^2$. (ii) There is $\theta>0$ with
--   $$\kappa_{\max}<4\eta_\star\theta\qquad\text{and}\qquad \theta\kappa_{\max}<4\lambda_\star .$$
--
--   **Spaces.** $L^2_{\mathbb G}$, $S^2_{\mathbb G}([0,T])$, $S^2_{\mathbb G}([0,T-])$ (in $S^2$ on every $[0,\tau]$, $\tau<T$), $D^2_{\mathbb G}=L^2_{\mathbb G}\cap S^2_{\mathbb G}([0,T-])$, the vector spaces $L^2([0,T])$, $L^2([0,T-])$, and the weighted spaces of Definition 2.1: $\mathcal H_l$ with $\|Y\|_l^2=\mathbb E\sup_{0\le t\le T}|Y_t/(T-t)^l|^2$ and $\mathcal M_l$ with $\|Y\|_{\mathcal M_l}=\operatorname{ess\,sup}_{(t,\omega)}|Y_t|/(T-t)^l$.
--
--   **Equations.** A scalar BSDE $-dy=F(t,y,z)\,dt-z\,d\widetilde W$ on $[0,\tau]$; a progressive version $\mu$ of $t\mapsto\mathbb E[\xi_t\mid\mathcal G_t]$; the singular Riccati BSDE $-dA=(2\lambda-A^2/(2\eta))\,dt-Z^A\,d\widetilde W$ on $[0,T)$ with $A_t\to+\infty$ as $t\uparrow T$ (Lemma A.1); and the conditional mean-field FBSDE (2.3)
--   $$dX_t=-\frac{Y_t}{2\eta_t}\,dt,\qquad -dY_t=\Big(\kappa_t\,\mathbb E\Big[\frac{Y_t}{2\eta_t}\,\Big|\,\mathcal F^0_t\Big]+2\lambda_tX_t\Big)dt-Z_t\,d\widetilde W_t,\qquad X_0=\mathcal X,\ X_T=0,$$
--   the forward equation on $[0,T]$ and the backward one on $[0,T)$. A solution *in the class of Theorem 2.4* additionally has $X\in\mathcal H_\alpha$, $Y\in L^2_{\mathbb F}([0,T])$ and $Z\in L^2_{\mathbb F}([0,T-])$.
--
--   These objects are the substrate of every statement of the mission: each player of the $N$-player game is an instance of this data.
--
--   **Formalization Note.** Time is $\mathbb R_{\ge0}$ and time integrals are over $[0,t]\subset\mathbb R$. The paper writes $\lambda$; Lean uses `lam`. The paper's "$1/\lambda,1/\eta\in L^\infty$" is stated as positive essential lower bounds (Lean has $1/0=0$), and (2.4) is stated without division, which agrees with the printed form when $\kappa_{\max}>0$. Filtrations are augmented by the null sets (footnote 1, p. 2). An equation on $[0,T)$ is imposed on every $[0,\tau]$, $\tau<T$, with terminal value $Y_\tau$, as in Remark 2.10. Norms are computed in $[0,\infty]$; the weight $(T-t)^{-l}$ is computed in $[0,\infty]$, so finiteness of $\|Y\|_l$ with $l>0$ forces $Y_T=0$ a.s., the paper's convention for processes with values in $\mathbb R\cup\{\infty\}$. Each conditional expectation $\mathbb E[\,\cdot\mid\mathcal F^0_t]$ in a driver is evaluated through a progressive version $\mu$ that requires the argument to be integrable for a.e. $t$; any two versions agree $dt\otimes d\mathbb P$-a.e. The process $Y$ is real valued; $A_T=\infty$ is encoded as $\lim_{t\uparrow T}A_t=+\infty$ a.s.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, pp. 4–9, §1.2.1, §1.2.2, (2.3), Definition 2.1, Assumption 2.3, Theorem 2.4; p. 31, Lemma A.1

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

namespace MFGLiquidation.Nash

/-- The data of the representative player's liquidation problem (§1.2.1, pp. 4–5): horizon `T`,
the `m = k + 1`-dimensional Brownian motion `W̃ = (W⁰, W)` (coordinate `0` is the common noise
`W⁰`, coordinates `1, …, k` the private noise `W`), the initial portfolio `𝒳`, and the cost
coefficients `κ` (permanent impact), `lam` (= `λ`, risk aversion) and `η` (temporary impact). -/
structure Data (Ω : Type*) [MeasurableSpace Ω] (k : ℕ) where
  T : ℝ≥0
  W : ℝ≥0 → Ω → Fin (k + 1) → ℝ
  𝒳 : Ω → ℝ
  κ : ℝ≥0 → Ω → ℝ
  lam : ℝ≥0 → Ω → ℝ
  η : ℝ≥0 → Ω → ℝ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}

/-- Standing probabilistic setting: `T > 0`, `W̃` is a standard `(k+1)`-dimensional Brownian
motion (independent coordinates, so `W⁰` and `W` are independent), `𝒳` is measurable and
independent of the whole path of `W̃`. -/
structure Data.Standing (D : Data Ω k) (P : Measure Ω) : Prop where
  T_pos : 0 < D.T
  brownian : IsStdBrownian P D.W
  init_meas : Measurable D.𝒳
  init_indep : IndepFun D.𝒳 (fun ω t => D.W t ω) P

/-- The σ-algebra generated by the `P`-null sets (used to augment filtrations). -/
def nullSigma (P : Measure Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {N | MeasurableSet N ∧ P N = 0}

lemma nullSigma_le (P : Measure Ω) : nullSigma P ≤ mΩ :=
  MeasurableSpace.generateFrom_le fun _ h => h.1

/-- `𝔽⁰`: the filtration generated by the common noise `W⁰`, augmented by the null sets. -/
noncomputable def filtF0 {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) :
    Filtration ℝ≥0 mΩ where
  seq t := Filtration.natural (fun t ω => D.W t ω 0)
      (fun t => ((measurable_pi_apply 0).comp (hD.brownian.meas t)).stronglyMeasurable) t
    ⊔ nullSigma P
  mono' _ _ h := sup_le_sup_right (Filtration.mono _ h) _
  le' t := sup_le (Filtration.le _ t) (nullSigma_le P)

/-- `𝔽`: `𝓕_t = σ(𝒳, W⁰_s, W_s, s ≤ t)`, augmented by the null sets. -/
noncomputable def filtF {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) :
    Filtration ℝ≥0 mΩ where
  seq t := MeasurableSpace.comap D.𝒳 inferInstance ⊔ brownianFiltration hD.brownian t
    ⊔ nullSigma P
  mono' _ _ h := sup_le_sup_right (sup_le_sup_left (Filtration.mono _ h) _) _
  le' t := sup_le (sup_le hD.init_meas.comap_le (Filtration.le _ t)) (nullSigma_le P)

/-- `dt ⊗ dP` on `[0, T] × Ω`. -/
noncomputable def dtP (T : ℝ≥0) (P : Measure Ω) : Measure (ℝ × Ω) :=
  (volume.restrict (Set.Icc (0 : ℝ) T)).prod P

/-- Essential supremum of a process over `[0, T] × Ω` w.r.t. `dt ⊗ dP`. -/
noncomputable def esssupT (D : Data Ω k) (P : Measure Ω) (u : ℝ≥0 → Ω → ℝ) : ℝ :=
  essSup (fun p : ℝ × Ω => u p.1.toNNReal p.2) (dtP D.T P)

/-- Essential infimum of a process over `[0, T] × Ω` w.r.t. `dt ⊗ dP`. -/
noncomputable def essinfT (D : Data Ω k) (P : Measure Ω) (u : ℝ≥0 → Ω → ℝ) : ℝ :=
  essInf (fun p : ℝ × Ω => u p.1.toNNReal p.2) (dtP D.T P)

/-- `κ_max := ess sup κ`. -/
noncomputable def Data.kappaMax (D : Data Ω k) (P : Measure Ω) : ℝ := esssupT D P D.κ
/-- `η_⋆ := ess inf η`. -/
noncomputable def Data.etaLow (D : Data Ω k) (P : Measure Ω) : ℝ := essinfT D P D.η
/-- `‖η‖ := ess sup |η|`. -/
noncomputable def Data.etaNorm (D : Data Ω k) (P : Measure Ω) : ℝ :=
  esssupT D P (fun t ω => |D.η t ω|)
/-- `λ_⋆ := ess inf λ`. -/
noncomputable def Data.lamLow (D : Data Ω k) (P : Measure Ω) : ℝ := essinfT D P D.lam
/-- `α := η_⋆ / ‖η‖`. -/
noncomputable def Data.alpha (D : Data Ω k) (P : Measure Ω) : ℝ := D.etaLow P / D.etaNorm P

/-- Assumption 2.3 (p. 8). (i) `κ, λ, η` are `𝔽`-progressive, nonnegative and essentially
bounded; `λ` and `η` have positive essential lower bounds (the paper's `1/λ, 1/η ∈ L^∞`);
`𝒳 ∈ L²`. (ii) there is `θ > 0` with `κ_max < 4 η_⋆ θ` and `θ κ_max < 4 λ_⋆`. -/
structure Data.Assumption23 (D : Data Ω k) (P : Measure Ω) (hD : D.Standing P) : Prop where
  κ_prog : IsStronglyProgressive (filtF hD) D.κ
  lam_prog : IsStronglyProgressive (filtF hD) D.lam
  η_prog : IsStronglyProgressive (filtF hD) D.η
  κ_bdd : ∃ c : ℝ, ∀ᵐ p ∂(dtP D.T P), 0 ≤ D.κ p.1.toNNReal p.2 ∧ D.κ p.1.toNNReal p.2 ≤ c
  lam_bdd : ∃ c : ℝ, ∀ᵐ p ∂(dtP D.T P), 0 ≤ D.lam p.1.toNNReal p.2 ∧ D.lam p.1.toNNReal p.2 ≤ c
  η_bdd : ∃ c : ℝ, ∀ᵐ p ∂(dtP D.T P), 0 ≤ D.η p.1.toNNReal p.2 ∧ D.η p.1.toNNReal p.2 ≤ c
  lam_low : ∃ c : ℝ, 0 < c ∧ ∀ᵐ p ∂(dtP D.T P), c ≤ D.lam p.1.toNNReal p.2
  η_low : ∃ c : ℝ, 0 < c ∧ ∀ᵐ p ∂(dtP D.T P), c ≤ D.η p.1.toNNReal p.2
  init_L2 : MemLp D.𝒳 2 P
  weak : ∃ θ : ℝ, 0 < θ ∧ D.kappaMax P < 4 * D.etaLow P * θ ∧ θ * D.kappaMax P < 4 * D.lamLow P

/-- `S²_G([0, T])`. -/
def IsS2 (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G u ∧ ∫⁻ ω, ⨆ t ∈ Set.Iic T, ‖u t ω‖ₑ ^ 2 ∂P < ⊤

/-- `S²_G([0, T−])`: in `S²` on every `[0, τ]`, `τ < T`. -/
def IsS2Minus (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G u ∧ ∀ τ < T, ∫⁻ ω, ⨆ t ∈ Set.Iic τ, ‖u t ω‖ₑ ^ 2 ∂P < ⊤

/-- `D²_G := L²_G([0, T]) ∩ S²_G([0, T−])`. -/
def IsD2 (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ) : Prop :=
  L2F G P T u ∧ IsS2Minus G P T u

/-- Vector process (columns `Z j`) in `L²_G([0, T])`. -/
def IsL2Vec (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (Z : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ j, L2F G P T (Z j)

/-- Vector process in `L²_G([0, T−])`: in `L²` on every `[0, τ]`, `τ < T`. -/
def IsL2VecMinus (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (Z : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ τ < T, ∀ j, L2F G P τ (Z j)

/-- `‖Y‖²_{H_l} = E sup_{0 ≤ t ≤ T} |Y_t / (T − t)^l|²`, in `[0, ∞]`; the weight
`(T − t)^{−l}` is computed in `ℝ≥0∞` (`0^{−l} = ∞` for `l > 0`). -/
noncomputable def hNormSq (T : ℝ≥0) (P : Measure Ω) (l : ℝ) (Y : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (⨆ t ∈ Set.Iic T, ENNReal.ofReal ((T : ℝ) - t) ^ (-l) * ‖Y t ω‖ₑ) ^ 2 ∂P

/-- `H_l` (Definition 2.1). -/
def MemH (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (l : ℝ) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G Y ∧ hNormSq T P l Y < ⊤

/-- `‖Y‖_{M_l} = ess sup_{(t, ω)} |Y_t| / (T − t)^l` (Definition 2.1), in `[0, ∞]`. -/
noncomputable def mNorm (T : ℝ≥0) (P : Measure Ω) (l : ℝ) (Y : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  essSup (fun p : ℝ × Ω => ENNReal.ofReal ((T : ℝ) - p.1) ^ (-l) * ‖Y p.1.toNNReal p.2‖ₑ)
    (dtP T P)

/-- `M_l` (Definition 2.1). -/
def MemM (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (l : ℝ) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G Y ∧ mNorm T P l Y < ⊤

/-- Scalar BSDE on `[0, τ]`: `y_t = ξ + ∫_t^τ F(s, y_s, z_s) ds − Σ_j ∫_t^τ z^j dW̃^j`,
with `y, z^j ∈ L²` on `[0, τ]` (Peng's `SolvesBSDE` with one component). -/
def SolvesScalarBSDE (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (τ : ℝ≥0)
    (W : ℝ≥0 → Ω → Fin (k + 1) → ℝ) (ξ : Ω → ℝ)
    (F : ℝ≥0 → Ω → ℝ → (Fin (k + 1) → ℝ) → ℝ)
    (y : ℝ≥0 → Ω → ℝ) (z : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  SolvesBSDE (ι := Unit) G P τ W (fun ω _ => ξ ω)
    (fun s ω p K _ => F s ω (p ()) (fun j => K j ()))
    (fun t ω _ => y t ω) (fun j t ω _ => z j t ω)

/-- `μ` is a `G`-progressive version of `t ↦ E[ξ_t | G_t]`: for a.e. `t ∈ [0, T]`, `ξ_t` is
integrable and `μ_t = E[ξ_t | G_t]` a.s. -/
def IsCondExpVersion (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (ξ μ : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G μ ∧
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Integrable (ξ t.toNNReal) P ∧ μ t.toNNReal =ᵐ[P] P[ξ t.toNNReal | G t.toNNReal]

/-- The singular Riccati BSDE (Lemma A.1, first equation of (2.8)):
`−dA = (2λ − A²/(2η)) dt − Z^A dW̃` on `[0, T)`, `A ∈ S²([0, T−])`, `Z^A ∈ L²([0, T−])`,
`lim_{t ↑ T} A_t = +∞` a.s. -/
def IsSingularRiccati {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  IsS2Minus (filtF hD) P D.T A ∧ IsL2VecMinus (filtF hD) P D.T ZA ∧
    (∀ τ < D.T, SolvesScalarBSDE (filtF hD) P τ D.W (A τ)
      (fun s ω a _ => 2 * D.lam s ω - a ^ 2 / (2 * D.η s ω)) A ZA) ∧
    ∀ᵐ ω ∂P, Tendsto (fun t => A t ω) (𝓝[<] D.T) atTop

/-- The conditional mean-field FBSDE (2.3):
`dX = −Y/(2η) dt`, `X_0 = 𝒳`, `X_T = 0`,
`−dY = (κ E[Y/(2η) | 𝓕⁰_t] + 2λX) dt − Z dW̃` on `[0, T)`;
the conditional expectation is evaluated through an `𝔽⁰`-progressive version `μ`. -/
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

/-- A solution of (2.3) in the class of Theorem 2.4:
`X ∈ H_α`, `Y ∈ L²_𝔽([0, T])`, `Z ∈ L²_𝔽([0, T−])`. -/
def SolvesFBSDE23InClass {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (X Y : ℝ≥0 → Ω → ℝ) (Z : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  SolvesFBSDE23 hD X Y Z ∧ MemH (filtF hD) P D.T (D.alpha P) X ∧
    L2F (filtF hD) P D.T Y ∧ IsL2VecMinus (filtF hD) P D.T Z

end MFGLiquidation.Nash


