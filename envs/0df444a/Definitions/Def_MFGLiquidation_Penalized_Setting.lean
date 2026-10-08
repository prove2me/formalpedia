-- Prove2me | Definitions.Def_MFGLiquidation_Penalized_Setting
-- name    : MFGLiquidation_Penalized_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:46.332033+00:00
-- url     : https://prove2.me/theorems/7ee63b66-3a7b-4ff3-969c-34e02d41dfa2
-- title:
--   Brownian motion W̃ = (W⁰, W), initial portfolio 𝒳, filtrations 𝔽⁰ and 𝔽, Assumption 2.3, the spaces of §1.2.2 and Definition 2.1, the singular Riccati BSDE and the FBSDE (2.3)
-- statement:
--   This file fixes the probabilistic setting of the mean field liquidation game of Fu, Graewe, Horst and Popier.
--
--   **Data.** A horizon $T>0$; an $m$-dimensional Brownian motion $\widetilde W=(W^0,W)$ with $m=k+1$, where $W^0$ (coordinate $0$) is the one-dimensional common noise and $W$ the $(m-1)$-dimensional idiosyncratic noise; an initial portfolio $\mathcal X$ independent of $\widetilde W$; and cost coefficients: the market impact $\kappa$, the risk aversion $\lambda$ and the temporary impact $\eta$, all processes on $[0,T]\times\Omega$.
--
--   **Filtrations.** $\mathbb F^0=(\mathcal F^0_t)$ with $\mathcal F^0_t=\sigma(W^0_s,\ s\le t)$ and $\mathbb F=(\mathcal F_t)$ with $\mathcal F_t=\sigma(\mathcal X, W^0_s, W_s,\ s\le t)$, both augmented by the null sets.
--
--   **Essential bounds.** With $dt\otimes d\mathbb P$ on $[0,T]\times\Omega$: $\kappa_{\max}=\operatorname{ess\,sup}\kappa$, $\eta_\star=\operatorname{ess\,inf}\eta$, $\lambda_\star=\operatorname{ess\,inf}\lambda$, $\|\eta\|=\operatorname{ess\,sup}|\eta|$, and $\alpha=\eta_\star/\|\eta\|$ (2.5).
--
--   **Assumption 2.3.** (i) $\kappa,\lambda,\eta$ are $\mathbb F$-progressive, nonnegative and essentially bounded; $\lambda$ and $\eta$ are essentially bounded below by positive constants (this is "$1/\lambda,1/\eta\in L^\infty$"); $\mathcal X\in L^2$ and is independent of $W^0,W$. (ii) There is $\theta>0$ with
--   $$\kappa_{\max}<4\eta_\star\theta,\qquad \theta\,\kappa_{\max}<4\lambda_\star ,$$
--   which is (2.4), $\frac{\kappa_{\max}}{4\eta_\star}<\theta<\frac{4\lambda_\star}{\kappa_{\max}}$, written without division.
--
--   **Spaces.** $S^2([0,T])$ ($\mathbb E\sup_{t\le T}|u_t|^2<\infty$), $S^2([0,T-])$ (the same on every $[0,\tau]$, $\tau<T$), $D^2=L^2\cap S^2([0,T-])$, $L^2$ and $L^2([0,T-])$ for $\mathbb R^m$-valued processes, and the weighted spaces of Definition 2.1:
--   $$\|Y\|_{\mathcal H_l}^2=\mathbb E\Big[\sup_{0\le t\le T}\Big|\frac{Y_t}{(T-t)^l}\Big|^2\Big],\qquad \|Y\|_{\mathcal M_l}=\operatorname*{ess\,sup}_{(t,\omega)}\frac{|Y_t|}{(T-t)^l}.$$
--
--   **Equations.** A scalar BSDE on $[0,\tau]$ is read in integrated form, $y_t=\xi+\int_t^\tau F(s,y_s,z_s)\,ds-\int_t^\tau z_s\,d\widetilde W_s$. The **singular Riccati BSDE** of Lemma A.1 is
--   $$-dA_t=\Big(2\lambda_t-\frac{A_t^2}{2\eta_t}\Big)dt-Z^A_t\,d\widetilde W_t\ \text{ on }[0,T),\qquad \lim_{t\uparrow T}A_t=+\infty\ \text{a.s.},$$
--   with $(A,Z^A)\in S^2([0,T-])\times L^2([0,T-])$. The conditional mean-field FBSDE (2.3) is
--   $$dX_t=-\frac{Y_t}{2\eta_t}dt,\quad -dY_t=\Big(\kappa_t\,\mathbb E\Big[\frac{Y_t}{2\eta_t}\Big|\mathcal F^0_t\Big]+2\lambda_tX_t\Big)dt-Z_t\,d\widetilde W_t,\quad X_0=\mathcal X,\ X_T=0,$$
--   the first equation on $[0,T]$ and the second on $[0,T)$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Time is $\mathbb R_{\ge0}$ and time integrals are over `Set.Icc`. $\lambda$ is written `lam` ($\lambda$ is a Lean keyword). BSDEs on $[0,T)$ are imposed on every $[0,\tau]$, $\tau<T$, with terminal value the process itself at $\tau$; scalar BSDEs are `Peng1990.SMP.SolvesBSDE` with a one-point index type. The weighted norms are lower integrals and essential suprema in $[0,\infty]$ with weight `ENNReal.ofReal (T - t) ^ (-l)`, so that, for $l>0$, finiteness of $\|Y\|_{\mathcal H_l}$ forces $Y_T=0$ a.s., the paper's convention for processes with values in $\mathbb R\cup\{\infty\}$. The value $A_T=\infty$ is encoded as $\lim_{t\uparrow T}A_t=+\infty$ a.s. (p. 9). The conditional expectation $\mathbb E[\,\cdot\,|\mathcal F^0_t]$ inside a driver is evaluated through an $\mathbb F^0$-progressive version $\mu$ (`IsCondExpVersion`), which requires integrability of the argument for a.e. $t$; any two versions agree $dt\otimes d\mathbb P$-a.e. The quantities $\kappa_{\max},\eta_\star,\lambda_\star,\|\eta\|$ are read as essential bounds over $dt\otimes d\mathbb P$ (the notation section, p. 6).
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, pp. 4–9, §1.2.1, §1.2.2, (2.3), Definition 2.1, Assumption 2.3, (2.5), (2.8); p. 31, Lemma A.1

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic

namespace MFGLiquidation.Penalized

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

/-- The data of the representative player's problem (§1.2.1, pp. 4–5): horizon `T`, the
`m = k + 1`-dimensional Brownian motion `W̃ = (W⁰, W)` (coordinate `0` is `W⁰`), the initial
portfolio `𝒳`, and the cost coefficients `κ`, `λ` (written `lam`), `η`. -/
structure Data (Ω : Type*) [MeasurableSpace Ω] (k : ℕ) where
  T : ℝ≥0
  W : ℝ≥0 → Ω → Fin (k + 1) → ℝ
  𝒳 : Ω → ℝ
  κ : ℝ≥0 → Ω → ℝ
  lam : ℝ≥0 → Ω → ℝ
  η : ℝ≥0 → Ω → ℝ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}

/-- Standing structure (p. 4): `T > 0`, `W̃` is a standard Brownian motion with independent
coordinates (so `W⁰` and `W` are independent), and `𝒳` is measurable and independent of the
whole path of `W̃`. -/
structure Data.Standing (D : Data Ω k) (P : Measure Ω) : Prop where
  T_pos : 0 < D.T
  brownian : IsStdBrownian P D.W
  init_meas : Measurable D.𝒳
  init_indep : IndepFun D.𝒳 (fun ω t => D.W t ω) P

/-- The σ-algebra generated by the `P`-null sets (used to augment filtrations, footnote 1). -/
def nullSigma (P : Measure Ω) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {N | MeasurableSet N ∧ P N = 0}

theorem nullSigma_le (P : Measure Ω) : nullSigma P ≤ mΩ :=
  MeasurableSpace.generateFrom_le fun _ h => h.1

/-- `𝔽⁰`: the filtration generated by `W⁰`, augmented by the null sets. -/
noncomputable def filtF0 {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) :
    Filtration ℝ≥0 mΩ where
  seq t := Filtration.natural (fun t ω => D.W t ω 0)
      (fun t => ((measurable_pi_apply 0).comp (hD.brownian.meas t)).stronglyMeasurable) t
    ⊔ nullSigma P
  mono' _ _ hst := sup_le_sup_right ((Filtration.natural _ _).mono hst) _
  le' t := sup_le ((Filtration.natural _ _).le t) (nullSigma_le P)

/-- `𝔽`: `𝓕_t = σ(𝒳, W⁰_s, W_s, s ≤ t)`, augmented by the null sets. -/
noncomputable def filtF {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) :
    Filtration ℝ≥0 mΩ where
  seq t := MeasurableSpace.comap D.𝒳 inferInstance ⊔ brownianFiltration hD.brownian t
    ⊔ nullSigma P
  mono' _ _ hst := sup_le_sup_right (sup_le_sup_left ((brownianFiltration _).mono hst) _) _
  le' t := sup_le (sup_le hD.init_meas.comap_le ((brownianFiltration _).le t)) (nullSigma_le P)

/-- The product measure `dt ⊗ dP` on `[0, T] × Ω`. -/
noncomputable def dtP (T : ℝ≥0) (P : Measure Ω) : Measure (ℝ × Ω) :=
  (volume.restrict (Set.Icc (0 : ℝ) T)).prod P

/-- Essential supremum over `[0, T] × Ω` w.r.t. `dt ⊗ dP`. -/
noncomputable def esssupT (D : Data Ω k) (P : Measure Ω) (u : ℝ≥0 → Ω → ℝ) : ℝ :=
  essSup (fun p : ℝ × Ω => u p.1.toNNReal p.2) (dtP D.T P)

/-- Essential infimum over `[0, T] × Ω` w.r.t. `dt ⊗ dP`. -/
noncomputable def essinfT (D : Data Ω k) (P : Measure Ω) (u : ℝ≥0 → Ω → ℝ) : ℝ :=
  essInf (fun p : ℝ × Ω => u p.1.toNNReal p.2) (dtP D.T P)

/-- `κ_max`. -/
noncomputable def Data.kappaMax (D : Data Ω k) (P : Measure Ω) : ℝ := esssupT D P D.κ

/-- `η_⋆`. -/
noncomputable def Data.etaLow (D : Data Ω k) (P : Measure Ω) : ℝ := essinfT D P D.η

/-- `‖η‖`. -/
noncomputable def Data.etaNorm (D : Data Ω k) (P : Measure Ω) : ℝ :=
  esssupT D P (fun t ω => |D.η t ω|)

/-- `λ_⋆`. -/
noncomputable def Data.lamLow (D : Data Ω k) (P : Measure Ω) : ℝ := essinfT D P D.lam

/-- `α := η_⋆ / ‖η‖` (2.5). -/
noncomputable def Data.alpha (D : Data Ω k) (P : Measure Ω) : ℝ := D.etaLow P / D.etaNorm P

/-- Assumption 2.3 (p. 8). -/
structure Data.Assumption23 (D : Data Ω k) (P : Measure Ω) (hD : D.Standing P) : Prop where
  prog_κ : IsStronglyProgressive (filtF hD) D.κ
  prog_lam : IsStronglyProgressive (filtF hD) D.lam
  prog_η : IsStronglyProgressive (filtF hD) D.η
  bdd_κ : ∃ c : ℝ, ∀ᵐ p ∂(dtP D.T P), 0 ≤ D.κ p.1.toNNReal p.2 ∧ D.κ p.1.toNNReal p.2 ≤ c
  bdd_lam : ∃ c : ℝ, ∀ᵐ p ∂(dtP D.T P), 0 ≤ D.lam p.1.toNNReal p.2 ∧ D.lam p.1.toNNReal p.2 ≤ c
  bdd_η : ∃ c : ℝ, ∀ᵐ p ∂(dtP D.T P), 0 ≤ D.η p.1.toNNReal p.2 ∧ D.η p.1.toNNReal p.2 ≤ c
  low_lam : ∃ c : ℝ, 0 < c ∧ ∀ᵐ p ∂(dtP D.T P), c ≤ D.lam p.1.toNNReal p.2
  low_η : ∃ c : ℝ, 0 < c ∧ ∀ᵐ p ∂(dtP D.T P), c ≤ D.η p.1.toNNReal p.2
  init_L2 : MemLp D.𝒳 2 P
  weak : ∃ θ : ℝ, 0 < θ ∧ D.kappaMax P < 4 * D.etaLow P * θ ∧
    θ * D.kappaMax P < 4 * D.lamLow P

/-- `S²_G([0, T])`. -/
def IsS2 (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G u ∧ ∫⁻ ω, ⨆ t ∈ Set.Iic T, ‖u t ω‖ₑ ^ 2 ∂P < ⊤

/-- `S²_G([0, T−])`. -/
def IsS2Minus (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G u ∧ ∀ τ < T, ∫⁻ ω, ⨆ t ∈ Set.Iic τ, ‖u t ω‖ₑ ^ 2 ∂P < ⊤

/-- `D²_G := L²_G([0, T]) ∩ S²_G([0, T−])`. -/
def IsD2 (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (u : ℝ≥0 → Ω → ℝ) : Prop :=
  L2F G P T u ∧ IsS2Minus G P T u

/-- `L²_G([0, T]; ℝ^m)` for a vector process given by its columns. -/
def IsL2Vec (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (Z : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ j, L2F G P T (Z j)

/-- `L²_G([0, T−]; ℝ^m)`. -/
def IsL2VecMinus (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (Z : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ τ < T, ∀ j, L2F G P τ (Z j)

/-- `‖Y‖²_{ℋ_l} = E sup_{t ≤ T} |Y_t / (T − t)^l|²`, computed in `[0, ∞]` (Definition 2.1). -/
noncomputable def hNormSq (T : ℝ≥0) (P : Measure Ω) (l : ℝ) (Y : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (⨆ t ∈ Set.Iic T, ENNReal.ofReal ((T : ℝ) - t) ^ (-l) * ‖Y t ω‖ₑ) ^ 2 ∂P

/-- `ℋ_l` (Definition 2.1). -/
def MemH (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (l : ℝ) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G Y ∧ hNormSq T P l Y < ⊤

/-- `‖Y‖_{ℳ_l} = ess sup_{(t,ω)} |Y_t| / (T − t)^l`, computed in `[0, ∞]` (Definition 2.1). -/
noncomputable def mNorm (T : ℝ≥0) (P : Measure Ω) (l : ℝ) (Y : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  essSup (fun p : ℝ × Ω => ENNReal.ofReal ((T : ℝ) - p.1) ^ (-l) * ‖Y p.1.toNNReal p.2‖ₑ)
    (dtP T P)

/-- `ℳ_l` (Definition 2.1). -/
def MemM (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (l : ℝ) (Y : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G Y ∧ mNorm T P l Y < ⊤

/-- The scalar BSDE `y_t = ξ + ∫_t^τ F(s, y_s, z_s) ds − Σ_j ∫_t^τ z^j dW̃^j` on `[0, τ]`
(`Peng1990.SMP.SolvesBSDE` with one-point index type). -/
def SolvesScalarBSDE (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (τ : ℝ≥0)
    (W : ℝ≥0 → Ω → Fin (k + 1) → ℝ) (ξ : Ω → ℝ)
    (F : ℝ≥0 → Ω → ℝ → (Fin (k + 1) → ℝ) → ℝ) (y : ℝ≥0 → Ω → ℝ)
    (z : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  SolvesBSDE (ι := Unit) G P τ W (fun ω _ => ξ ω)
    (fun s ω q K _ => F s ω (q ()) (fun j => K j ())) (fun t ω _ => y t ω)
    (fun j t ω _ => z j t ω)

/-- `μ` is a `G`-progressive version of `t ↦ E[ξ_t | G_t]` for a.e. `t ∈ [0, T]`. -/
def IsCondExpVersion (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (ξ μ : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive G μ ∧
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Integrable (ξ t.toNNReal) P ∧ μ t.toNNReal =ᵐ[P] P[ξ t.toNNReal | G t.toNNReal]

/-- The singular Riccati BSDE (Lemma A.1, first equation of (2.8)):
`−dA = (2λ − A²/(2η)) dt − Z^A dW̃` on `[0, T)`, `A_T = +∞`, in
`S²([0, T−]) × L²([0, T−])`. -/
def IsSingularRiccati {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (A : ℝ≥0 → Ω → ℝ) (ZA : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  IsS2Minus (filtF hD) P D.T A ∧ IsL2VecMinus (filtF hD) P D.T ZA ∧
    (∀ τ < D.T, SolvesScalarBSDE (filtF hD) P τ D.W (A τ)
      (fun s ω a _ => 2 * D.lam s ω - a ^ 2 / (2 * D.η s ω)) A ZA) ∧
    ∀ᵐ ω ∂P, Tendsto (fun t => A t ω) (𝓝[<] D.T) atTop

/-- The conditional mean-field FBSDE (2.3): forward equation on `[0, T]`, `X_T = 0`, and the
backward equation on every `[0, τ]`, `τ < T`, with a `𝔽⁰`-progressive version `μ` of
`E[Y_t/(2η_t) | 𝓕⁰_t]`. -/
def SolvesFBSDE23 {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (X Y : ℝ≥0 → Ω → ℝ) (Z : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ∀ t ≤ D.T,
      IntegrableOn (fun s : ℝ => Y s.toNNReal ω / (2 * D.η s.toNNReal ω)) (Set.Icc 0 (t : ℝ)) ∧
      X t ω = D.𝒳 ω - ∫ s in Set.Icc (0 : ℝ) t, Y s.toNNReal ω / (2 * D.η s.toNNReal ω)) ∧
    (∀ᵐ ω ∂P, X D.T ω = 0) ∧
    (∃ μ, IsCondExpVersion (filtF0 hD) P D.T (fun t ω => Y t ω / (2 * D.η t ω)) μ ∧
      ∀ τ < D.T, SolvesScalarBSDE (filtF hD) P τ D.W (Y τ)
        (fun s ω _ _ => D.κ s ω * μ s ω + 2 * D.lam s ω * X s ω) Y Z) ∧
    IsStronglyProgressive (filtF hD) X

end MFGLiquidation.Penalized


