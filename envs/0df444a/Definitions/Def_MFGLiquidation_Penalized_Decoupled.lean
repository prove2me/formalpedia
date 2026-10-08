-- Prove2me | Definitions.Def_MFGLiquidation_Penalized_Decoupled
-- name    : MFGLiquidation_Penalized_Decoupled
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:30:41.507985+00:00
-- url     : https://prove2.me/theorems/b00cb42b-21b6-43e8-b57b-3a740abce1a8
-- title:
--   The decoupled FBSDE (2.10), the regular Riccati BSDE (4.3), the spaces ℋⁿ_l and ℳⁿ_l, the penalized FBSDE (4.4) and Assumption 4.1
-- statement:
--   Let $(A,Z^A)$ be the singular Riccati solution, $n\ge1$ an integer, $\eta_\star$ the essential lower bound of $\eta$, and $\gamma$ a constant with $0<\gamma<\alpha\wedge\tfrac12$.
--
--   1. **(2.10).** $dX_t=-\frac{1}{2\eta_t}(A_tX_t+B_t)dt$ on $[0,T]$, $X_0=\mathcal X$; $-dB_t=\big(\kappa_t\mathbb E\big[\frac{1}{2\eta_t}(A_tX_t+B_t)\big|\mathcal F^0_t\big]-\frac{A_tB_t}{2\eta_t}\big)dt-Z^B_t\,d\widetilde W_t$ on $[0,T)$, $B_T=0$. The class of Lemma 2.6 / Proposition 2.8 is $\mathcal H_\alpha\times\mathcal H_\gamma\times D^2\times L^2([0,T];\mathbb R^m)\times L^2([0,T-];\mathbb R^m)$ for $(X,B,Y,Z^B,Z^Y)$.
--   2. **(4.3) = (A.3).** $-dA^n_t=\big(2\lambda_t-\frac{(A^n_t)^2}{2\eta_t}\big)dt-Z^{A^n}_t\,d\widetilde W_t$ on $[0,T]$, $A^n_T=2n$, with $(A^n,Z^{A^n})\in S^2([0,T])\times L^2([0,T];\mathbb R^m)$.
--   3. **The spaces of p. 25.**
--   $$\|U\|_{n,l}=\Big(\mathbb E\Big[\sup_{0\le t\le T}\Big|\frac{U_t}{(T-t+\eta_\star/n)^l}\Big|^2\Big]\Big)^{1/2},\qquad \|U\|_{\mathcal M^n_l}=\operatorname*{ess\,sup}_{(t,\omega)\in[0,T]\times\Omega}\frac{|U_t|}{(T-t+\eta_\star/n)^l},$$
--   and $\mathcal H^n_l$, $\mathcal M^n_l$ are the progressive processes for which these are finite.
--   4. **(4.4)** with $\mathfrak p\in\mathbb R$ and $f$:
--   $$\begin{aligned}dX^n_t&=-\tfrac{1}{2\eta_t}(A^n_tX^n_t+B^n_t)\,dt,\qquad X^n_0=\mathcal X,\\ -dB^n_t&=\Big(\kappa_t\mathfrak p\,\mathbb E\Big[\tfrac{1}{2\eta_t}(A^n_tX^n_t+B^n_t)\Big|\mathcal F^0_t\Big]+f_t-\tfrac{A^n_tB^n_t}{2\eta_t}\Big)dt-Z^{B^n}_t\,d\widetilde W_t,\qquad B^n_T=0,\\ dY^n_t&=\Big(-2\lambda_tX^n_t-\kappa_t\mathfrak p\,\mathbb E\Big[\tfrac{A^n_tX^n_t+B^n_t}{2\eta_t}\Big|\mathcal F^0_t\Big]-f_t\Big)dt+Z^{Y^n}_t\,d\widetilde W_t,\qquad Y^n_T=2nX^n_T,\end{aligned}$$
--   all on $[0,T]$. The system (4.2) is the case $\mathfrak p=1$, $f=0$. The class of Theorem 4.3 is $\mathcal H^n_\alpha\times\mathcal H^n_\gamma\times S^2\times L^2([0,T];\mathbb R^m)\times L^2([0,T];\mathbb R^m)$.
--   5. **Assumption 4.1.** There is a constant $C$ such that a.s., for all $0\le r\le s<T$,
--   $$\exp\Big(-\int_r^s\frac{A_u}{2\eta_u}\,du\Big)\le C\,\frac{T-s}{T-r}.$$
--
--   These are the objects of §4: the penalized FBSDEs whose solutions approximate the constrained equilibrium.
--
--   **Formalization Note.** The regularity class of $A^n$ is not printed in Lemma A.3; $S^2\times L^2$ on $[0,T]$ is the standard class for this non-singular quadratic BSDE (its solution is bounded). Unlike (2.11), in (4.4) the process $Y^n$ is pinned by its terminal value, so no relation $Y^n=A^nX^n+B^n$ is imposed. In (2.10), the $B$-equation is imposed on every $[0,\tau]$, $\tau<T$, together with $B_T=0$; with $B\in\mathcal H_\gamma$ and $Z^B\in L^2([0,T])$ this is the $[0,T]$ form. The weights of $\mathcal H^n_l,\mathcal M^n_l$ are `ENNReal.ofReal (T - t + η⋆/n) ^ (-l)`; for $n\ge1$ they are finite and positive on $[0,T]$. Assumption 4.1 is printed without "a.s." on p. 24 and with it on p. 32; it is stated a.s., with $C$ chosen before $\omega$. The paper's $\mathfrak p$ is written `p`.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, p. 9, (2.10); p. 24, Assumption 4.1; p. 25, (4.2), (4.3), ℳⁿ_l, ℋⁿ_l; p. 26, (4.4); p. 32, Lemma A.3 (A.3) and §A.2

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_MFGLiquidation_Penalized_Setting

namespace MFGLiquidation.Penalized

open MeasureTheory ProbabilityTheory Filter Topology Peng1990.SMP
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}

/-- The decoupled FBSDE (2.10) for a given singular Riccati solution `A`:
`dX = −(AX + B)/(2η) dt` on `[0, T]`, `X_0 = 𝒳`;
`−dB = (κ E[(AX + B)/(2η) | 𝓕⁰] − AB/(2η)) dt − Z^B dW̃` on every `[0, τ]`, `τ < T`;
`B_T = 0`. -/
def SolvesFBSDE210 {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (A X B : ℝ≥0 → Ω → ℝ) (ZB : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ∀ t ≤ D.T,
      IntegrableOn (fun s : ℝ => (A s.toNNReal ω * X s.toNNReal ω + B s.toNNReal ω)
        / (2 * D.η s.toNNReal ω)) (Set.Icc 0 (t : ℝ)) ∧
      X t ω = D.𝒳 ω - ∫ s in Set.Icc (0 : ℝ) t,
        (A s.toNNReal ω * X s.toNNReal ω + B s.toNNReal ω) / (2 * D.η s.toNNReal ω)) ∧
    IsStronglyProgressive (filtF hD) X ∧
    (∃ ν, IsCondExpVersion (filtF0 hD) P D.T
        (fun t ω => (A t ω * X t ω + B t ω) / (2 * D.η t ω)) ν ∧
      ∀ τ < D.T, SolvesScalarBSDE (filtF hD) P τ D.W (B τ)
        (fun s ω b _ => D.κ s ω * ν s ω - A s ω * b / (2 * D.η s ω)) B ZB) ∧
    (∀ᵐ ω ∂P, B D.T ω = 0)

/-- The solution class of Lemma 2.6 / Proposition 2.8:
`ℋ_α × ℋ_γ × D² × L²([0, T]; ℝ^m) × L²([0, T−]; ℝ^m)`. -/
def ClassFBSDE211 {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (γ : ℝ)
    (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  MemH (filtF hD) P D.T (D.alpha P) X ∧ MemH (filtF hD) P D.T γ B ∧
    IsD2 (filtF hD) P D.T Y ∧ IsL2Vec (filtF hD) P D.T ZB ∧ IsL2VecMinus (filtF hD) P D.T ZY

/-- The regular Riccati BSDE (4.3) = (A.3): `−dAⁿ = (2λ − (Aⁿ)²/(2η)) dt − Z^{Aⁿ} dW̃`
on `[0, T]`, `Aⁿ_T = 2n`, in `S²([0, T]) × L²([0, T]; ℝ^m)`. -/
def IsRegularRiccati {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (n : ℕ)
    (An : ℝ≥0 → Ω → ℝ) (ZAn : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  IsS2 (filtF hD) P D.T An ∧ IsL2Vec (filtF hD) P D.T ZAn ∧
    SolvesScalarBSDE (filtF hD) P D.T D.W (fun _ => 2 * (n : ℝ))
      (fun s ω a _ => 2 * D.lam s ω - a ^ 2 / (2 * D.η s ω)) An ZAn

/-- `‖U‖²_{n,l} = E sup_{t ≤ T} |U_t / (T − t + η_⋆/n)^l|²`, in `[0, ∞]` (p. 25). -/
noncomputable def hnNormSq (D : Data Ω k) (P : Measure Ω) (n : ℕ) (l : ℝ)
    (U : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, (⨆ t ∈ Set.Iic D.T,
      ENNReal.ofReal ((D.T : ℝ) - t + D.etaLow P / n) ^ (-l) * ‖U t ω‖ₑ) ^ 2 ∂P

/-- `ℋⁿ_l` (p. 25). -/
def MemHn {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (n : ℕ) (l : ℝ)
    (U : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive (filtF hD) U ∧ hnNormSq D P n l U < ⊤

/-- `‖U‖_{ℳⁿ_l} = ess sup_{(t,ω)} |U_t| / (T − t + η_⋆/n)^l`, in `[0, ∞]` (p. 25). -/
noncomputable def mnNorm (D : Data Ω k) (P : Measure Ω) (n : ℕ) (l : ℝ)
    (U : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  essSup (fun p : ℝ × Ω =>
      ENNReal.ofReal ((D.T : ℝ) - p.1 + D.etaLow P / n) ^ (-l) * ‖U p.1.toNNReal p.2‖ₑ)
    (dtP D.T P)

/-- `ℳⁿ_l` (p. 25). -/
def MemMn {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (n : ℕ) (l : ℝ)
    (U : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive (filtF hD) U ∧ mnNorm D P n l U < ⊤

/-- The penalized FBSDE (4.4) with penalty `n`, parameter `p` (the paper's 𝔭) and data `f`,
for a given solution `Aⁿ` of (4.3):
`dXⁿ = −(AⁿXⁿ + Bⁿ)/(2η) dt`, `Xⁿ_0 = 𝒳`;
`−dBⁿ = (κ p E[(AⁿXⁿ + Bⁿ)/(2η) | 𝓕⁰] + f − AⁿBⁿ/(2η)) dt − Z^{Bⁿ} dW̃`, `Bⁿ_T = 0`;
`dYⁿ = (−2λXⁿ − κ p E[(AⁿXⁿ + Bⁿ)/(2η) | 𝓕⁰] − f) dt + Z^{Yⁿ} dW̃`, `Yⁿ_T = 2n Xⁿ_T`;
all on `[0, T]`. (4.2) is the case `p = 1`, `f = 0`. -/
def SolvesFBSDE44 {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (n : ℕ)
    (An : ℝ≥0 → Ω → ℝ) (p : ℝ) (f : ℝ≥0 → Ω → ℝ) (X B Y : ℝ≥0 → Ω → ℝ)
    (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ∀ t ≤ D.T,
      IntegrableOn (fun s : ℝ => (An s.toNNReal ω * X s.toNNReal ω + B s.toNNReal ω)
        / (2 * D.η s.toNNReal ω)) (Set.Icc 0 (t : ℝ)) ∧
      X t ω = D.𝒳 ω - ∫ s in Set.Icc (0 : ℝ) t,
        (An s.toNNReal ω * X s.toNNReal ω + B s.toNNReal ω) / (2 * D.η s.toNNReal ω)) ∧
    IsStronglyProgressive (filtF hD) X ∧
    ∃ ν, IsCondExpVersion (filtF0 hD) P D.T
        (fun t ω => (An t ω * X t ω + B t ω) / (2 * D.η t ω)) ν ∧
      SolvesScalarBSDE (filtF hD) P D.T D.W (fun _ => 0)
        (fun s ω b _ => D.κ s ω * p * ν s ω + f s ω - An s ω * b / (2 * D.η s ω)) B ZB ∧
      SolvesScalarBSDE (filtF hD) P D.T D.W (fun ω => 2 * (n : ℝ) * X D.T ω)
        (fun s ω _ _ => 2 * D.lam s ω * X s ω + D.κ s ω * p * ν s ω + f s ω) Y ZY

/-- The solution class of Theorem 4.3:
`ℋⁿ_α × ℋⁿ_γ × S²([0, T]) × L²([0, T]; ℝ^m) × L²([0, T]; ℝ^m)`. -/
def ClassFBSDE44 {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P) (n : ℕ) (γ : ℝ)
    (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  MemHn hD n (D.alpha P) X ∧ MemHn hD n γ B ∧ IsS2 (filtF hD) P D.T Y ∧
    IsL2Vec (filtF hD) P D.T ZB ∧ IsL2Vec (filtF hD) P D.T ZY

/-- Assumption 4.1 (p. 24; a.s. form of p. 32) on the singular Riccati solution `A`:
there is `C` such that a.s., for all `0 ≤ r ≤ s < T`,
`exp(−∫_r^s A_u/(2η_u) du) ≤ C (T − s)/(T − r)`. -/
def Assumption41 {D : Data Ω k} {P : Measure Ω} (_hD : D.Standing P)
    (A : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ C : ℝ, ∀ᵐ ω ∂P, ∀ r s : ℝ, 0 ≤ r → r ≤ s → s < D.T →
    Real.exp (-∫ u in Set.Icc r s, A u.toNNReal ω / (2 * D.η u.toNNReal ω))
      ≤ C * (((D.T : ℝ) - s) / ((D.T : ℝ) - r))

end MFGLiquidation.Penalized


