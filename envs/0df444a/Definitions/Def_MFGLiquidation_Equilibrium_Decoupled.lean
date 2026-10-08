-- Prove2me | Definitions.Def_MFGLiquidation_Equilibrium_Decoupled
-- name    : MFGLiquidation_Equilibrium_Decoupled
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:29:34.42423+00:00
-- url     : https://prove2.me/theorems/0ef7fd91-35a8-4eb1-b493-ddf54d3fb419
-- title:
--   The decoupled FBSDE (2.11) with parameter 𝔭 and data f, its solution class, and unique solvability
-- statement:
--   Let $A$ be a process (in the statements, the solution of the singular Riccati BSDE), $\mathfrak p\in\mathbb R$ a parameter and $f$ a process. A tuple $(X,B,Y,Z^B,Z^Y)$ **solves (2.11)** if
--   $$\begin{cases} dX_t=-\dfrac{1}{2\eta_t}(A_tX_t+B_t)\,dt, & X_0=\mathcal X,\\[4pt] -dB_t=\Big(\kappa_t\mathfrak p\,\mathbb E\Big[\dfrac{A_tX_t+B_t}{2\eta_t}\Big|\mathcal F^0_t\Big]+f_t-\dfrac{A_tB_t}{2\eta_t}\Big)dt-Z^B_t\,d\widetilde W_t, & B_T=0,\\[4pt] dY_t=\Big(-2\lambda_tX_t-\kappa_t\mathfrak p\,\mathbb E\Big[\dfrac{A_tX_t+B_t}{2\eta_t}\Big|\mathcal F^0_t\Big]-f_t\Big)dt+Z^Y_t\,d\widetilde W_t, \end{cases}$$
--   together with the decoupling relation $Y_t=A_tX_t+B_t$ for $t\in[0,T)$. The forward equation holds on $[0,T]$ (in integral form, with an integrable integrand), the two backward equations on every $[0,\tau]$, $\tau<T$, and $X$ is $\mathbb F$-progressive.
--
--   The **solution class** is $\mathcal H_\alpha\times\mathcal H_\gamma\times D^2_{\mathbb F}([0,T])\times L^2_{\mathbb F}([0,T];\mathbb R^m)\times L^2_{\mathbb F}([0,T-];\mathbb R^m)$. Two solutions **agree** when $X$ and $B$ agree a.s. at every $t\le T$, $Y$ at every $t<T$, $Z^B$ $dt\otimes d\mathbb P$-a.e. on $[0,T]$, and $Z^Y$ on every $[0,\tau]$, $\tau<T$. The system is **uniquely solvable** for $(A,\gamma,\mathfrak p)$ if for every $f\in L^2_{\mathbb F}([0,T])$ a solution in the class exists and any two solutions in the class agree. The file also fixes two auxiliary notions: a vector of Itô integral processes $J^j=\int_0^\cdot Z^j\,d\widetilde W^j$ on $[0,T]$, and a true martingale on $[0,T]$ (integrable, with $\mathbb E[M_t\mid\mathcal G_s]=M_s$ for $s\le t\le T$).
--
--   For $\mathfrak p=1$, $f=0$ the first two equations are the system (2.10); the parameter $\mathfrak p$ is the homotopy of the method of continuation.
--
--   **Formalization Note** As printed, the third equation of (2.11) has a drift that does not involve $Y$ and no terminal condition, so $(X,B,Y+c,Z^B,Z^Y)$ would be another solution for every $c\in L^2(\mathcal F_0)$; uniqueness holds only together with $Y=AX+B$ on $[0,T)$, which Lemma 2.6 states and the proof of Lemma 2.7 uses ("and $\widetilde Y=A\widetilde X+\widetilde B$"). It is therefore part of the solution concept. The paper says the first two equations hold on $[0,T]$; the $B$-equation is imposed on every $[0,\tau]$, $\tau<T$, plus $B_T=0$, because the integrated form on $[0,T]$ already requires $Z^B\in L^2([0,T])$, which is a conclusion of Lemma 2.5. In the class ($B\in\mathcal H_\gamma$, $Z^B\in L^2([0,T])$) the two forms are equivalent. The conditional expectation is evaluated through one $\mathbb F^0$-progressive version $\nu$, shared by both backward equations.
-- source:
--   Fu, Graewe, Horst, Popier, A Mean Field Game of Optimal Portfolio Liquidation, arXiv:1804.04911v3, pp. 9–10, (2.10), (2.11); pp. 11–12, Lemmas 2.6, 2.7 (solution class)

import Mathlib
import Definitions.Def_MFGLiquidation_Equilibrium_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MFGLiquidation.Equilibrium

open Peng1990.SMP

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}

/-- `(X, B, Y, Z^B, Z^Y)` solves the decoupled FBSDE (2.11) with parameter `p` (the paper's `𝔭`)
and data `f`, for a given process `A`:
* `X_t = 𝒳 − ∫_0^t (A_s X_s + B_s)/(2η_s) ds` on `[0, T]`, `X` progressive;
* `ν` is an `𝔽⁰`-progressive version of `E[(A_t X_t + B_t)/(2η_t) | 𝓕⁰_t]`;
* `−dB_t = (κ_t 𝔭 ν_t + f_t − A_t B_t/(2η_t)) dt − Z^B_t dW̃_t` on every `[0, τ]`, `τ < T`,
  and `B_T = 0`;
* `dY_t = (−2λ_t X_t − κ_t 𝔭 ν_t − f_t) dt + Z^Y_t dW̃_t` on every `[0, τ]`, `τ < T`;
* the decoupling relation `Y_t = A_t X_t + B_t`, `t ∈ [0, T)`. -/
def SolvesFBSDE211 {D : Data Ω k} {P : Measure Ω} (hD : D.Standing P)
    (A : ℝ≥0 → Ω → ℝ) (p : ℝ) (f : ℝ≥0 → Ω → ℝ) (X B Y : ℝ≥0 → Ω → ℝ)
    (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyProgressive (filtF hD) X ∧
    (∀ᵐ ω ∂P, ∀ t ≤ D.T,
      IntegrableOn (fun s : ℝ => (A s.toNNReal ω * X s.toNNReal ω + B s.toNNReal ω) /
          (2 * D.η s.toNNReal ω)) (Set.Icc 0 (t : ℝ)) ∧
      X t ω = D.𝒳 ω - ∫ s in Set.Icc (0 : ℝ) t,
          (A s.toNNReal ω * X s.toNNReal ω + B s.toNNReal ω) / (2 * D.η s.toNNReal ω)) ∧
    ∃ ν : ℝ≥0 → Ω → ℝ,
      IsCondExpVersion (filtF0 hD) P D.T
        (fun t ω => (A t ω * X t ω + B t ω) / (2 * D.η t ω)) ν ∧
      (∀ τ < D.T, SolvesScalarBSDE (filtF hD) P τ D.W (B τ)
        (fun s ω b _ => D.κ s ω * p * ν s ω + f s ω - A s ω * b / (2 * D.η s ω)) B ZB) ∧
      (∀ᵐ ω ∂P, B D.T ω = 0) ∧
      (∀ τ < D.T, SolvesScalarBSDE (filtF hD) P τ D.W (Y τ)
        (fun s ω _ _ => 2 * D.lam s ω * X s ω + D.κ s ω * p * ν s ω + f s ω) Y ZY) ∧
      (∀ t < D.T, Y t =ᵐ[P] fun ω => A t ω * X t ω + B t ω)

/-- The solution class of Lemmas 2.6, 2.7 and Proposition 2.8:
`(X, B, Y, Z^B, Z^Y) ∈ ℋ_α × ℋ_γ × D²_𝔽([0, T]) × L²_𝔽([0, T]; ℝ^m) × L²_𝔽([0, T−]; ℝ^m)`. -/
def ClassFBSDE211 {D : Data Ω k} {P : Measure Ω} [SFinite P] (hD : D.Standing P) (γ : ℝ)
    (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  MemH (filtF hD) P D.T (D.alpha P) X ∧ MemH (filtF hD) P D.T γ B ∧
    IsD2 (filtF hD) P D.T Y ∧ IsL2Vec (filtF hD) P D.T ZB ∧ IsL2VecMinus (filtF hD) P D.T ZY

/-- Two solutions of (2.11) are the same: `X, B` agree a.s. at every `t ≤ T`, `Y` at every
`t < T`, `Z^B` agree `dt ⊗ dP`-a.e. on `[0, T]`, and `Z^Y` on every `[0, τ]`, `τ < T`. -/
def AgreeFBSDE211 {D : Data Ω k} {P : Measure Ω} [SFinite P] (_hD : D.Standing P)
    (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ)
    (X' B' Y' : ℝ≥0 → Ω → ℝ) (ZB' ZY' : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t ≤ D.T, X' t =ᵐ[P] X t) ∧ (∀ t ≤ D.T, B' t =ᵐ[P] B t) ∧
    (∀ t < D.T, Y' t =ᵐ[P] Y t) ∧ (∀ j, AEEqT D.T P (ZB' j) (ZB j)) ∧
    ∀ τ < D.T, ∀ j, AEEqT τ P (ZY' j) (ZY j)

/-- (2.11) with parameter `p` is uniquely solvable in the class of Lemma 2.6 for every data
`f ∈ L²_𝔽([0, T])`: a solution in the class exists, and any two solutions in the class
agree. -/
def UniquelySolvable211 {D : Data Ω k} {P : Measure Ω} [SFinite P] (hD : D.Standing P)
    (A : ℝ≥0 → Ω → ℝ) (γ p : ℝ) : Prop :=
  ∀ f : ℝ≥0 → Ω → ℝ, L2F (filtF hD) P D.T f →
    (∃ (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      ClassFBSDE211 hD γ X B Y ZB ZY ∧ SolvesFBSDE211 hD A p f X B Y ZB ZY) ∧
    ∀ (X B Y : ℝ≥0 → Ω → ℝ) (ZB ZY : Fin (k + 1) → ℝ≥0 → Ω → ℝ)
      (X' B' Y' : ℝ≥0 → Ω → ℝ) (ZB' ZY' : Fin (k + 1) → ℝ≥0 → Ω → ℝ),
      ClassFBSDE211 hD γ X B Y ZB ZY → SolvesFBSDE211 hD A p f X B Y ZB ZY →
      ClassFBSDE211 hD γ X' B' Y' ZB' ZY' → SolvesFBSDE211 hD A p f X' B' Y' ZB' ZY' →
      AgreeFBSDE211 hD X B Y ZB ZY X' B' Y' ZB' ZY'

/-- `J = (J^1, …, J^m)` are Itô integral processes `J^j_t = ∫_0^t Z^j_s dW̃^j_s` on `[0, T]`. -/
def IsItoIntegralVec (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → Fin (k + 1) → ℝ) (Z J : Fin (k + 1) → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ j, IsItoIntegral G P T (fun s ω => W s ω j) (Z j) (J j)

/-- `M` is a true `𝔾`-martingale on `[0, T]`: integrable at every `t ≤ T`, and
`E[M_t | 𝒢_s] = M_s` a.s. for all `s ≤ t ≤ T`. -/
def IsMartingaleOn (G : Filtration ℝ≥0 mΩ) (P : Measure Ω) (T : ℝ≥0) (M : ℝ≥0 → Ω → ℝ) :
    Prop :=
  (∀ t ≤ T, Integrable (M t) P) ∧ ∀ s t : ℝ≥0, s ≤ t → t ≤ T → P[M t | G s] =ᵐ[P] M s

end MFGLiquidation.Equilibrium


