-- Prove2me | Definitions.Def_ExitGamePrivate_Belief
-- name    : ExitGamePrivate_Belief
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:23:49.893429+00:00
-- url     : https://prove2.me/theorems/adadce13-2798-46f3-bb61-6c7b367dd9c9
-- title:
--   Belief map $Y(a)=F^{-1}(e^{-a})$, $A(y)=-\log F(y)$, exit rate $\lambda$ (4.4), the maximal Carathéodory solution of (4.13), and the profile (4.1)
-- statement:
--   The candidate equilibrium of §4 (pp.10–11, 15–16) is built from the following objects.
--
--   1. The **belief map** $Y(a)=F^{-1}(e^{-a})$, $a\ge0$ (4.3), with $F^{-1}$ the inverse of $F$ on $[\theta_L,\theta_U]$, and its inverse $A(y)=-\log F(y)$ for $y\in(\theta_L,\theta_U]$, $A(\theta_L)=\infty$ (4.5).
--   2. The function of Lemma 4.4, $l(x,y)=\dfrac{ry-D(x)}{m(x)-y}$, and the **exit rate**
--   $$\lambda(x,y)=\frac{ry-D(x)}{m(x)-y}\,1_{x\le\alpha(y)}. \tag{4.4}$$
--   3. A **Carathéodory solution** of (4.13) along a path of $X^x$ started at $a$: a function $B$, continuous on $[0,\infty)$, such that $s\mapsto\lambda(X^x_s,Y(B_s))$ is integrable on every $[0,t]$ and
--   $$B_t=a+\int_0^t\lambda\big(X^x_s,Y(B_s)\big)\,ds,\qquad t\ge0. \tag{4.13}$$
--   4. The process $A^{x,a}_t(\omega)$: the **largest** Carathéodory solution along $X^x(\omega)$ started at $a$ (Proposition 4.6 and Remark 4.7).
--   5. The equilibrium strategy as a function of the type, $\hat\tau(\omega,\theta)=\inf\{t\ge0:Y(A^{x,0}_t(\omega))<\theta\}$ ($\inf\emptyset=\infty$); player $i$ plays $\tau_i=\hat\tau(\cdot,\theta_i)$, which is (4.1).
--
--   The process $Y(A_t)$ is the highest type still in the game, and $\lambda(X_t,Y(A_t))$ is the rate at which the opponent exits. The module also contains the Lebesgue–Stieltjes measure $dA$ of an increasing right-continuous path extended by $0$ to negative times, used in (4.7).
--
--   **Formalization Note** $Y(a)$ is written as $\inf\{y\in[\theta_L,\theta_U]:e^{-a}\le F(y)\}$, which under Assumption 4.1 is the unique $y$ with $F(y)=e^{-a}$; $A$ takes values in $[-\infty,\infty]$. The paper constructs its process as the limit $A^0$ of Lipschitz approximations (4.35)–(4.36) and notes that $A^0$ is the largest Carathéodory solution; the pathwise largest solution agrees with $A^0$ almost surely and avoids $\alpha^{-1}$ outside $[\alpha(\theta_L),\alpha(\theta_U)]$, where (4.35) is undefined.
-- source:
--   Kwon & Palczewski, Exit Game with Private Information, arXiv:2210.01610v2, §4.1 pp.10–11 ((4.1), (4.3), (4.4), (4.5)), Lemma 4.2 p.14, Lemma 4.4 p.15, Proposition 4.6 p.15 ((4.13)), Remark 4.7 p.16, proof of Theorem 4.17 p.22

import Mathlib
import Definitions.Def_ExitGamePrivate_Game

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section

namespace ExitGamePrivate

/-- A path `t ↦ f(t)` on `[0, ∞)` extended by `0` to `t < 0`: for an increasing path this encodes
`f(0−) = 0`, as in Lemma 4.2 ("A₀₋ = 0", p.14). -/
def extZero (f : ℝ → ℝ) : ℝ → ℝ := fun t => if t < 0 then 0 else f t

open Classical in
/-- The Lebesgue–Stieltjes measure `df` of an increasing, right-continuous function `f : ℝ → ℝ`,
the measure of `∫ … dA_s` in (4.7), p.14 (`0` if `f` is not monotone). For a right-continuous
increasing `f`, Mathlib's `Monotone.stieltjesFunction` (built from right limits) is `f` itself. -/
def stieltjesMeasure (f : ℝ → ℝ) : Measure ℝ :=
  if h : Monotone f then h.stieltjesFunction.measure else 0

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] (G : Model Ω)

/-- The belief map (4.3), p.11: `Y(a) = F^{-1}(e^{-a})`, `a ≥ 0`, with `F^{-1}` the inverse of `F`
restricted to `[θ_L, θ_U]`.

**Formalization Note** Written as `inf{y ∈ [θ_L, θ_U] : e^{-a} ≤ F(y)}`. Under Assumption 4.1
(`F` continuous, strictly increasing on `[θ_L, θ_U]`, `F(θ_L) = 0`, `F(θ_U) = 1`) this is the
unique `y ∈ (θ_L, θ_U]` with `F(y) = e^{-a}` for every `a ≥ 0`; in particular `Y(0) = θ_U`.
Only `a ≥ 0` is used. -/
def Y (a : ℝ) : ℝ := sInf {y : ℝ | y ∈ Icc G.θL G.θU ∧ Real.exp (-a) ≤ G.F y}

/-- The function (4.5), p.11: `A(y) = −log F(y)` for `y ∈ (θ_L, θ_U]` and `A(θ_L) = ∞`, with values
in `EReal`. Only `y ∈ [θ_L, θ_U]` is used. -/
def Acum (y : ℝ) : EReal := if y ≤ G.θL then ⊤ else ((-Real.log (G.F y) : ℝ) : EReal)

/-- The function of Lemma 4.4, p.15: `l(x, y) = (ry − D(x))/(m(x) − y)`. -/
def l (x y : ℝ) : ℝ := (G.r * y - G.D x) / (G.m x - y)

/-- The exit intensity (4.4), p.11: `λ(x, y) = (ry − D(x))/(m(x) − y) · 1_{x ≤ α(y)}`. -/
def lam (α : ℝ → ℝ) (x y : ℝ) : ℝ := if x ≤ α y then G.l x y else 0

/-- `B` is a Carathéodory solution of (4.13) along the path `ω` of `Xˣ`, started at `A₀ = a`
(Proposition 4.6, p.15): `B` is continuous on `[0, ∞)`, `s ↦ λ(Xˣ_s(ω), Y(B_s))` is integrable on
every `[0, t]`, and `B_t = a + ∫_0^t λ(Xˣ_s(ω), Y(B_s)) ds` for every `t ≥ 0`. -/
def IsCaratheodory (α : ℝ → ℝ) (x a : ℝ) (ω : Ω) (B : ℝ → ℝ) : Prop :=
  ContinuousOn B (Ici 0) ∧
    ∀ t : ℝ, 0 ≤ t →
      IntervalIntegrable (fun s => G.lam α (G.X x s ω) (G.Y (B s))) volume 0 t ∧
      B t = a + ∫ s in (0 : ℝ)..t, G.lam α (G.X x s ω) (G.Y (B s))

/-- The process `A^{x,a}` of Proposition 4.6 (p.15): the largest Carathéodory solution of (4.13)
along the path `ω` of `Xˣ`, started at `a`, i.e. `A^{x,a}_t(ω) = sup{B_t : B a Carathéodory
solution}`.

**Formalization Note** The paper constructs `A⁰ = lim_{ε↓0} A^ε` from Lipschitz approximations
(4.35)–(4.36) (p.26) and notes that it is the largest Carathéodory solution (Remark 4.7, p.16;
§6, p.32). Every pathwise solution lies below each `A^ε` by ODE comparison, and `A⁰` is a solution
outside a null set (Lemma 4.3), so the two definitions agree almost surely; the pathwise maximal
solution is used because (4.35) needs `α^{-1}` outside `[α(θ_L), α(θ_U)]`, where the paper does
not define it. On the null set where no solution exists the value is the default of `sSup`. -/
def Asol (α : ℝ → ℝ) (x a t : ℝ) (ω : Ω) : ℝ :=
  sSup {z : ℝ | ∃ B : ℝ → ℝ, G.IsCaratheodory α x a ω B ∧ B t = z}

/-- The equilibrium strategy as a function of the type, `τ̂(ω, θ) = inf{t ≥ 0 : Y(A_t(ω)) < θ}`
(p.10 and proof of Theorem 4.17, p.22), with `A = A^{x,0}` and `inf ∅ = ∞`. -/
def tauHat (α : ℝ → ℝ) (x : ℝ) (ω : Ω) (θ : ℝ) : WithTop ℝ≥0 :=
  hittingAfter (fun (t : ℝ≥0) ω => G.Y (G.Asol α x 0 (t : ℝ) ω)) (Iio θ) 0 ω

end Model

end ExitGamePrivate


