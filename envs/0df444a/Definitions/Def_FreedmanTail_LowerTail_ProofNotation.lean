-- Prove2me | Definitions.Def_FreedmanTail_LowerTail_ProofNotation
-- name    : FreedmanTail_LowerTail_ProofNotation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:32:38.653739+00:00
-- url     : https://prove2.me/theorems/a4232a1f-026a-43ab-a6ae-789302af33f0
-- title:
--   Notation (4.14) of the proof of (4.10): φ(λ), λ, k, N, the intervals I_1,…,I_5 and the terms η_i
-- statement:
--   Fix reals $\delta,a,b$ and a random variable $W$ on a probability space $(\Omega,\mathcal F,P)$. The proof of Proposition (4.10) uses the notation
--
--   $$
--   \varphi(\lambda)=\frac{\lambda^2}{2}-\frac{\lambda^3}{6},\qquad \lambda=(1+\delta)\frac ab,\qquad k=\frac{a^2}{b},\qquad N=\frac{2}{\delta^2},
--   $$
--
--   the five intervals
--
--   $$
--   I_1=[0,Na],\quad I_2=(Na,(1-2\delta)b],\quad I_3=(b,2b],\quad I_4=(2b,\infty),\quad I_5=((1-2\delta)b,b],
--   $$
--
--   which partition $[0,\infty)$ under (4.12), and, for an interval $I$,
--
--   $$
--   \eta_I=\varphi(\lambda)\int_I P\{W<x\}\,e^{-\varphi(\lambda)x}\,dx ,
--   $$
--
--   with $\eta_i=\eta_{I_i}$. The terms $\eta_1,\dots,\eta_4$ are the error terms of the proof and $\eta_5$ is its main term.
--
--   **Formalization Note** The page prints (4.14) as "$\varphi(\lambda)=\lambda^2/2>\lambda^3/6$"; the "$>$" is a misprint for "$-$", as the rest of the proof shows ("$0<\varphi<f$", "$\varphi(\lambda)(1-2\delta)b<\tfrac12\lambda^2(1-2\delta)b$", and the factor $\exp[\tfrac16\lambda^3(1-2\delta)b]$ in (4.20)). The integral is the Lebesgue integral on $\mathbb R$ restricted to $I$; the integrand is a nondecreasing function of $x$ times $e^{-\varphi(\lambda)x}$, hence measurable, and it is integrable whenever $\varphi(\lambda)>0$.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 109 (PDF p. 10), proof of (4.10): display (4.14) and the definitions of I_1,…,I_5 and η_i

import Mathlib
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.14), p. 109: `φ(λ) = λ²/2 − λ³/6`.
The page prints `φ(λ) = λ²/2 > λ³/6`; the `>` is a misprint for `−` (the proof uses
`0 < φ < f`, `φ(λ)(1 − 2δ)b < ½λ²(1 − 2δ)b` and the factor `exp[⅙λ³(1 − 2δ)b]` of (4.20)). -/
noncomputable def phi (lam : ℝ) : ℝ := lam ^ 2 / 2 - lam ^ 3 / 6

/-- Freedman (1975), (4.14), p. 109: `λ = (1 + δ) a / b`. -/
noncomputable def lamStar (δ a b : ℝ) : ℝ := (1 + δ) * a / b

/-- Freedman (1975), (4.14), p. 109: `k = a²/b`. -/
noncomputable def kStar (a b : ℝ) : ℝ := a ^ 2 / b

/-- Freedman (1975), (4.14), p. 109: `N = 2/δ²`. -/
noncomputable def NStar (δ : ℝ) : ℝ := 2 / δ ^ 2

/-- Freedman (1975), p. 109: `I₁ = [0, Na]`. -/
noncomputable def I1 (δ a : ℝ) : Set ℝ := Set.Icc 0 (NStar δ * a)

/-- Freedman (1975), p. 109: `I₂ = (Na, (1 − 2δ)b]`. -/
noncomputable def I2 (δ a b : ℝ) : Set ℝ := Set.Ioc (NStar δ * a) ((1 - 2 * δ) * b)

/-- Freedman (1975), p. 109: `I₃ = (b, 2b]`. -/
def I3 (b : ℝ) : Set ℝ := Set.Ioc b (2 * b)

/-- Freedman (1975), p. 109: `I₄ = (2b, ∞)`. -/
def I4 (b : ℝ) : Set ℝ := Set.Ioi (2 * b)

/-- Freedman (1975), p. 109: `I₅ = ((1 − 2δ)b, b]`. -/
def I5 (δ b : ℝ) : Set ℝ := Set.Ioc ((1 - 2 * δ) * b) b

/-- Freedman (1975), p. 109:
`η_I = φ(λ) ∫_I P{W < x} exp[−φ(λ)x] dx` with `λ = (1 + δ)a/b`, for an interval `I`
(the page's `η_i` is `eta P W δ a b I_i`). The integrand is a monotone function of `x`
times `exp[−φ(λ)x]`, hence measurable. -/
noncomputable def eta {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : Ω → ℝ)
    (δ a b : ℝ) (I : Set ℝ) : ℝ :=
  phi (lamStar δ a b) *
    ∫ x in I, P.real {ω | W ω < x} * Real.exp (-(phi (lamStar δ a b) * x))

end FreedmanTail.LowerTail


