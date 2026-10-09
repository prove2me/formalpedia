-- Prove2me | Definitions.Def_MHSpectralGap_LocalLip_PathMetric
-- name    : MHSpectralGap_LocalLip_PathMetric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:53:59.907734+00:00
-- url     : https://prove2.me/theorems/21c1a8c9-e739-4d36-8bc1-26591e2e7118
-- title:
--   (3.6), p. 22 and Lemma 3.5, p. 22 — the weighted path distance d̄, d = 1 ∧ d̄, and the length bound J
-- statement:
--   Let $H$ be a real normed space and $\eta,\varepsilon$ real parameters. For $T\ge0$ and $x,y\in H$ let
--
--   $$\mathsf A(T,x,y)=\{\psi\in C^1([0,T],H):\ \psi(0)=x,\ \psi(T)=y,\ \|\dot\psi\|=1\}$$
--
--   be the unit-speed paths from $x$ to $y$ of length $T$. The paper's (3.6) defines
--
--   $$\bar d(x,y)=\inf_{T,\ \psi\in\mathsf A(T,x,y)}\frac1\varepsilon\int_0^T\exp(\eta\|\psi(t)\|)\,dt,\qquad d(x,y)=1\wedge\bar d(x,y).$$
--
--   So $\bar d$ is a path length in which the arc element is weighted by $e^{\eta\|\psi\|}$: two points far from the origin must be closer in norm to be "close" for $d$. Lemma 3.5 also uses
--
--   $$J=\varepsilon\exp\bigl(-\eta\,((\|x\|\vee\|y\|-\varepsilon)\vee0)\bigr).$$
--
--   The distance $d$ replaces the distance $1\wedge\|x-y\|/\varepsilon$ of the globally Lipschitz case and is the distance of Theorem 2.14.
--
--   **Formalization Note** Paths are functions $\mathbb R\to H$ of which only the values on $[0,T]$ matter; $C^1([0,T],H)$ is continuous differentiability on the closed interval, and unit speed is imposed on the open interval $(0,T)$. For $T>0$ this is the same as unit speed on $[0,T]$ (the derivative is continuous); for $T=0$ it admits the constant path, so $\bar d(x,x)=0$. The infimum is taken in $[0,\infty]$ over $T\ge0$, so it is $+\infty$ (and $d=1$) if no admissible path exists, never a junk $0$; $d$ is the real number $\min(1,\bar d)$. In $J$ the "$\vee0$" applies to $\|x\|\vee\|y\|-\varepsilon$, as in the proof of Lemma 3.5.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 22, (3.6) and the J of Lemma 3.5 (1); also p. 13, Theorem 2.14

import Mathlib

open scoped ENNReal

namespace MHSpectralGap.LocalLip

/-- `A(T, x, y)` (3.6): `C¹` paths `ψ : [0, T] → H` (represented on `ℝ`, only the values on
`[0, T]` matter) with `ψ(0) = x`, `ψ(T) = y` and unit speed `‖ψ̇(t)‖ = 1` for `0 < t < T`. -/
def pathSet {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] (x y : H) (T : ℝ) :
    Set (ℝ → H) :=
  {ψ | ψ 0 = x ∧ ψ T = y ∧ ContDiffOn ℝ 1 ψ (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Ioo 0 T, ‖deriv ψ t‖ = 1}

/-- `d̄(x, y) = inf_{T ≥ 0, ψ ∈ A(T, x, y)} (1/ε) ∫_0^T exp(η ‖ψ(t)‖) dt` (3.6), an infimum in
`[0, ∞]` (equal to `∞` when no admissible path exists). -/
noncomputable def dBarE {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] (η ε : ℝ)
    (x y : H) : ℝ≥0∞ :=
  ⨅ (T : ℝ) (_ : 0 ≤ T) (ψ ∈ pathSet x y T),
    ENNReal.ofReal ((1 / ε) * ∫ t in (0)..T, Real.exp (η * ‖ψ t‖))

/-- `d(x, y) = 1 ∧ d̄(x, y)` (3.6). -/
noncomputable def dPath {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] (η ε : ℝ)
    (x y : H) : ℝ :=
  (min 1 (dBarE η ε x y)).toReal

/-- `J = ε exp(−η((‖x‖ ∨ ‖y‖ − ε) ∨ 0))` (Lemma 3.5 (1)). -/
noncomputable def Jlen {H : Type} [NormedAddCommGroup H] (η ε : ℝ) (x y : H) : ℝ :=
  ε * Real.exp (-(η * max (max ‖x‖ ‖y‖ - ε) 0))

end MHSpectralGap.LocalLip


