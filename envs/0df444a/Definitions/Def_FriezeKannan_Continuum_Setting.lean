-- Prove2me | Definitions.Def_FriezeKannan_Continuum_Setting
-- name    : FriezeKannan_Continuum_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:53.432257+00:00
-- url     : https://prove2.me/theorems/b669daa4-417c-4bc6-8da6-08ee81f165f1
-- title:
--   §8, p. 217 — f(S, T), ‖f‖₂ and cut functions CUT(S, T, d) on [0,1]²
-- statement:
--   This module fixes the objects of §8 (*Continuous case*) of Frieze and Kannan (1999), p. 217.
--
--   The domain is the unit square $[0,1]^2$, with Lebesgue measure $dx\,dy$ (the product of Lebesgue measure on $[0,1]$ with itself). For a real function $f$ on $[0,1]^2$:
--
--   1. For subsets $S,T\subseteq[0,1]$, the **rectangle integral** is
--   $$f(S,T)=\int_{S\times T} f(x,y)\,dx\,dy.$$
--   2. The **$L^2$ norm** is
--   $$\|f\|_2=\Big(\int_{[0,1]^2} f(x,y)^2\,dx\,dy\Big)^{1/2}.$$
--   3. For $S,T\subseteq[0,1]$ and a real $d$, the **cut function** $\mathrm{CUT}(S,T,d)$ equals $d$ on $S\times T$ and $0$ elsewhere.
--   4. For a finite family $(S_t,T_t,d_t)_{t=1}^{s}$, the function $f_1+\dots+f_s$ with $f_t=\mathrm{CUT}(S_t,T_t,d_t)$ is the pointwise sum of these cut functions (the empty sum, $s=0$, is the zero function).
--
--   The measure $|S|$ of a set $S\subseteq[0,1]$ is its Lebesgue measure, a number in $[0,1]$.
--
--   These are the objects in which the continuous analogue of the matrix cut decomposition (Theorem 12) is stated. The cut norm $\|f\|_C=\sup_{S,T}|f(S,T)|$ over measurable $S,T$ is not given a separate definition: a bound $\|f\|_C\le c$ is stated as $|f(S,T)|\le c$ for all measurable $S,T$.
--
--   **Formalization Note.** $[0,1]$ is Mathlib's `unitInterval` with its Lebesgue measure, and the square is the product type with the product measure, so sets $S,T$ need no side condition $S\subseteq[0,1]$. $\|f\|_2$ is defined as the square root of the Bochner integral of $f^2$; it is the true $L^2$ norm only when $f$ is square integrable, and every theorem using it assumes this. The page restricts $f(S,T)$ and cut functions to measurable $S,T$; the definitions accept any sets, and every theorem that uses them requires `MeasurableSet` on each set it quantifies over.
-- source:
--   Frieze and Kannan, Quick approximation to matrices and applications, Combinatorica 19 (1999), p. 217, §8 Continuous case (definitions of ‖f‖₂, f(S, T), ‖f‖_C and CUT(S, T, d))

import Mathlib

namespace FriezeKannan.Continuum

open MeasureTheory

/-- The unit square `[0,1]²`, with Lebesgue (product) measure `volume = volume.prod volume`. -/
abbrev Sq := unitInterval × unitInterval

/-- `f(S, T) = ∫_{S×T} f(x, y) dx dy` (Frieze–Kannan §8, p. 217). -/
noncomputable def rectInt (f : Sq → ℝ) (S T : Set unitInterval) : ℝ :=
  ∫ p in S ×ˢ T, f p

/-- `‖f‖₂ = (∫_{[0,1]²} f(x, y)² dx dy)^{1/2}` (Frieze–Kannan §8, p. 217). -/
noncomputable def l2Norm (f : Sq → ℝ) : ℝ :=
  Real.sqrt (∫ p, f p ^ 2)

/-- The cut function `CUT(S, T, d)`: equal to `d` on `S × T` and `0` elsewhere
(Frieze–Kannan §8, p. 217). -/
noncomputable def cutFun (S T : Set unitInterval) (d : ℝ) : Sq → ℝ :=
  (S ×ˢ T).indicator (fun _ => d)

/-- The sum `f₁ + ⋯ + f_s` of the cut functions `f_t = CUT(S_t, T_t, d_t)`, `t ∈ Fin s`. -/
noncomputable def cutFunSum {s : ℕ} (Ss Ts : Fin s → Set unitInterval) (d : Fin s → ℝ) :
    Sq → ℝ :=
  fun p => ∑ t, cutFun (Ss t) (Ts t) (d t) p

end FriezeKannan.Continuum


