-- Prove2me | Definitions.Def_GravityNonRenorm_Defs
-- name    : GravityNonRenorm_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:27:11.533699+00:00
-- url     : https://prove2.me/theorems/8ac4d710-4ec3-4b32-be2c-0f5d15c0f73d
-- title:
--   Model for Shomer's black-hole vs CFT entropy argument
-- statement:
--   This definition file fixes the physical model used by every statement of the mission (Shomer, arXiv:0709.3555, Secs. IV–V).
--
--   1. $\mathrm{Vol}(S^n)=\dfrac{2\pi^{(n+1)/2}}{\Gamma\!\left(\frac{n+1}{2}\right)}$, the area of the unit round sphere $S^n$ (`sphereArea n`).
--   2. $\omega_n=\dfrac{16\pi}{n\,\mathrm{Vol}(S^n)}$, the constant appearing below Eq. (31) (`omega n`).
--   3. The CFT entropy as a function of energy (Eqs. 29–30): with $T(E)=\bigl(E/(bR^{d-1})\bigr)^{1/d}$,
--   $$S_{\rm CFT}(E)=a\,\bigl(R\,T(E)\bigr)^{d-1}$$ (`cftEntropyOfEnergy d a b R E`).
--   4. The Schwarzschild and Schwarzschild–AdS metric functions (Eqs. 31, 33):
--   $$f(r)=1-\frac{\omega_{d-2}G_NM}{r^{d-3}},\qquad f_{\rm AdS}(r)=1-\frac{\omega_{d-2}G_NM}{r^{d-3}}+\frac{r^2}{R_{\rm AdS}^2}.$$
--   5. The Bekenstein–Hawking entropy $S=A/(4G_N)$.
--   6. The horizon radius $r_H$ = the supremum (largest element) of the set of positive zeros of $f$ (resp. $f_{\rm AdS}$), and the black-hole entropy $S_{\rm BH}(M)=\mathrm{Vol}(S^{d-2})\,r_H^{d-2}/(4G_N)$ (Eqs. 32, 34).
--
--   These definitions are the shared model on which every theorem of the mission is stated.
--
--   **Formalization Note** Horizon radii use `sSup`, which returns $0$ on an empty (or unbounded) set; the mission's statements only use them for $M>0$ or asymptotically. Natural-number subtraction is used in exponents such as $d-3$; statements carry the dimension bounds that make these exact.
-- source:
--   Assaf Shomer, A pedagogical explanation for the non-renormalizability of gravity, arXiv:0709.3555v2 [hep-th] (2007), https://arxiv.org/abs/0709.3555, Sec. IV Eqs. (29)-(30), Sec. V Eqs. (31)-(34)

import Mathlib

namespace GravityNonRenorm

open Real

/-- Area (`(n)`-dimensional volume) of the unit round sphere `Sⁿ ⊂ ℝⁿ⁺¹`:
`Vol(Sⁿ) = 2 π^{(n+1)/2} / Γ((n+1)/2)`. -/
noncomputable def sphereArea (n : ℕ) : ℝ :=
  2 * π ^ (((n : ℝ) + 1) / 2) / Real.Gamma (((n : ℝ) + 1) / 2)

/-- Shomer's constant `ω_n = 16π / (n · Vol(Sⁿ))` (text below Eq. (31)). -/
noncomputable def omega (n : ℕ) : ℝ :=
  16 * π / ((n : ℝ) * sphereArea n)

/-- Entropy of a `d`-dimensional conformal field theory on `ℝ_time × S^{d-1}` (sphere radius `R`)
as a function of its energy `E`, obtained from Eq. (29), `S = a (RT)^{d-1}`, `E = b R^{d-1} T^d`,
by eliminating the temperature: `T(E) = (E / (b R^{d-1}))^{1/d}` and `S(E) = a (R T(E))^{d-1}`. -/
noncomputable def cftEntropyOfEnergy (d : ℕ) (a b R E : ℝ) : ℝ :=
  a * (R * (E / (b * R ^ (d - 1))) ^ ((1 : ℝ) / d)) ^ (d - 1)

/-- Metric function of the `d`-dimensional Schwarzschild solution, Eq. (31):
`f(r) = 1 - ω_{d-2} G_N M / r^{d-3}`. -/
noncomputable def schwarzschildF (d : ℕ) (G M r : ℝ) : ℝ :=
  1 - omega (d - 2) * G * M / r ^ (d - 3)

/-- Metric function of the `d`-dimensional Schwarzschild–AdS solution, Eq. (33):
`f(r) = 1 - ω_{d-2} G_N M / r^{d-3} + r² / R_AdS²`. -/
noncomputable def adsSchwarzschildF (d : ℕ) (G M RAdS r : ℝ) : ℝ :=
  1 - omega (d - 2) * G * M / r ^ (d - 3) + r ^ 2 / RAdS ^ 2

/-- Bekenstein–Hawking entropy `S = A / (4 G_N)` of a horizon of area `A`. -/
noncomputable def bekensteinHawkingEntropy (G A : ℝ) : ℝ :=
  A / (4 * G)

/-- Horizon radius of the `d`-dimensional Schwarzschild black hole of mass `M`:
the largest positive zero of `f` (Eq. (31)). -/
noncomputable def flatHorizonRadius (d : ℕ) (G M : ℝ) : ℝ :=
  sSup {r : ℝ | 0 < r ∧ schwarzschildF d G M r = 0}

/-- Horizon radius of the `d`-dimensional Schwarzschild–AdS black hole of mass `M`:
the largest positive zero of `f` (Eq. (33)). -/
noncomputable def adsHorizonRadius (d : ℕ) (G M RAdS : ℝ) : ℝ :=
  sSup {r : ℝ | 0 < r ∧ adsSchwarzschildF d G M RAdS r = 0}

/-- Bekenstein–Hawking entropy of the `d`-dimensional Schwarzschild black hole of energy `M`,
Eq. (32): horizon area `A = Vol(S^{d-2}) r_H^{d-2}`. -/
noncomputable def flatBHEntropy (d : ℕ) (G M : ℝ) : ℝ :=
  bekensteinHawkingEntropy G (sphereArea (d - 2) * flatHorizonRadius d G M ^ (d - 2))

/-- Bekenstein–Hawking entropy of the `d`-dimensional Schwarzschild–AdS black hole of energy `M`,
Eq. (34): horizon area `A = Vol(S^{d-2}) r_H^{d-2}`. -/
noncomputable def adsBHEntropy (d : ℕ) (G M RAdS : ℝ) : ℝ :=
  bekensteinHawkingEntropy G (sphereArea (d - 2) * adsHorizonRadius d G M RAdS ^ (d - 2))

end GravityNonRenorm


