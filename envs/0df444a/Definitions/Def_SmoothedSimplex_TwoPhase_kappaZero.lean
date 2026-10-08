-- Prove2me | Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
-- name    : SmoothedSimplex_TwoPhase_kappaZero
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:11:32.801694+00:00
-- url     : https://prove2.me/theorems/0b4f5ed3-15e3-42ba-8174-0443494ed1ca
-- title:
--   Definition 5.1.5 — bad minor and low-height events
-- statement:
--   The proof uses two positive thresholds for $n>d\ge3$ and $\sigma>0$:
--   $$\kappa_0=\frac{\sigma\min(1,\sigma)}{12d^2n^7\sqrt{\ln n}},\qquad h_0=\frac{\sigma}{4n^4}.$$
--   For a $d$-set $I$, $X_I$ indicates $s_{\min}(A_I)\le\kappa_0$. For a $(d-1)$-set $K$ and $j\notin K$, $Y_K^j$ indicates that $a_j$ is within distance $h_0$ of the span of $A_K$. The likely dyadic scales are
--   $$\mathcal K=\{2^{\lfloor\log_2 x\rfloor}:\kappa_0\le x\le\sqrt d+3d\sqrt{\ln n}\,\sigma\}.$$
--   These quantities connect the many-good-minors estimate to the two shadow bounds.
--
--   **Formalization Note** Indicators take values in $\mathbb N$ so their sums count events. Floors are integer floors of real logarithms. The interval implementation of $\mathcal K$ is exact for the positive parameters used by the theorems.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, equation (35), printed p. 60, PDF p. 60; equation (36), printed p. 61, PDF p. 61; Definition 5.1.5, printed p. 62, PDF p. 62

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_complexityBound

namespace SmoothedSimplex.TwoPhase

/-- The threshold `κ₀` of equation (35), Spielman–Teng, printed p. 60,
PDF p. 60. Used only when `n>d≥3` and `σ>0`. -/
noncomputable def kappaZero (n d : ℕ) (σ : ℝ) : ℝ :=
  σ * min 1 σ / (12 * (d : ℝ)^2 * (n : ℝ)^7 * Real.sqrt (Real.log n))

/-- The height threshold `h₀` of Definition 5.1.5, printed p. 62,
PDF p. 62. -/
noncomputable def heightZero (n : ℕ) (σ : ℝ) : ℝ :=
  σ / (4 * (n : ℝ)^4)

/-- The distance from `a_j` to the span of the vectors indexed by `K`,
as in Definition 5.1.5, printed p. 62, PDF p. 62. -/
noncomputable def height {n d : ℕ} (a : Fin n → Point d)
    (K : Finset (Fin n)) (j : Fin n) : ℝ :=
  Metric.infDist (a j) (Submodule.span ℝ (Set.range (fun i : K => a i.1)) : Set (Point d))

/-- The indicator `X_I=[s_min(A_I)≤κ₀]` of Definition 5.1.5,
printed p. 62, PDF p. 62. -/
noncomputable def badMinor {n d : ℕ} (a : Fin n → Point d) (I : Finset (Fin n))
    (σ : ℝ) : ℕ :=
  if sMin a I ≤ kappaZero n d σ then 1 else 0

/-- The indicator `Y^j_K=[dist(a_j,Span(A_K))≤h₀]` of
Definition 5.1.5, printed p. 62, PDF p. 62. -/
noncomputable def lowHeight {n d : ℕ} (a : Fin n → Point d)
    (K : Finset (Fin n)) (j : Fin n) (σ : ℝ) : ℕ :=
  if height a K j ≤ heightZero n σ then 1 else 0

/-- The set `𝒦` of equation (36), Spielman–Teng, printed p. 61,
PDF p. 61. Floors are integer floors of base-two logarithms; the integer
interval gives exactly `{2^⌊lg x⌋ : κ₀≤x≤√d+3d√(ln n)σ}` when `σ>0`. -/
noncomputable def kappaGrid (n d : ℕ) (σ : ℝ) : Finset ℝ :=
  ((Finset.Icc
    (Int.floor (Real.logb 2 (kappaZero n d σ)))
    (Int.floor (Real.logb 2 (Real.sqrt d + 3 * d * Real.sqrt (Real.log n) * σ)))).image
      (fun k : ℤ => (2 : ℝ)^k))

end SmoothedSimplex.TwoPhase


