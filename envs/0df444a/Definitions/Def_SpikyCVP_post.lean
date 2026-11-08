-- Prove2me | Definitions.Def_SpikyCVP_post
-- name    : SpikyCVP_post
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:42:59.918545+00:00
-- url     : https://prove2.me/theorems/553a5d79-fa96-4cfb-8ab5-c6e9df80c12f
-- title:
--   Prior $h_p(s,r)$, Gaussian weight $\rho(x,s)$, super-Gaussian $f_p(x,r)$ and posterior $P_{x,r}$
-- statement:
--   Fix $1\le p<2$ and $r>0$. For widths $s$ in the open orthant $\mathbb R^n_{>0}$ and $x\in\mathbb R^n$ define the **prior**, the anisotropic **Gaussian weight** and the **super-Gaussian**
--
--   $$h_p(s,r)=\prod_{j=1}^n g_{p/2}\Big(\frac{\pi r^2}{s_j^2}\Big)\frac{2\pi r^2}{s_j^3},\qquad \rho(x,s)=\exp\Big(-\pi\sum_j\frac{x_j^2}{s_j^2}\Big),\qquad f_p(x,r)=\exp\Big(-\frac{\|x\|_p^p}{r^p}\Big),$$
--
--   and the **posterior** at $x$,
--
--   $$P_{x,r}(s)=\frac{\rho(x,s)\,h_p(s,r)}{f_p(x,r)}\qquad (s\in\mathbb R^n_{>0}),$$
--
--   with $P_{x,r}(s)=0$ off the orthant. The law $S\sim P_{x,r}$ is Lebesgue measure on $\mathbb R^n$ with density $P_{x,r}$. It depends only on $x$ and $r$; the algorithm samples widths from it at the current vector and then solves a Euclidean problem in the metric $\sum_k y_k^2/s_k^2$.
--
--   **Formalization Note** That $P_{x,r}$ integrates to $1$ is the identity (3.3), a milestone; the definition does not assume it. Probabilities of events that need not be measurable are stated through the measure of the complementary event.
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), §2.3, p.15 (PDF p.17); §3, Equations (3.3), (3.4), pp.16–17 (PDF pp.18–19)

import Mathlib
import Definitions.Def_PNormReg_Norms
import Definitions.Def_SpikyCVP_latt
import Definitions.Def_SpikyCVP_gStable

open Real MeasureTheory PNormReg

namespace SpikyCVP

/-- The open positive orthant `R^n_{>0}` of widths `s`. -/
def orthant (n : ℕ) : Set (Fin n → ℝ) := {s | ∀ j, 0 < s j}

/-- The prior `hp(s, r) := Π_{j=1}^n g_{p/2}(πr²/s_j²) · 2πr²/s_j³` for `s ∈ R^n_{>0}`, `r > 0`.
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), §3, p.16 (PDF p.18). -/
noncomputable def prior {n : ℕ} (p r : ℝ) (s : Fin n → ℝ) : ℝ :=
  ∏ j, gStable (p / 2) (π * r ^ 2 / s j ^ 2) * (2 * π * r ^ 2 / s j ^ 3)

/-- `ρ(x, s) := exp(−π Σ_j x_j²/s_j²)` (§3, p.16). -/
noncomputable def rho {n : ℕ} (x s : Fin n → ℝ) : ℝ :=
  Real.exp (-(π * ∑ j, x j ^ 2 / s j ^ 2))

/-- `fp(x, r) := exp(−∥x∥p^p / r^p)` (§2.3, p.15). -/
noncomputable def fp {n : ℕ} (p : ℝ) (x : Fin n → ℝ) (r : ℝ) : ℝ :=
  Real.exp (-(lpPow p x / r ^ p))

/-- The posterior density at `x`, Equation (3.4), p.17: `Px,r(s) := ρ(x, s) hp(s, r) / fp(x, r)` for
`s ∈ R^n_{>0}`.

**Formalization Note.** The density is `0` off the open orthant, where the paper does not define it, so
no width `s_j = 0` is ever divided by inside the support. -/
noncomputable def post {n : ℕ} (p : ℝ) (x : Fin n → ℝ) (r : ℝ) (s : Fin n → ℝ) : ℝ :=
  Set.indicator (orthant n) (fun s => rho x s * prior p r s / fp p x r) s

/-- The law `S ∼ Px,r` on `ℝⁿ`: Lebesgue measure with density `Px,r`.

**Formalization Note.** That this is a probability measure is the identity (3.3) (milestone); no
instance is registered here. Probabilities of events that need not be measurable are stated through the
measure of the complementary event, which is the stronger form for an outer measure. -/
noncomputable def postMeasure {n : ℕ} (p : ℝ) (x : Fin n → ℝ) (r : ℝ) : Measure (Fin n → ℝ) :=
  volume.withDensity fun s => ENNReal.ofReal (post p x r s)

end SpikyCVP


