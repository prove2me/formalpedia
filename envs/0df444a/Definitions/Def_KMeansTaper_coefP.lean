-- Prove2me | Definitions.Def_KMeansTaper_coefP
-- name    : KMeansTaper_coefP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:09.256183+00:00
-- url     : https://prove2.me/theorems/052d1135-3419-45f0-80f4-ec365645e66c
-- title:
--   The coefficients $P$, $A$, $B=\kappa P$ and $m=A-1-xB$
-- statement:
--   For a parameter $\kappa$ and a real $x$ (the paper uses $\kappa>0$ and $x\in[0,1]$) put
--
--   $$P(x)=\int_0^1 t\,e^{-tx}\,dt,\qquad A(x)=1+\kappa\int_0^1\bigl(1-e^{-tx}\bigr)\,dt,\qquad B(x)=\kappa P(x),\qquad m(x)=A(x)-1-xB(x).$$
--
--   These are the analytic coefficients of the potential of the tapered process; they enter the finite inequality SFI (Definition 2.2), the certificate $[\mathrm C]$ and the local lemma. The integrands are continuous, so the integrals are ordinary Riemann integrals.
--
--   **Formalization Note** The coefficients are functions of $x$ on all of $\mathbb R$; $A$, $B$, $m$ also take $\kappa$ as an argument.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Section 2 ("Coefficients"), p.3 (PDF p.6)

import Mathlib

namespace KMeansTaper

/-- **The coefficient `P`**, Section 2 ("Coefficients"), p.3 (PDF p.6):
`P(x) = ∫₀¹ t e^{-tx} dt`.

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b661022…fc5a3).

**Formalization Note.** Defined for every real `x`; the paper uses `x ∈ [0, 1]`. -/
noncomputable def coefP (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, (t * Real.exp (-(t * x)))

/-- **The coefficient `A`**, p.3: `A(x) = 1 + κ ∫₀¹ (1 - e^{-tx}) dt`, for a parameter `κ`. -/
noncomputable def coefA (κ x : ℝ) : ℝ := 1 + κ * ∫ t in (0 : ℝ)..1, (1 - Real.exp (-(t * x)))

/-- **The coefficient `B = κ P`**, p.3. -/
noncomputable def coefB (κ x : ℝ) : ℝ := κ * coefP x

/-- **The coefficient `m = A - 1 - x B`**, p.3. -/
noncomputable def coefM (κ x : ℝ) : ℝ := coefA κ x - 1 - x * coefB κ x

end KMeansTaper


