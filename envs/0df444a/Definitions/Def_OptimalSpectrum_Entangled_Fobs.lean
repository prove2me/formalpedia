-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_Fobs
-- name    : OptimalSpectrum_Entangled_Fobs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:54.714973+00:00
-- url     : https://prove2.me/theorems/522a225b-d622-403b-b087-986e26fcd852
-- title:
--   Polynomial moment observable $F_p=\sum_m p_m M_m$
-- statement:
--   For a real polynomial $p(x)=\sum_{m=0}^K p_m x^m$,
--
--   $$F_p=\sum_{m=0}^{K}p_m M_m .$$
--
--   Its measured value is the entangled moment estimate $\widehat F_p$ of $\mathrm{tr}\,p(\sigma)$.
--
--   **Formalization Note** The sum runs up to the degree of $p$, which gives the same operator for every $K\ge\deg p$.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.1.2, p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_momentObs

namespace OptimalSpectrum.Entangled

/-- **Polynomial moment observable `F_p`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.1.2, printed p. 21 (PDF p. 23): "For a polynomial p(x) = ∑_(m=0)^K p_m x^m of degree at
most K, set F_p := ∑_(m=0)^K p_m M_m."

**Formalization Note.** The sum runs over `m ≤ deg p`; coefficients beyond the degree are zero, so
this is the page's sum for every `K ≥ deg p`. Real coefficients act on complex matrices through
`ℝ ⊆ ℂ`. -/
noncomputable def Fobs (d n : ℕ) (Pbar : Matrix (Fin d) (Fin d) ℂ) (p : Polynomial ℝ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∑ m ∈ Finset.range (p.natDegree + 1), ((p.coeff m : ℝ) : ℂ) • momentObs d n Pbar m

end OptimalSpectrum.Entangled


