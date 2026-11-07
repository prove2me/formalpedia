-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_cCoef
-- name    : OptimalSpectrum_Entangled_cCoef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:54.684849+00:00
-- url     : https://prove2.me/theorems/2f82c15a-5608-4139-8b79-287d37f1482a
-- title:
--   Scheme coefficients $c_r$, Eq. (35)
-- statement:
--   For $r\ge1$,
--
--   $$c_r=\frac1{(r-1)!}\cdot\begin{cases}3^r\,d^{\uparrow r},&\text{unentangled},\\[2pt] \prod_{j=0}^{r-1}(1+jL),&\text{entangled},\end{cases}$$
--
--   where $d^{\uparrow r}=d(d+1)\cdots(d+r-1)$ is the rising factorial. These constants carry the whole dependence of the variance bounds on the measurement scheme (Lemma 7.1, Corollary 7.2).
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Lemma 7.1, Eq. (35), p. 20 (PDF p. 22)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_Scheme

namespace OptimalSpectrum.Entangled

/-- **Scheme coefficients `c_r`, Eq. (35).**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Lemma 7.1, Eq. (35), printed p. 20 (PDF p. 22): "where, for r ⩾ 1,
c_r := (1/(r − 1)!) · { 3^r d^↑r, unentangled; ∏_(j=0)^(r−1)(1 + jL), entangled. }"

`d^↑r = d(d+1)⋯(d+r−1)` is the rising factorial (§4, printed p. 11).

**Formalization Note.** The rising factorial is written as the product `∏_(j<r) (d + j)`. The
coefficient is used for `r ≥ 1` only. -/
noncomputable def cCoef (s : Scheme) (d : ℕ) (L : ℝ) (r : ℕ) : ℝ :=
  (1 / ((r - 1).factorial : ℝ)) *
    match s with
    | Scheme.unentangled => 3 ^ r * ∏ j ∈ Finset.range r, ((d : ℝ) + j)
    | Scheme.entangled => ∏ j ∈ Finset.range r, (1 + (j : ℝ) * L)

end OptimalSpectrum.Entangled


