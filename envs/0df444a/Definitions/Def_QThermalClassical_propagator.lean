-- Prove2me | Definitions.Def_QThermalClassical_propagator
-- name    : QThermalClassical_propagator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:43.737825+00:00
-- url     : https://prove2.me/theorems/731b2d05-cb8e-4e9b-8754-2e8e8e08bd0b
-- title:
--   Propagator $e^{-\eta H}e^{\eta(H-H')}$ and the coefficients $f_t$
-- statement:
--   For operators $H,H'$ and real $\eta$, the **propagator** is
--   $$
--   e^{-\eta H}e^{\eta(H-H')},
--   $$
--   used with $H'=H_{(a^*)}$ (eq. (15), Lemma 8) and $\eta=\beta$ or $\beta/2$. The **Boltzmann factor** is $e^{-\eta H}$. The coefficients of Lemma 8 are defined by
--   $$
--   f_0(H,H')=I,\qquad f_{t+1}(H,H')=-[H,f_t(H,H')]-f_t(H,H')\,H'.
--   $$
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), eq. (15), p.12; Lemma 8, eq. (54), p.21

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- The Boltzmann factor `e^{−ηH}`. -/
noncomputable def boltz (H : Op Q) (η : ℝ) : Op Q :=
  NormedSpace.exp (((-η : ℝ) : ℂ) • H)

/-- The propagator `e^{−ηH} e^{η(H − H')}` (eq. (15) with `η = β/2`; Lemma 8 with `η = β`).

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), eq. (15), p.12; Lemma 8, eq. (54), p.21. -/
noncomputable def propagator (H H' : Op Q) (η : ℝ) : Op Q :=
  NormedSpace.exp (((-η : ℝ) : ℂ) • H) * NormedSpace.exp (((η : ℝ) : ℂ) • (H - H'))

/-- The coefficients `f_t(H, H')` of Lemma 8: `f_0 = I` and
`f_{t+1} = −[H, f_t] − f_t H'` (arXiv:2607.28536, Lemma 8, p.21). -/
def fSeq (H H' : Op Q) : ℕ → Op Q
  | 0 => 1
  | t + 1 => -(H * fSeq H H' t - fSeq H H' t * H) - fSeq H H' t * H'

end QThermalClassical


