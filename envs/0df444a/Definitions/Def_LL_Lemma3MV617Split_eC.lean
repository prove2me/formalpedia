-- Prove2me | Definitions.Def_LL_Lemma3MV617Split_eC
-- name    : LL_Lemma3MV617Split_eC
-- status  : Definition
-- author  : @sthubbar
-- created : 2026-11-25T13:03:05.852159+00:00
-- url     : https://prove2.me/theorems/7859d653-fe72-581e-a65e-78de082f6931
-- title:
--   The additive character $e(x)=e^{2\pi i x}$
-- statement:
--   For real $x$, $e(x)=\exp(2\pi i x)\in\mathbb C$.

import Mathlib

namespace LL_Lemma3MV617Split

noncomputable section

open Real MeasureTheory Polynomial

noncomputable def eC (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

end

end LL_Lemma3MV617Split


