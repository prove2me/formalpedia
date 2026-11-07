-- Prove2me | Definitions.Def_SecondBestBT_gammaLimit
-- name    : SecondBestBT_gammaLimit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:12.400223+00:00
-- url     : https://prove2.me/theorems/936eebf5-8495-4307-9f6d-37230dd7aa20
-- title:
--   Gamma expression $L(\alpha)$ of Lemma 5.6
-- statement:
--   For $\alpha>0$,
--   $$
--   L(\alpha)=\frac{1}{1+\alpha}\,\frac{\Gamma\big(\frac{1}{1+\alpha}\big)^2}{\Gamma\big(\frac{2}{1+\alpha}\big)} .
--   $$
--   For example $L(1)=\pi/2$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Lemma 5.6, p.20

import Mathlib

namespace SecondBestBT

/-- The Gamma expression `L(α) = (1/(1 + α)) · Γ(1/(1 + α))² / Γ(2/(1 + α))` of Lemma 5.6
(Liu–Qin–Ren–Wang, arXiv:2606.03849, held version sha256 17184930…, Lemma 5.6, p.20).

**Formalization Note** `Real.Gamma`; for `α > 0` both arguments lie in `(0, 2)`, where `Γ` is
positive. -/
noncomputable def gammaLimit (α : ℝ) : ℝ :=
  1 / (1 + α) * Real.Gamma (1 / (1 + α)) ^ 2 / Real.Gamma (2 / (1 + α))

end SecondBestBT


