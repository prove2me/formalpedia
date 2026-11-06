-- Prove2me | Definitions.Def_OmniMix_Feta
-- name    : OmniMix_Feta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:21.798819+00:00
-- url     : https://prove2.me/theorems/d4c3a565-a11b-4190-8bb8-5b2589a9e959
-- title:
--   $F^\eta_{p,y}(h)$
-- statement:
--   For real $\eta,p,h$ and an outcome value $y$,
--   $$
--   F^\eta_{p,y}(h)=\exp\big(\eta h(y-p)-\eta^2p(1-p)h^2\big).
--   $$
--   It is the per-round weight factor of Algorithm 2 for a single forecast $p$.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, Lemma 3.4, §3.2, p.14

import Mathlib

namespace OmniMix

/-- **`F^η_{p,y}(h) = exp(ηh(y − p) − η²p(1 − p)h²)`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, Lemma 3.4, §3.2, p.14.

**Formalization Note.** The outcome enters through its real value `y` (`0` or `1`). -/
noncomputable def Feta (η p y h : ℝ) : ℝ :=
  Real.exp (η * h * (y - p) - η ^ 2 * p * (1 - p) * h ^ 2)

end OmniMix


