-- Prove2me | Definitions.Def_BBPSSW_Distill_recurrenceMap
-- name    : BBPSSW_Distill_recurrenceMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:41.465989+00:00
-- url     : https://prove2.me/theorems/2a83e6fc-836a-47c6-95d0-e61e1c655880
-- title:
--   Recurrence relation $F'(F)$, Eq. (7)
-- statement:
--   The fidelity after one successful recurrence step:
--
--   $$F'(F)=\frac{F^2+\frac19(1-F)^2}{F^2+\frac23F(1-F)+\frac59(1-F)^2}.$$
--
--   **Formalization Note** The denominator equals $\frac89F^2-\frac49F+\frac59>0$ for every real $F$, so the division is always defined.
-- source:
--   Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, Purification of Noisy Entanglement and Faithful Teleportation via Noisy Channels, arXiv:quant-ph/9511027v2, Eq. (7), p. 3

import Mathlib

namespace BBPSSW.Distill

/-- **The recurrence relation, Eq. (7).**
Bennett, Brassard, Popescu, Schumacher, Smolin, Wootters, *Purification of Noisy Entanglement
and Faithful Teleportation via Noisy Channels*, arXiv:quant-ph/9511027v2, Eq. (7), p. 3: "F′ = (F^2 + (1/9)(1−F)^2) / (F^2 + (2/3)F(1−F) + (5/9)(1−F)^2). (7)"

**Formalization Note.** The denominator equals (8/9)F² − (4/9)F + 5/9, which is positive for
every real F, so the division never meets Lean's `x / 0 = 0` convention. -/
noncomputable def recurrenceMap (F : ℝ) : ℝ :=
  (F ^ 2 + (1 / 9) * (1 - F) ^ 2) / (F ^ 2 + (2 / 3) * F * (1 - F) + (5 / 9) * (1 - F) ^ 2)

end BBPSSW.Distill


