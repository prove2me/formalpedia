-- Prove2me | Definitions.Def_RvsCert_C
-- name    : RvsCert_C
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:07.028615+00:00
-- url     : https://prove2.me/theorems/70e1463d-3177-4926-807d-236388cbfbbd
-- title:
--   Certificate complexity $C(f)$
-- statement:
--   For a Boolean function $f$ on a finite set of bit positions, the **certificate complexity** is
--   $$
--   C(f)=\max_{x} C_x(f)=\max\{C_0(f),C_1(f)\},
--   $$
--   the largest, over all inputs, of the least size of a certificate. It is the measure in the paper's Theorem 1.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Theorem 1, p.1 (standard notion, [BdW02])

import Mathlib
import Definitions.Def_RvsCert_certAt

namespace RvsCert

/-- **Certificate complexity** `C(f)` (standard, [BdW02]; Theorem 1, p.1 of
Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): the maximum over all inputs `x` of the least size of a certificate for
`x`, i.e. `max (C0 f) (C1 f)`. -/
noncomputable def C {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) : ℕ :=
  Finset.univ.sup (certAt f)

end RvsCert


