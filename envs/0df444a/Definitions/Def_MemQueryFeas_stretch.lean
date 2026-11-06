-- Prove2me | Definitions.Def_MemQueryFeas_stretch
-- name    : MemQueryFeas_stretch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:34:22.981113+00:00
-- url     : https://prove2.me/theorems/024c746d-8af9-4b96-aae7-41c12e348cb0
-- title:
--   The stretch $T_{F,\alpha}$
-- statement:
--   For a subspace $F$ and $\alpha\in\mathbb R$,
--   $$
--   T_{F,\alpha}=\alpha P_F+P_{F^\perp}.
--   $$
--   It multiplies the component along $F$ by $\alpha$ and leaves the orthogonal component unchanged.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.1, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_MemQueryFeas_Op

namespace MemQueryFeas

/-- **The stretch `T_{F,α}`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.1, p.8 (PDF p.9): "we introduce the following notation for
stretching the space by a factor `α` along `F^⊥`: `T_{F,α} := α P_F + P_{F^⊥}`."

**Formalization Note.** `F` is given by its projection `P_F`, and `P_{F^⊥} = 1 − P_F`. The formula
multiplies the `F`-component by `α`, which is the convention used throughout the paper. -/
def stretch {d : ℕ} (F : Op d) (α : ℝ) : Op d :=
  α • F + (1 - F)

end MemQueryFeas


