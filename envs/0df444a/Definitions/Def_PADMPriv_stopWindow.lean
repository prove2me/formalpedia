-- Prove2me | Definitions.Def_PADMPriv_stopWindow
-- name    : PADMPriv_stopWindow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:35.105198+00:00
-- url     : https://prove2.me/theorems/3da047a6-d7f5-4673-bdad-e0eddc833473
-- title:
--   Stopping window $\{\lfloor n/2\rfloor+1,\dots,n\}$
-- statement:
--   Stop-PADM stops at a random iteration $K$ drawn from the window
--   $$
--   \{\lfloor n/2\rfloor+1,\dots,n\},
--   $$
--   which has $\lceil n/2\rceil$ elements.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Section 4.2, p.10

import Mathlib

namespace PADMPriv

/-- The random-stopping window `{⌊n/2⌋ + 1, …, n}` of Stop-PADM, Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d),
Section 4.2, p.10.

**Formalization Note** `n / 2` is natural-number division, i.e. `⌊n/2⌋`. -/
def stopWindow (n : ℕ) : Finset ℕ :=
  Finset.Icc (n / 2 + 1) n

end PADMPriv


