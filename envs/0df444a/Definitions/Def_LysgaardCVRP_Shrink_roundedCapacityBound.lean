-- Prove2me | Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
-- name    : LysgaardCVRP_Shrink_roundedCapacityBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:29:16.9211+00:00
-- url     : https://prove2.me/theorems/1547316b-892a-4fd5-9413-d7343699d294
-- title:
--   Rounded capacity bound $k(S) = \lceil q(S)/Q \rceil$
-- statement:
--   For a set $S$ of customers with total demand $q(S)$ and vehicle capacity $Q > 0$, the **rounded capacity bound** is
--
--   $$k(S) = \left\lceil \frac{q(S)}{Q} \right\rceil .$$
--
--   It is the obvious lower bound on the bin-packing number $r(S)$. Replacing $r(S)$ by $k(S)$ in the capacity inequalities gives the **rounded capacity inequalities** (RCIs) $x(\delta(S)) \ge 2k(S)$, which are the ones the branch-and-cut algorithm separates.
--
--   **Formalization Note** The natural-number ceiling `⌈·⌉₊` is used; its argument is nonnegative under the standing hypotheses $Q > 0$ and $q_i > 0$.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), p. 424 (PDF p. 2), §1, k(S) and the rounded capacity inequalities

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_demand

namespace LysgaardCVRP.Shrink

/-- The rounded capacity bound $k(S) = \lceil q(S)/Q \rceil$ of Lysgaard, Letchford & Eglese,
Math. Program. Ser. A 100 (2004), §1, p. 424 (PDF p. 2), the right-hand side (divided by 2) of the
rounded capacity inequalities (RCIs) $x(\delta(S)) \ge 2k(S)$.

**Formalization Note.** `⌈·⌉₊` is the natural-number ceiling. The theorems assume $Q > 0$ and
$q_i > 0$, so the argument is nonnegative and the ceiling is the ordinary one. -/
noncomputable def roundedCapacityBound {n : ℕ} (q : Fin (n + 1) → ℕ) (Q : ℝ)
    (S : Finset (Fin (n + 1))) : ℕ :=
  ⌈demand q S / Q⌉₊

end LysgaardCVRP.Shrink


