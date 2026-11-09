-- Prove2me | Definitions.Def_QCSepTotal_hellingerSq
-- name    : QCSepTotal_hellingerSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:31:00.568056+00:00
-- url     : https://prove2.me/theorems/95b3b737-da4d-4ade-9f17-2abc314e023b
-- title:
--   Squared Hellinger distance $h^2(P,Q)=1-\sum_z\sqrt{P(z)Q(z)}$
-- statement:
--   For probability distributions $P, Q$ on a common discrete space, the **squared Hellinger distance** is
--   $$h^2(P,Q)=1-\sum_z\sqrt{P(z)\,Q(z)},$$
--   and the Hellinger distance is $h=\sqrt{h^2}$. No factor $\tfrac12$ appears, exactly as printed.
--
--   It enters through inequality (1) and the cut-and-paste property of Fact 1, which together bound the change in a transcript distribution when one party's input changes.
--
--   **Formalization Note** The sum is an infinite sum over a discrete space; its summands are bounded by $(P(z)+Q(z))/2$, so it never takes a junk value.
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), §2, p.3 (squared Hellinger distance)

import Mathlib

namespace QCSepTotal

/-- **Squared Hellinger distance** `h²(P, Q) = 1 − ∑_z √(P(z) Q(z))` (F. Le Gall, *Improved
Separations between Quantum and Classical Communication Complexity of Total Functions*,
arXiv:2609.16726, held version sha256 970e1476…, §2, p.3); the Hellinger distance is
`h = √h²`.

**Formalization Note.** Distributions are `PMF`s and the sum is a `tsum`, so the definition also
covers the countable transcript space. The family `√(P z Q z)` is summable for two `PMF`s (it is
bounded by `(P z + Q z)/2`), so the `tsum` never takes its junk value; on a finite type it is the
finite sum of the paper. No factor `½` is used, exactly as printed. -/
noncomputable def hellingerSq {α : Type*} (P Q : PMF α) : ℝ :=
  1 - ∑' z, Real.sqrt ((P z).toReal * (Q z).toReal)

end QCSepTotal


