-- Prove2me | Definitions.Def_NSWBetter_sortDesc
-- name    : NSWBetter_sortDesc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:04.596197+00:00
-- url     : https://prove2.me/theorems/08c45c17-f136-4cc3-a70e-ae9c318c9665
-- title:
--   Values of the goods sorted non-increasingly
-- statement:
--   For an instance with identical valuations whose goods have the multiset of values $s$, the goods are listed so that $v(g_1)\ge v(g_2)\ge\dots\ge v(g_m)$; `sortDesc s` is this list of values (0-based).
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 3, p.11 ("assume that v(g1) ≥ v(g2) ≥ · · · ≥ v(gm)")

import Mathlib

namespace NSWBetter

/-- **Sorted values.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 3, p.11: "assume that v(g1) ≥ v(g2) ≥ · · · ≥ v(gm)".

`sortDesc s` is the list of the values in the multiset `s`, sorted non-increasingly: position `k` (0-based) holds `v(g_(k+1))`.

**Formalization Note.** An instance with identical valuations is given by its number of agents `Δ` and the multiset `s` of the values of its goods; every notion of Section 3 depends only on these (round-robin bundle values do not depend on how ties are broken, p.23). -/
noncomputable def sortDesc (s : Multiset ℝ) : List ℝ := (s.sort (· ≤ ·)).reverse

end NSWBetter


