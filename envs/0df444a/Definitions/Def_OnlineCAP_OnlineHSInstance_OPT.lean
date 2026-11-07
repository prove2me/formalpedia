-- Prove2me | Definitions.Def_OnlineCAP_OnlineHSInstance_OPT
-- name    : OnlineCAP_OnlineHSInstance_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:25.931619+00:00
-- url     : https://prove2.me/theorems/871666b9-b564-4518-88c9-a9625fb77ce6
-- title:
--   Offline optimum OPT
-- statement:
--   For an instance with ground set $G$ and costs $c$, and a request list $s$, the **offline optimum** is
--
--   $$\mathrm{OPT}(s)=\min\Big\{\sum_{e\in H}c(e)\;:\;H\subseteq G,\ H\cap\mathrm{cov}(r)\neq\emptyset\text{ for every request } r\text{ of } s\Big\},$$
--
--   the least cost of a set of elements hitting every request, chosen with knowledge of the whole sequence.
--
--   **Formalization Note** Written as a real infimum. For a valid list the set of feasible $H$ is finite and nonempty ($H=G$ is feasible), so the infimum is a minimum; on a list without feasible solutions Lean returns $0$, which no theorem uses.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), §2.2, p.10

import Mathlib
import Definitions.Def_OnlineCAP_OnlineHSInstance

namespace OnlineCAP

/-- **The offline optimum `OPT`.** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), §2.2, p.10 (PDF p.10): "OPT is the cost of the optimal
offline solution that knows the entire request sequence in advance."

`I.OPT s` is the least cost `∑_{e ∈ H} c(e)` of a set `H ⊆ G` hitting every request of `s`.

**Formalization Note.** A real infimum (`sInf`) over a finite set of values: for a valid list the
set is nonempty (`H = G`), so `OPT` is a genuine minimum. On a list with no feasible solution the
value is the junk `0`; every theorem only uses `OPT` on valid lists. -/
noncomputable def OnlineHSInstance.OPT {U Req : Type} (I : OnlineHSInstance U Req)
    (s : List Req) : ℝ :=
  sInf ((fun H : Finset U => ∑ e ∈ H, I.c e) ''
    {H : Finset U | H ⊆ I.G ∧ ∀ r ∈ s, ∃ e ∈ H, e ∈ I.cov r})

end OnlineCAP


