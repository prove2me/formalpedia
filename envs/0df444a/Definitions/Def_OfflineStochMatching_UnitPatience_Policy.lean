-- Prove2me | Definitions.Def_OfflineStochMatching_UnitPatience_Policy
-- name    : OfflineStochMatching_UnitPatience_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:35:57.02485+00:00
-- url     : https://prove2.me/theorems/191a2166-be60-4689-a24d-df849d5d3d53
-- title:
--   Probing algorithm as an adaptive probing policy
-- statement:
--   A **probing policy** maps the history so far (the list of probed edges together with their observed activeness) either to the next edge to probe or to *stop*. It may choose the next probe based on the realizations of past probes, but cannot see edges it has not probed.
--
--   **Formalization Note** Policies are deterministic. A randomized probing algorithm is a mixture of deterministic ones, so its expected weight is at most that of the best deterministic policy; the optimal probing algorithm against which approximation ratios are measured may therefore be taken deterministic.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §1, p. 2 (algorithms probe the edges in any order based on the realizations of past probes)

import Mathlib

namespace OfflineStochMatching.UnitPatience

/-- **Probing algorithms (adaptive probing policies).**
Brubach, Grammel, Ma, MacRury, Srinivasan, *Improved Guarantees for Offline Stochastic Matching via
New Ordered Contention Resolution Schemes*, arXiv:2106.06892v3, §1, p. 2: "Most generally, we
allow algorithms to probe the edges in any order based on the realizations of past probes."

A policy maps the history so far, the list of probed edges with their observed activeness
(`(e, true)` = probed and active), to the next edge to probe, or to `none` (stop).

**Formalization Note.** Policies are deterministic; a randomized probing algorithm is a mixture
of deterministic ones, so its expected value is at most that of the best deterministic one, and
the optimal probing algorithm against which approximation ratios are measured (p. 7) may be
taken deterministic. A policy sees only the history, so it cannot anticipate unprobed edges. -/
abbrev Policy (E : Type*) : Type _ := List (E × Bool) → Option E

end OfflineStochMatching.UnitPatience


