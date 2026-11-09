-- Prove2me | Definitions.Def_AutobidSPPE_TieRule
-- name    : AutobidSPPE_TieRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:54.429751+00:00
-- url     : https://prove2.me/theorems/499203ba-a38f-487d-9b05-ea1c3602cfd5
-- title:
--   Deterministic single-winner tie rule
-- statement:
--   A **tie rule** for $n$ bidders is a deterministic map that, given any nonempty set $S$ of bidders (the bidders whose bids attain the highest bid), selects one bidder of $S$. The auction allocates the item to exactly one bidder, chosen by the rule among the highest bidders. The paper fixes an arbitrary such rule ("An arbitrary fixed tie rule is used"); every result of the mission holds for every rule.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Problem 1.1, p.4; §2.2, p.10

import Mathlib

namespace AutobidSPPE

/-- A deterministic single-winner tie rule (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Problem 1.1, p.4: "using a fixed
tie-breaking rule"; §2.2, p.10: "An arbitrary fixed tie rule is used"). Given the set of bidders
with the highest bid, the rule picks one of them.

**Formalization Note** The theorems quantify over every tie rule. A rule is a map from
nonempty sets of bidders to one of their members. -/
structure TieRule (n : ℕ) where
  /-- the bidder chosen from a set of tied highest bidders -/
  pick : Finset (Fin n) → Fin n
  /-- the chosen bidder belongs to the set -/
  pick_mem : ∀ S : Finset (Fin n), S.Nonempty → pick S ∈ S

end AutobidSPPE


