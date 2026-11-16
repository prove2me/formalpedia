-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_allocT
-- name    : AutobidSPPE_Supplement_allocT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:38:13.895195+00:00
-- url     : https://prove2.me/theorems/5516af6e-cfdd-41a7-a8dc-c230576ebf18
-- title:
--   Throttling allocation $x_i$ for a participation set
-- statement:
--   Given a realized participation set $P$ and value profile $v$, participants bid their values and non-participants receive nothing. The **allocation indicator** $x_i$ of bidder $i$ equals $1$ if $i\in P$ and $i$ is the participant chosen by the tie rule among the participants with the highest value, and $0$ otherwise. An empty auction has no winner.
--
--   **Formalization Note** Section 3.2 fixes the smallest-index tie rule; the theorems allow every deterministic single-winner tie rule (the published `AutobidSPPE.TieRule`), which contains it.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Problem 1.2, p.4; §3.2, p.26

import Mathlib
import Definitions.Def_AutobidSPPE_TieRule

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The throttling allocation indicator `xᵢ ∈ {0, 1}` for a realized participation set `P` and
value profile `v` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), Problem 1.2, p.4; §3.2, p.26): participants bid their values, non-participants
receive nothing, and the item goes to the participant chosen by the tie rule among the participants with
the highest value. An empty auction has no winner.

**Formalization Note** §3.2 fixes the smallest-index tie rule; the theorems quantify over every
deterministic single-winner tie rule (`AutobidSPPE.TieRule`), which contains it. -/
noncomputable def allocT {n : ℕ} (tie : TieRule n) (P : Finset (Fin n)) (v : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  if i ∈ P ∧ tie.pick (P.filter fun j => ∀ k ∈ P, v k ≤ v j) = i then 1 else 0

end AutobidSPPE.Supplement


