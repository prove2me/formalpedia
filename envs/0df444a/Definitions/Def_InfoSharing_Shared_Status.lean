-- Prove2me | Definitions.Def_InfoSharing_Shared_Status
-- name    : InfoSharing_Shared_Status
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T05:28:35.780988+00:00
-- url     : https://prove2.me/theorems/66826e83-7fde-4e89-84da-6e06b97807c2
-- title:
--   Information status of a manufacturer, §3
-- statement:
--   Each of the two manufacturers has an **information status** $X_i \in \{I, U\}$: $I$ (informed) if the retailer shares the demand signal with him, $U$ (uninformed) otherwise. For a status profile $X = (X_1, X_2)$, $n$ denotes the number of informed manufacturers, $n \in \{0,1,2\}$. For each manufacturer $i$, $j$ denotes his rival, and the profile in which $i$ alone is informed is written $(I_i, U_j)$.
--
--   These are the labels of every payoff table and contracting game of the paper.
--
--   **Formalization Note.** Manufacturers are indexed by `Fin 2`; the rival of $i$ is `1 - i`.
--
--   This is a shared definition of the series, reviewed once for both missions: `01-diseconomy-sequential` (production diseconomy, §5; Shang, Ha & Tong 2016, p. 249, §3, item 2) and `02-economy-sequential` (production economy, §6; p. 249, §3 (sequence of events, stage 2)). The cost parameter $c$ is a plain real; the missions differ only in the hypotheses their theorems put on it: $c > 0$ in the first, $c = -c_e$ with $0 < c_e < 2/(1+\phi)$ in the second.
-- source:
--   Shang, Ha & Tong, Information Sharing in a Supply Chain with a Common Retailer, Management Sci. 62(1) 2016, p. 249, §3, item 2

import Mathlib

namespace InfoSharing.Shared

/-- A manufacturer's information status (Shang, Ha & Tong 2016, §3, p. 249): `informed`
(the paper's `I`: the retailer shares the demand signal with him) or `uninformed` (`U`). -/
inductive Status
  | informed
  | uninformed
  deriving DecidableEq

/-- The rival of manufacturer `i ∈ {0, 1}` (the paper's `j` for a given `i`). -/
def other (i : Fin 2) : Fin 2 := 1 - i

/-- The number `n` of informed manufacturers in a status profile `X = (X₁, X₂)`. -/
def numInformed (X : Fin 2 → Status) : ℕ :=
  (Finset.univ.filter fun i => X i = Status.informed).card

/-- The profile in which manufacturer `i` alone is informed. -/
def onlyInformed (i : Fin 2) : Fin 2 → Status :=
  fun j => if j = i then Status.informed else Status.uninformed

end InfoSharing.Shared


