-- Prove2me | Definitions.Def_CoffmanMitrani_shift
-- name    : CoffmanMitrani_shift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:21:00.853574+00:00
-- url     : https://prove2.me/theorems/57c01e54-55f8-4750-8430-dfa09fe0bb91
-- title:
--   Seed shift
-- statement:
--   The shifted sample point keeps all arrival and service data and drops the first seed $u_j(0)$ of every job. A mixing strategy uses $u_{j_0}(0)$ of the job opening a busy period to choose the busy period's type and runs the chosen strategy on the shifted sample point, so the type is independent of everything the chosen strategy uses.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §2, p. 814 (mixing strategies)

import Mathlib
import Definitions.Def_CoffmanMitrani_Omega

namespace CoffmanMitrani

/-- **Seed shift.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §2, p. 814 (mixing strategies: "a sequence of Bernoulli trials determines the sequence of
busy period types").

`shift ω` keeps the arrival and service data of `ω` and drops the first seed of every job. The
mixing strategy uses seed `0` of a busy period to choose its type and runs the chosen strategy on
`shift ω`, so the type is independent of everything the chosen strategy uses. -/
def shift {M : ℕ} (ω : Omega M) : Omega M :=
  (ω.1, ω.2.1, fun j ℓ => ω.2.2 j (ℓ + 1))

end CoffmanMitrani


