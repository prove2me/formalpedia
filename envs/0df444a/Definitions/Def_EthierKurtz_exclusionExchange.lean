-- Prove2me | Definitions.Def_EthierKurtz_exclusionExchange
-- name    : EthierKurtz_exclusionExchange
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:58:25.715305+00:00
-- url     : https://prove2.me/theorems/4f424602-5256-46c5-b70e-0caffae2a2ab
-- title:
--   Two-site exclusion exchange
-- statement:
--   Given two sites and a Boolean occupation configuration, exchange the values at those sites and leave every other coordinate unchanged; coincident sites give the identity.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, equation (3.26), printed p. 381 (PDF p. 390).

import Mathlib

open Filter
open scoped Topology BigOperators

namespace EthierKurtz

/-- Equation (3.26): exchange two sites, also valid when they coincide. -/
noncomputable def exclusionExchange {S : Type*} (i j : S) (η : S → Bool) :
    S → Bool := by
  classical
  exact fun k => if k = i then η j else if k = j then η i else η k

end EthierKurtz


