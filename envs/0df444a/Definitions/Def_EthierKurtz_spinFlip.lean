-- Prove2me | Definitions.Def_EthierKurtz_spinFlip
-- name    : EthierKurtz_spinFlip
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:40:47.327982+00:00
-- url     : https://prove2.me/theorems/2eb699bc-b582-4082-96fc-cb8cc08ec943
-- title:
--   Single-coordinate spin flip
-- statement:
--   Given a site and a Boolean spin configuration, replace exactly that site's value by its Boolean negation and leave every other coordinate unchanged.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, immediately before equation (3.24), printed p. 381 (PDF p. 390).

import Mathlib

open Filter
open scoped Topology BigOperators

namespace EthierKurtz

/-- Flip exactly one spin; this is the source configuration (ᵢη). -/
noncomputable def spinFlip {S : Type*} (i : S) (η : S → Bool) : S → Bool := by
  classical
  exact Function.update η i (!(η i))

end EthierKurtz


