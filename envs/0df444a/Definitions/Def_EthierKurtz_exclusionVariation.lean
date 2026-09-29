-- Prove2me | Definitions.Def_EthierKurtz_exclusionVariation
-- name    : EthierKurtz_exclusionVariation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:58:54.601472+00:00
-- url     : https://prove2.me/theorems/c6ffe39b-aec8-4511-958b-335e5df78ff4
-- title:
--   Uniform two-site exchange variation
-- statement:
--   The supremum, over all Boolean occupation configurations, of the absolute change in a continuous observable caused by exchanging two specified sites.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, equations (3.26) and (3.29), printed p. 381 (PDF p. 390).

import Definitions.Def_EthierKurtz_exclusionExchange

open Filter
open scoped Topology BigOperators

namespace EthierKurtz

/-- Uniform norm of the two-site difference Δᵢⱼ f. -/
noncomputable def exclusionVariation {S : Type*} (f : C(S → Bool, ℝ))
    (i j : S) : ℝ :=
  sSup (Set.range (fun η : S → Bool => |f (exclusionExchange i j η) - f η|))

end EthierKurtz


