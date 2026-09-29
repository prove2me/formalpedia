-- Prove2me | Definitions.Def_EthierKurtz_spinVariation
-- name    : EthierKurtz_spinVariation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:41:24.855252+00:00
-- url     : https://prove2.me/theorems/8bf89409-644f-4d13-b5db-78e5c5784fe7
-- title:
--   Uniform single-coordinate variation
-- statement:
--   The supremum, over all Boolean spin configurations, of the absolute change in a continuous observable caused by flipping one specified coordinate.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, definition of Δ_i and equation (3.24), printed p. 381 (PDF p. 390).

import Definitions.Def_EthierKurtz_spinFlip

open Filter
open scoped Topology BigOperators

namespace EthierKurtz

/-- Uniform norm of Δ_i f, expressed without a separate bundled difference
operator. The configuration space is nonempty and compact, and the range of
absolute differences is bounded; this real supremum is therefore literal. -/
noncomputable def spinVariation {S : Type*} (f : C(S → Bool, ℝ)) (i : S) : ℝ :=
  sSup (Set.range (fun η : S → Bool => |f (spinFlip i η) - f η|))

end EthierKurtz


