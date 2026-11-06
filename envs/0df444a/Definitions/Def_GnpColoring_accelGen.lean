-- Prove2me | Definitions.Def_GnpColoring_accelGen
-- name    : GnpColoring_accelGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:15.025545+00:00
-- url     : https://prove2.me/theorems/edf84ce3-134f-4c67-8abe-efae639c1f5e
-- title:
--   The accelerated generator $\tilde L$
-- statement:
--   $$\tilde L=\sum_{s\in S}H_s+q\sum_{B\in\mathcal B}L_B.$$
--
--   Since $1\le a_s\le q$, its Dirichlet form lies between those of $L$ and $qL$.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 3.2, p.16

import Mathlib
import Definitions.Def_GnpColoring_accelSingle
import Definitions.Def_GnpColoring_blocks
import Definitions.Def_GnpColoring_blockLap

open scoped Classical
open Finset

namespace GnpColoring

/-- **The accelerated generator** `L̃ = Σ_{s∈S} H_s + q Σ_{B∈𝓑} L_B`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 3.2, p.16. -/
noncomputable def accelGen {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (S : Finset (Fin n))
    (f : (Fin n → Fin q) → ℝ) : (Fin n → Fin q) → ℝ :=
  fun x => ∑ s ∈ S, accelSingle G q s f x +
    (q : ℝ) * ∑ B ∈ blocks G S, blockLap (MarkovMixing.properColoringDist G q) B f x

end GnpColoring


