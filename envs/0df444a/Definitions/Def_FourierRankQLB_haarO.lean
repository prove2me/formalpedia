-- Prove2me | Definitions.Def_FourierRankQLB_haarO
-- name    : FourierRankQLB_haarO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:23.452581+00:00
-- url     : https://prove2.me/theorems/044cc597-59e5-4e26-a93b-8ec415b080e7
-- title:
--   Normalized Haar measure $\mu_d$ on $O(d)$
-- statement:
--   The normalized Haar measure $\mu_d$ of the compact group $O(d)$: the left-invariant Borel probability measure.
--
--   All average-case statements draw the hidden matrix from $\mu_d$, and the Fourier-rank spaces are subspaces of $L^p(O(d),\mu_d)$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §3.1, p.16

import Mathlib
import Definitions.Def_FourierRankQLB_Od

open MeasureTheory

namespace FourierRankQLB

/-- The normalized Haar measure `μ_d` on `O(d)`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §3.1, p. 16 ("`μ_n` denotes normalized Haar measure on `O(n)`").

**Formalization Note.** This is the Haar measure giving the compact group `O(d)` mass one. -/
noncomputable def haarO (d : ℕ) : Measure (Od d) := Measure.haarMeasure ⊤

instance instIsProbabilityMeasureHaarO (d : ℕ) : IsProbabilityMeasure (haarO d) :=
  ⟨by simpa [haarO] using Measure.haarMeasure_self (G := Od d) (K₀ := ⊤)⟩

instance instIsMulLeftInvariantHaarO (d : ℕ) : (haarO d).IsMulLeftInvariant := by
  unfold haarO
  infer_instance

end FourierRankQLB


