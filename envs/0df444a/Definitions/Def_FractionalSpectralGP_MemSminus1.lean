-- Prove2me | Definitions.Def_FractionalSpectralGP_MemSminus1
-- name    : FractionalSpectralGP_MemSminus1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:09.729574+00:00
-- url     : https://prove2.me/theorems/5cc1515b-7738-43b5-ab9a-78277995a679
-- title:
--   Membership in the Kondratiev space $S_{-1}$
-- statement:
--   A formal series $f$ belongs to the Kondratiev space $S_{-1}$ of stochastic distributions if $f\in\mathcal H'_k$ for some $k$:
--
--   $$
--   S_{-1}=\bigcup_k\mathcal H'_k .
--   $$
--
--   $S_{-1}$ is stable under the Wick product and contains the white noise space.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, (4.6), p.11

import Mathlib
import Definitions.Def_FractionalSpectralGP_MemHprime

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Membership in the Kondratiev space `S_{−1}` of stochastic distributions, the inductive limit
(union) of the increasing family `𝓗'_k` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, (4.6), p.11). -/
def MemSminus1 (f : (ℕ →₀ ℕ) → ℂ) : Prop :=
  ∃ k : ℕ, MemHprime k f

end FractionalSpectralGP


