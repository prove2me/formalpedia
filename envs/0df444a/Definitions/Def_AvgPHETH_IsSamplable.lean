-- Prove2me | Definitions.Def_AvgPHETH_IsSamplable
-- name    : AvgPHETH_IsSamplable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:29:16.573189+00:00
-- url     : https://prove2.me/theorems/af9fd9d2-cc70-4191-82d6-823eda0c5543
-- title:
--   Polynomial-time samplable families
-- statement:
--   A family $D$ of distributions is polynomial-time samplable with oracle $O$ if it has a sampler with oracle $O$. For $O=\emptyset$ this is polynomial-time samplability.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.1, p.14 (PDF 16); footnote 2, p.10 (PDF 12)

import Mathlib
import Definitions.Def_AvgPHETH_IsSampler
open KarpLiptonOM

namespace AvgPHETH

/-- The family `D` is polynomial-time samplable with oracle `O`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.1, p.14 (PDF 16); footnote 2, p.10 (PDF 12): "`DistΣ_2^{p,O}` allows the sampling algorithms
to query `O`"). -/
def IsSamplable (O : Set (List Bool)) (D : ℕ → PMF (List Bool)) : Prop :=
  ∃ (M : OracleTM) (r : Polynomial ℕ) (e : ℕ), IsSampler M r e O D

end AvgPHETH


