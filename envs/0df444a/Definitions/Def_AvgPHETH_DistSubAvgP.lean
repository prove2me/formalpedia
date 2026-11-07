-- Prove2me | Definitions.Def_AvgPHETH_DistSubAvgP
-- name    : AvgPHETH_DistSubAvgP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:33:08.741254+00:00
-- url     : https://prove2.me/theorems/9fc2803f-84db-4e66-9845-309eb88889ed
-- title:
--   $\mathrm{Dist}\Sigma_d^{p,O}\subseteq\mathrm{AvgP}^O$
-- statement:
--   The statement that $(L,D)\in\mathrm{AvgP}^O$ for every $L\in\Sigma_d^{p,O}$ and every family $D$ that is polynomial-time samplable with oracle $O$. At $O=\emptyset$ and $d=2$ this is $\mathrm{Dist}\Sigma_2^p\subseteq\mathrm{AvgP}$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.1, p.14 (PDF 16)

import Mathlib
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_IsSamplable
import Definitions.Def_AvgPHETH_AvgPDist

namespace AvgPHETH

/-- `DistΣ_d^{p,O} ⊆ AvgP^O`: for every `L ∈ Σ_d^{p,O}` and every family `D` samplable in polynomial
time with oracle `O`, the problem `(L, D)` is in `AvgP^O` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.1, p.14 (PDF 16)).
At `O = ∅`, `d = 2` this is `DistΣ₂^p ⊆ AvgP`. -/
def DistSubAvgP (O : Set (List Bool)) (d : ℕ) : Prop :=
  ∀ L ∈ SigmaPO O d, ∀ D : ℕ → PMF (List Bool), IsSamplable O D → AvgPDist O L D

end AvgPHETH


