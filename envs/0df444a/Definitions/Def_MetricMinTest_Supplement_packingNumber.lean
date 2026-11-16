-- Prove2me | Definitions.Def_MetricMinTest_Supplement_packingNumber
-- name    : MetricMinTest_Supplement_packingNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:33:46.352757+00:00
-- url     : https://prove2.me/theorems/27e5a0a7-71f1-449e-91d2-1a1b9af8b3c7
-- title:
--   Packing number $M_d(r)$
-- statement:
--   $M_d(r)$ is the largest cardinality of a subset of indices with pairwise distances greater than $r$. With $r=2\gamma$ it gives the packing lower bound $H_d(\gamma)\ge M_d(2\gamma)\gamma^{-2}$ (Proposition 3.3) and the lower bound of Theorem I.1.
--
--   **Formalization Note** A natural-number supremum, bounded by the number of indices.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Proposition 3.3, p.7

import Mathlib

namespace MetricMinTest.Supplement

/-- **Packing number `M_d(r)`.** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Proposition 3.3, p.7: "Let M_d(r) be the largest
cardinality of a subset with pairwise distances greater than r."

**Formalization Note.** `sSup` in `ℕ` of the cardinalities of finite sets with pairwise
distances `> r`; bounded by the number of indices, and the empty set and singletons qualify. -/
noncomputable def packingNumber {ι : Type} [Fintype ι] (d : ι → ι → ℝ) (r : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ Z : Finset ι, Z.card = n ∧ ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → r < d x y}

end MetricMinTest.Supplement


