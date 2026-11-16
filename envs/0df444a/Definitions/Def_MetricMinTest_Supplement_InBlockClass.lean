-- Prove2me | Definitions.Def_MetricMinTest_Supplement_InBlockClass
-- name    : MetricMinTest_Supplement_InBlockClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:34:26.948807+00:00
-- url     : https://prove2.me/theorems/d8f0b39c-9540-4079-a9cb-71de2378fb60
-- title:
--   Known-block instance class
-- statement:
--   For a partition $\Pi$ of $[k]$ into blocks with mean diameters $\Delta_C$, the **known-block class** consists of all instances (laws on $[-1,1]$) with
--   $$\max_{i\in C}\mu_i-\min_{i\in C}\mu_i\le\Delta_C\qquad(C\in\Pi),$$
--   without cross-block restrictions. It is the class of Theorem H.1.
--
--   **Formalization Note** The diameter condition is written as $|\mu_i-\mu_j|\le\Delta_C$ for all $i,j$ in the same block.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Appendix H, p.29

import Mathlib
import Definitions.Def_MetricMinTest_Instance_mean

namespace MetricMinTest.Supplement

/-- **Known-block class** (Appendix H). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Appendix H, p.29: "The class requires
max_{i∈C} µᵢ − min_{i∈C} µᵢ ≤ Δ_C (C ∈ Π), without cross-block restrictions."

**Formalization Note.** Blocks are the fibres of `blk`; `max − min ≤ Δ_C` over a finite block is
written as `|µᵢ − µⱼ| ≤ Δ_C` for all `i, j` in the block. Laws on `[−1, 1]` (`Instance`). -/
def InBlockClass {ι β : Type} (blk : ι → β) (ΔC : β → ℝ) (P : Instance ι) : Prop :=
  ∀ i j, blk i = blk j → |P.mean i - P.mean j| ≤ ΔC (blk i)

end MetricMinTest.Supplement


