-- Prove2me | Definitions.Def_MetricMinTest_Supplement_blockWorkload
-- name    : MetricMinTest_Supplement_blockWorkload
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:34:03.02966+00:00
-- url     : https://prove2.me/theorems/e149b119-cf15-498d-a518-4baf356dc412
-- title:
--   Block workload $H(\Pi,\gamma,\Delta)$
-- statement:
--   For a partition $\Pi$ of $[k]$ into blocks $C$ of sizes $k_C$, with mean diameters $\Delta_C\ge0$ and margins $\gamma_C\in(0,1/4]$,
--   $$H(\Pi,\gamma,\Delta)=\sum_{C\in\Pi}\frac{k_C}{\gamma_C^2+(k_C-1)(\gamma_C-\Delta_C)_+^2}.$$
--   It is the workload of the known-block model of Theorem H.1; for a common margin it is the information workload of the metric with within-block distance $\min\{\Delta_C,2\}$ and cross-block distance two.
--
--   **Formalization Note** The partition is given by a block label $\mathrm{blk}:[k]\to\beta$; blocks are its fibres.
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Appendix H, p.29

import Mathlib

namespace MetricMinTest.Supplement

/-- **Block workload `H(Π, γ, Δ)`** (Appendix H). Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Appendix H, p.29:
`H(Π, γ, Δ) = ∑_{C∈Π} k_C / (γ_C² + (k_C − 1)(γ_C − Δ_C)₊²)`.

**Formalization Note.** The partition `Π` is given by a block label `blk : ι → β`; block `C` is
the fibre `{i : blk i = C}` and `k_C` its size. The theorem using it requires `blk`
surjective (nonempty blocks). `(x)₊ = max x 0`. -/
noncomputable def blockWorkload {ι β : Type} [Fintype ι] [Fintype β] [DecidableEq β]
    (blk : ι → β) (γC ΔC : β → ℝ) : ℝ :=
  ∑ C : β, ((Finset.univ.filter (fun i => blk i = C)).card : ℝ) /
    (γC C ^ 2 + (((Finset.univ.filter (fun i => blk i = C)).card : ℝ) - 1) *
      (max (γC C - ΔC C) 0) ^ 2)

end MetricMinTest.Supplement


