-- Prove2me | Definitions.Def_BayesClock_OPT
-- name    : BayesClock_OPT
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:10.323546+00:00
-- url     : https://prove2.me/theorems/eb6a069e-13e6-4171-9081-b3de412fe618
-- title:
--   Expected optimal social welfare $\mathrm{OPT}$
-- statement:
--   For value distributions $D_i$ and $D=\times_{i\in N}D_i$, the benchmark is the **expected optimal social welfare**
--
--   $$\mathrm{OPT}=\mathbb E_{v\sim D}\Big[\max_{F\in\mathcal F}\sum_{i\in F}v_i\Big].$$
--
--   An auction approximates the optimal welfare within a factor $\alpha$ if $\mathrm{OPT}\le\alpha\cdot\mathrm{auc}$, where $\mathrm{auc}$ is its expected welfare.
--
--   **Formalization Note** A lower integral with values in $[0,\infty]$, so that a non-integrable value does not collapse the benchmark to $0$.
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, §2, p.5

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- The benchmark `OPT = E v∼D [max F ∈ 𝓕, ∑ i ∈ F, v i]`, the expected optimal social welfare.
Feldman et al., arXiv:2202.09291v1, §2, p.5.

**Formalization Note** A lower Lebesgue integral with values in `ℝ≥0∞`, so that a non-integrable
value does not collapse the benchmark to `0`. The maximum over the finite family `𝓕` is a `⨆` in
the complete lattice `ℝ≥0∞`, and `𝓕` is nonempty for a downward-closed constraint. -/
noncomputable def OPT {N : Type*} [Fintype N] (𝓕 : Finset (Finset N))
    (ν : N → Measure ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ v, ⨆ F ∈ 𝓕, ∑ i ∈ F, (v i : ℝ≥0∞) ∂Measure.pi ν

end BayesClock


