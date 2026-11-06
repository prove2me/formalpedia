-- Prove2me | Definitions.Def_FlexibleNRM_dualObjective
-- name    : FlexibleNRM_dualObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:24:41.968903+00:00
-- url     : https://prove2.me/theorems/c4021700-3f4a-4f82-9b7c-fb7bc78064dc
-- title:
--   The objective of the dual form (10)
-- statement:
--   For $\mu\in\mathbb R^{|\mathcal L|}_+$, the objective of problem (10) is
--   $$\sum_{t\in\mathcal T}\max_{S\subseteq\mathcal J}\Big\{\sum_{j\in\mathcal J}\phi_{jt}(S)\max_{p\in\mathcal R_j}\Big\{f_j-\sum_{i\in\mathcal L}a_{ip}\mu_i\Big\}\Big\}+\sum_{i\in\mathcal L}c_i\mu_i.$$
--   It is the dual of (8) after eliminating the variables $\alpha_j$ and $\sigma_t$, and $\mu_i$ prices a unit of resource $i$.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Eq. (10), p.14

import Mathlib
import Definitions.Def_FlexibleNRM_Network

namespace FlexibleNRM

/-- The objective of the dual form (10) of linear program (8):
`∑_t max_{S ⊆ J} { ∑_j φ_jt(S) max_{p ∈ R_j} { f_j − ∑_i a_ip μ_i } } + ∑_i c_i μ_i`.

Zhu, Topaloglu, manuscript of November 16, 2022, Eq. (10), p.14. -/
noncomputable def dualObjective {n m r : ℕ} (N : Network n m r) (μ : Fin m → ℝ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 N.T,
      Finset.univ.sup' Finset.univ_nonempty (fun S : Finset (Fin n) =>
        ∑ j, (N.φ t).prob S j *
          (N.R j).sup' (N.R_nonempty j) (fun p => N.f j - ∑ i, (N.a i p : ℝ) * μ i)) +
    ∑ i, (N.c i : ℝ) * μ i

end FlexibleNRM


