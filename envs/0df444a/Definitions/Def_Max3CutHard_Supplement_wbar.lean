-- Prove2me | Definitions.Def_Max3CutHard_Supplement_wbar
-- name    : Max3CutHard_Supplement_wbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:46:27.731712+00:00
-- url     : https://prove2.me/theorems/f0606a0f-5c52-4ec8-8e13-45507314788d
-- title:
--   Total family weight $\bar w=\sum_t w(I_t)$
-- statement:
--   For a family $(I_0,I_1,I_2)$ of gadgets, the **total family weight** is
--
--   $$\bar w=\sum_{t\in\mathbb Z_3}w(I_t),$$
--
--   where $w(I_t)$ is the total edge weight of the gadget $I_t$. Theorem 4.1 normalises its completeness and soundness values by $\bar w$; for a balanced instance the reduction graph has total weight $\bar w/3$.
--
--   **Formalization Note** $w(I_t)$ is the published `Max3CutHard.wR` of the edge list of $I_t$.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Theorem 4.1, p.7

import Mathlib
import Definitions.Def_Max3CutHard_Family
import Definitions.Def_Max3CutHard_wR

namespace Max3CutHard.Supplement

open Max3CutHard

/-- **`w̄ = Σ_t w(I_t)`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Theorem 4.1, p.7: "with `w̄ = Σ_t w(I_t)`".

**Formalization Note.** `w(I_t)` is the published total weight `wR` of the edge list of the
gadget `F t`. -/
noncomputable def wbar {k : ℕ} (F : Family k) : ℝ :=
  ∑ t : ZMod 3, wR (F t).edges

end Max3CutHard.Supplement


