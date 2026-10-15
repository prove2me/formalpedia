-- Prove2me | Definitions.Def_RefMNLPricing_SteadyState_Model
-- name    : RefMNLPricing_SteadyState_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:30.163861+00:00
-- url     : https://prove2.me/theorems/13129de9-fece-4f7d-901c-7eb9651ab612
-- title:
--   Theorem 5, p. 22 — the multiplier κ = (1 − β)/(1 − αβ)
-- statement:
--   This file defines the multiplier that appears in the structure of optimal steady states for the multi-product pricing model of Guo, Jiang and Shen. For a memory parameter $\alpha\in[0,1]$ and a discount factor $\beta\in[0,1)$,
--   $$\kappa=\frac{1-\beta}{1-\alpha\beta}.$$
--
--   It scales the reference-price sensitivities in Theorem 5: if an optimal steady state $\mathbf p^{\star\star}$ exists and no product is gain-seeking, then for every product $i$,
--   $$p_i^{\star\star}-\Pi(\mathbf p^{\star\star},\mathbf p^{\star\star})\in\Big[\frac{1}{b_i+c_i^-\kappa},\ \frac{1}{b_i+c_i^+\kappa}\Big].$$
--   The same $\kappa$ appears in Corollaries 3 and 4 and in the single-price comparison of §4.3. The rest of the model (revenue, optimal value, optimal steady states, ceiling assumption) is imported from `RefMNLPricing.Myopic.Model`, `RefMNLPricing.Gap.Model` and `RefMNLPricing.GainSeeking.Model`.
--
--   **Formalization Note** The division is Lean's real division. Under the paper's standing assumptions $\alpha\in[0,1]$ and $\beta\in[0,1)$ we have $\alpha\beta<1$, so the denominator is positive and $\kappa\in(0,1]$. Every theorem that uses $\kappa$ states these hypotheses.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 22, Theorem 5 (definition of κ below (20))

import Mathlib
import Definitions.Def_RefMNLPricing_GainSeeking_Model
import Definitions.Def_RefMNLPricing_Gap_Model
import Definitions.Def_RefMNLPricing_Myopic_Model

namespace RefMNLPricing.SteadyState

/-- The multiplier `κ := (1 − β)/(1 − αβ)` of Theorem 5, p. 22. -/
noncomputable def kappa (α β : ℝ) : ℝ :=
  (1 - β) / (1 - α * β)

end RefMNLPricing.SteadyState


