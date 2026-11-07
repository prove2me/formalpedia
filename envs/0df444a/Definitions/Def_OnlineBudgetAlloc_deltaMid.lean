-- Prove2me | Definitions.Def_OnlineBudgetAlloc_deltaMid
-- name    : OnlineBudgetAlloc_deltaMid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:11.678078+00:00
-- url     : https://prove2.me/theorems/58b811a1-bd86-4283-9c3b-063f0b6f9c6b
-- title:
--   Total expected change in the middle phase $\Delta_{\mathrm{mid}}$
-- statement:
--   For a deterministic online algorithm on $D_{N,d}$, $\Delta_{\mathrm{mid}}$ is the total expected sum of $\Delta_t$ over the middle phase:
--   $$
--   \Delta_{\mathrm{mid}} = \mathbb E_{D_{N,d}}\Bigl[\sum_{g} \bigl(\Delta_{t_g} + \Delta_{t_g+1} + \Delta_{t_g+2}\bigr)\Bigr],
--   $$
--   where $t_g, t_g+1, t_g+2$ are the three items of round $g$. Lemma 8 shows that $\Delta_{\mathrm{mid}}$ is smaller, by a constant fraction of $N$, than the integral $\int_R^M F$ it replaces in the classical bound.
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.6 (after eq. (5))

import Mathlib
import Definitions.Def_OnlineBudgetAlloc_Instance
import Definitions.Def_OnlineBudgetAlloc_revenue
import Definitions.Def_OnlineBudgetAlloc_DetAlg
import Definitions.Def_OnlineBudgetAlloc_Seed
import Definitions.Def_OnlineBudgetAlloc_PartitionRule
import Definitions.Def_OnlineBudgetAlloc_inputD
import Definitions.Def_OnlineBudgetAlloc_vcap
import Definitions.Def_OnlineBudgetAlloc_Hscale
import Definitions.Def_OnlineBudgetAlloc_deltaD
import Definitions.Def_OnlineBudgetAlloc_expD

namespace OnlineBudgetAlloc

/-- `∆_mid`: "the total expected sum of ∆t for the entire middle phase" (Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §3.4, p.6), for
the deterministic online algorithm `A` on `D_{N,d}`. -/
noncomputable def deltaMid {N d : ℕ} (part : PartitionRule N d) (A : DetAlg N) : ℝ :=
  expD (fun s : Seed N d => ∑ g : Fin (numGroups N d), ∑ c : Fin 3, deltaD part A s (midItem g c))

end OnlineBudgetAlloc


