-- Prove2me | Definitions.Def_MPBSelect_Problem_ldr
-- name    : MPBSelect_Problem_ldr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:33.676022+00:00
-- url     : https://prove2.me/theorems/c786bce9-4f03-4ddf-9feb-59939d97ecef
-- title:
--   The objective $\underline{\mathrm{LDR}}(\boldsymbol\alpha)=\min_{(i,\theta_b)\in\Xi}W_i(\theta_b)G_i(\theta_b)$ of (20)
-- statement:
--   The objective of the relaxed OCBA problem (20) is
--   $$
--   \underline{\mathrm{LDR}}(\boldsymbol\alpha)=\min_{(i,\theta_b)\in\Xi}W_i(\theta_b)\,G_i(\theta_b),
--   $$
--   the smallest weighted pairwise rate over $\Xi$. It is a deterministic function of the allocation $\boldsymbol\alpha$, built from the true means and standard deviations; the name is the paper's label for the objective of (20), not a large-deviations limit.
--
--   **Formalization Note** The minimum is `Finset.inf'` over $\Xi$, which is nonempty, so no junk value occurs.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, §4.2, p.17, (20)

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_Problem_Xi
import Definitions.Def_MPBSelect_Problem_W
import Definitions.Def_MPBSelect_Problem_G

namespace MPBSelect

/-- **Objective of the relaxed OCBA problem (20), `LDR(α) = min_{(i,θb)∈Ξ} Wi(θb) Gi(θb)`.**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, (20), p.17:
"max_α min_{(i,θb)∈Ξ} Wi(θb)Gi(θb)", the inner minimum labelled ":= LDR" under the brace.

This is a deterministic function of the allocation `α`, built from the true means and
variances: the paper's label for the objective of (20), not a large-deviations limit.

**Formalization Note** The minimum is `Finset.inf'` over `Ξ`, which is nonempty
(`Problem.Xi_nonempty`, from `k ≥ 2`), so no junk value occurs. -/
noncomputable def Problem.ldr {k B : ℕ} (P : Problem k B) (α : Fin k → Fin B → ℝ) : ℝ :=
  P.Xi.inf' P.Xi_nonempty (fun x => P.W x.1 x.2 * P.G α x.1 x.2)

end MPBSelect


