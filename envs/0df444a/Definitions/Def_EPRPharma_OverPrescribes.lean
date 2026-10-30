-- Prove2me | Definitions.Def_EPRPharma_OverPrescribes
-- name    : EPRPharma_OverPrescribes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:18:34.795396+00:00
-- url     : https://prove2.me/theorems/a4912ae4-ef95-4727-af43-bcd8505cc92c
-- title:
--   The producer's decision induces over-prescription
-- statement:
--   A decision $(p,\eta_d,\eta_p)$ induces over-prescription if for some need $\theta_n\in[0,1]$ the doctor prescribes beyond it:
--
--   $$q_p^*(\theta_n)>\theta_n .$$
--
--   The paper: "If the doctor provides prescription medicine beyond the need of the patient ($q_p>\theta_n$), we consider this case as over-prescription."
--
--   **Formalization Note** Defined from the doctor's response, not from the inequality $\eta_d\ge p+o_d(1-\eta_p)$; their equivalence follows from Lemma 1.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.1, pp. 9–10

import Mathlib
import Definitions.Def_EPRPharma_doctorQ

namespace EPRPharma

/-- **The producer's decision induces over-prescription.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.1, pp. 9–10: "If the doctor provides
prescription medicine beyond the need of the patient (q_p > θ_n), we consider this case as
over-prescription". `OverPrescribes P d` says that for some need θ_n ∈ [0, 1] the doctor's
prescription under d exceeds θ_n.

**Formalization Note.** Defined from the doctor's response `doctorQ`, not from Lemma 1's
inequality η_d ≥ p + o_d(1 − η_p) (that equivalence is Lemma 1). -/
def OverPrescribes (P : Params) (d : Decision) : Prop :=
  ∃ θn ∈ Set.Icc (0:ℝ) 1, θn < doctorQ P d θn

end EPRPharma


