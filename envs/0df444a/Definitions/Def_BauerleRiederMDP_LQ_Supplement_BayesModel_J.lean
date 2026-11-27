-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_J
-- name    : BauerleRiederMDP_LQ_Supplement_BayesModel_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:58:46.015698+00:00
-- url     : https://prove2.me/theorems/55d4e467-f6f6-55dc-9f36-011b850e1ca3
-- title:
--   The value of the $N$-stage Bayesian problem
-- statement:
--   **The value of the $N$-stage Bayesian problem** $J_N(x) := \sup _\pi  J_{N\pi }(x)$ (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), eq. (5.2), p.150, PDF 163), the supremum over the history-dependent policies $\pi  \in  \tilde{\Pi}_N$ of p.163, PDF 176.
--
--   **Formalization Note.** The policies have rules on the histories $\tilde{H}_k$ that include the disturbances (Theorem 5.4.7 takes $\pi  \in  \tilde{\Pi}_N$); the supremum is in `EReal`.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011)

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_IsPolicy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_Jpi

namespace BauerleRiederMDP.LQ.Supplement

universe u

/-- **The value of the `N`-stage Bayesian problem** `J_N(x) := sup_π J_{Nπ}(x)` (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), eq. (5.2), p.150, PDF 163), the
supremum over the history-dependent policies `π ∈ Π̃_N` of p.163, PDF 176.

**Formalization Note.** The policies have rules on the histories `H̃_k` that include the
disturbances (Theorem 5.4.7 takes `π ∈ Π̃_N`); the supremum is in `EReal`. -/
noncomputable def BayesModel.J {EX A Z : Type u} {Θ : Type*} [MeasurableSpace EX] [MeasurableSpace A]
    [MeasurableSpace Z] [MeasurableSpace Θ] (M : BayesModel EX A Z Θ) (N : ℕ) (x : EX) : EReal :=
  ⨆ π ∈ {π : (k : ℕ) → Htil EX A Z k → A | M.IsPolicy N π}, M.Jpi N π x

end BauerleRiederMDP.LQ.Supplement


