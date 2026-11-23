-- Prove2me | Definitions.Def_CapitationRisk_PerfectRA_Supplement_MLR
-- name    : CapitationRisk_PerfectRA_Supplement_MLR
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:36:50.207154+00:00
-- url     : https://prove2.me/theorems/ea968d72-93d9-4565-8c62-a27aa386e20e
-- title:
--   Problem (34) — endogenous-price medical-loss-ratio equilibria
-- statement:
--   Let (w,P) be an implementable provider-response pair. The MLR feasible set additionally requires
--   $$\sum_i\lambda_i(w)r_i=\sum_sD_s(w_s)P_s.$$
--   An MLR equilibrium globally maximizes the unchanged plan profit (10) on these pairs. Projecting such pairs onto w gives the quality outcomes of problem (34), which Theorem 4 compares with (35).
--
--   **Formalization Note** P is chosen by the plan and need not equal the exogenous TM price P*. Both interval endpoints and every implementing price are included. This definition encodes the paper's exact equality version of MLR; it makes no claim about current regulatory thresholds.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), pp. 39–40, (34); p. 22, (17)

import Definitions.Def_CapitationRisk_PerfectRA_Supplement_ProviderResponse

namespace CapitationRisk.PerfectRA.Supplement

variable {S I : Type*} [Fintype S] [Fintype I]

/-- Problem (34): provider responses and the endogenous-price MLR identity (17). -/
def mlrPairs (M : Model S I) (r : I → ℝ) : Set ((S → ℝ) × (S → ℝ)) :=
  {a | a ∈ providerPairs M ∧
    ∑ i, M.lam i a.1 * r i = ∑ s, M.totDemand s (a.1 s) * a.2 s}

def IsMLREquilibrium (M : Model S I) (r : I → ℝ) (w P : S → ℝ) : Prop :=
  (w, P) ∈ mlrPairs M r ∧ IsMaxOn (pairProfit M r) (mlrPairs M r) (w, P)

end CapitationRisk.PerfectRA.Supplement


