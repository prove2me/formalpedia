-- Prove2me | Definitions.Def_CapitationRisk_PerfectRA_Supplement_ProviderResponse
-- name    : CapitationRisk_PerfectRA_Supplement_ProviderResponse
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:36:06.069282+00:00
-- url     : https://prove2.me/theorems/9117d713-4dae-496d-9fb5-950f38b76468
-- title:
--   Problems (35)–(36) — provider-response pairs and two-stage equilibrium
-- statement:
--   Let w be a quality vector and P a service-price vector. A pair (w,P) is implementable if w belongs to the quality box and, for each service s,
--   $$w_s\in\operatorname*{argmax}_{x\in[\underline w_s,1]}\{D_s(x)P_s-C_s^f(x)-c_sD_s(x)\},\qquad D_s(x)=\sum_i\lambda_i^s(x).$$
--   A two-stage equilibrium is an implementable pair globally maximizing the same plan profit (10), which depends on w and the fixed rates r, over every implementable pair. This is problem (36); direct quality optimization is the published IsMAEquilibrium of (35).
--
--   **Formalization Note** Interval membership and global maximality are explicit. Prices are arbitrary real decision variables, as in the displayed optimization; no first-order equality or canonical-price choice is imposed at boundary qualities. General optimization uses Mathlib's IsMaxOn, rather than a new generic game object.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), pp. 40–42, (35)–(36), (39)–(40)

import Definitions.Def_CapitationRisk_PerfectRA_Model

namespace CapitationRisk.PerfectRA.Supplement

variable {S I : Type*} [Fintype S] [Fintype I]

/-- Feasible pairs (quality, price) for (36): each provider globally optimizes (2). -/
def providerPairs (M : Model S I) : Set ((S → ℝ) × (S → ℝ)) :=
  {a | a.1 ∈ M.box ∧ ∀ s,
    IsMaxOn (M.providerPayoff s (a.2 s)) (Set.Icc (M.wl s) 1) (a.1 s)}

/-- The plan's unchanged objective (10), viewed on pairs. -/
def pairProfit (M : Model S I) (r : I → ℝ) (a : (S → ℝ) × (S → ℝ)) : ℝ :=
  M.profit r a.1

def IsTwoStageEquilibrium (M : Model S I) (r : I → ℝ)
    (w P : S → ℝ) : Prop :=
  (w, P) ∈ providerPairs M ∧ IsMaxOn (pairProfit M r) (providerPairs M) (w, P)

end CapitationRisk.PerfectRA.Supplement


