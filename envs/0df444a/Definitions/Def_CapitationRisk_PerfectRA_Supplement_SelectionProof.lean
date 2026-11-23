-- Prove2me | Definitions.Def_CapitationRisk_PerfectRA_Supplement_SelectionProof
-- name    : CapitationRisk_PerfectRA_Supplement_SelectionProof
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:35:32.224275+00:00
-- url     : https://prove2.me/theorems/b72c56a7-7138-445b-b0c9-4a622130580f
-- title:
--   Equation (16) — selection-proof feasibility at fixed TM prices
-- statement:
--   Given the published model, fixed capitation rates r_i and exogenous TM prices P*_s, restrict the quality box by the single identity
--   $$\sum_i\lambda_i(w)r_i=\sum_s\Bigl(\sum_i\lambda_i^s(w_s)\Bigr)P_s^*.$$
--   The selection-proof equilibrium globally maximizes the unchanged plan profit over this restricted set. This is the mechanism of Theorem 3; it imposes one aggregate equality, rather than one equality per type.
--
--   **Formalization Note** The missing star in the first display (16) is restored from the immediately following text, the next optimization display and (31)–(33). The price vector remains the published TMPrice evaluated at w*, and is not a decision variable.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), pp. 21–22, (16); pp. 38–39, (31)–(33)

import Definitions.Def_CapitationRisk_PerfectRA_Model

namespace CapitationRisk.PerfectRA.Supplement

variable {S I : Type*} [Fintype S] [Fintype I]

/-- Constraint (16), with the exogenous Pstar specified in the text and (31). -/
def selectionSet (M : Model S I) (r : I → ℝ) : Set (S → ℝ) :=
  {w | w ∈ M.box ∧ ∑ i, M.lam i w * r i = ∑ s, M.totDemand s (w s) * M.Pstar s}

def IsSelectionEquilibrium (M : Model S I) (r : I → ℝ) (w : S → ℝ) : Prop :=
  w ∈ selectionSet M r ∧ IsMaxOn (M.profit r) (selectionSet M r) w

end CapitationRisk.PerfectRA.Supplement


