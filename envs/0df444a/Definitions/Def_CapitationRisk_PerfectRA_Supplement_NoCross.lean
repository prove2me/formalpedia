-- Prove2me | Definitions.Def_CapitationRisk_PerfectRA_Supplement_NoCross
-- name    : CapitationRisk_PerfectRA_Supplement_NoCross
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:33:40.706752+00:00
-- url     : https://prove2.me/theorems/7f1c4b73-b273-48ef-b5a1-c1019fd63353
-- title:
--   Equation (15) and problems (9), (29)–(30) — per-type restrictions and regime equilibria
-- statement:
--   For each patient type i, capitation rate r_i and feasible quality vector w, the no-cross-subsidy restriction is the monetary equation printed immediately after (15):
--   $$\lambda_i(w)r_i=\sum_s\lambda_i^s(w_s)P_s^*\quad\text{for every }i.$$
--   A Boolean flag b chooses between the full quality box (b=false) and its intersection with all these equalities (b=true). A regime equilibrium is a feasible global maximizer of the published profit (10) on that set. This gives the four cases in Theorem 2's proof precise meanings.
--
--   **Formalization Note** Monetary equalities remain meaningful at zero enrollment. For positive enrollment they are exactly the displayed quotient form (15). Both fixed and variable costs are subtracted, as in (10) and the expansion on p. 38; the conflicting sign inside the brackets of (29)–(30) is corrected.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), p. 20, (15); pp. 37–38, (29)–(30)

import Definitions.Def_CapitationRisk_PerfectRA_Model

namespace CapitationRisk.PerfectRA.Supplement

variable {S I : Type*} [Fintype S] [Fintype I]

/-- The monetary equalities immediately following (15), meaningful also at zero enrollment. -/
def NoCross (M : Model S I) (r : I → ℝ) (w : S → ℝ) : Prop :=
  ∀ i, M.lam i w * r i = ∑ s, M.lamS s i (w s) * M.Pstar s

/-- The four-case proof of Theorem 2: true imposes (15) as in (29)/(30);
false retains precisely the unrestricted quality box of (9). -/
def regimeSet (M : Model S I) (r : I → ℝ) (impose : Bool) : Set (S → ℝ) :=
  {w | w ∈ M.box ∧ (impose = true → NoCross M r w)}

def IsRegimeEquilibrium (M : Model S I) (r : I → ℝ) (impose : Bool)
    (w : S → ℝ) : Prop :=
  w ∈ regimeSet M r impose ∧ IsMaxOn (M.profit r) (regimeSet M r impose) w

end CapitationRisk.PerfectRA.Supplement


