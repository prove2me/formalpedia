-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:29.766336+00:00
-- url     : https://prove2.me/theorems/298874cd-8202-4ae3-86fe-1d799d5dfbdc
-- title:
--   Dec Moments A
-- statement:
--   Definitions and structural lemmas for Dec Moments A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecMomentsA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
def dmW (U : Matrix (Fin n) (Fin n) ℂ) {i : ℕ} (hi : i ≤ n) (J : {J : Finset (Fin n) // J.card = i}) : ℝ :=
  ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2
def dmChi (i : ℕ) (a : Fin n) : ℂ := if (a : ℕ) < i then 1 else 0
def dmK (U : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) (k l : Fin n) : ℂ :=
  ∑ a, dmChi i a * (star (U a k) * U a l)
def dmInd (J : Finset (Fin n)) (k : Fin n) : ℂ := if k ∈ J then 1 else 0
end ReciprocityTheory.ChartRestriction.DS.S7


