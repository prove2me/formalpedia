-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagPivotAlgIndep
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagPivotAlgIndep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:06.611383+00:00
-- url     : https://prove2.me/theorems/62a89777-8687-4b5f-be62-28b61be90ccc
-- title:
--   PFlag Pivot Alg Indep
-- statement:
--   Definitions and structural lemmas for PFlag Pivot Alg Indep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagPivotAlgIndep.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial
namespace FlagPivotAlgIndep
variable (F : Type) [Field F] (n : ℕ)
abbrev genFrac (p : Fin n × Fin n) : FractionRing (MvPolynomial (Fin n × Fin n) F) :=
  algebraMap (MvPolynomial (Fin n × Fin n) F) _ (X p)
def spec (p : Fin n × Fin n) : FractionRing (MvPolynomial (Fin n × Fin n) F) :=
  if (p.2 : ℕ) < p.1 then 0
  else if h : (p.1 : ℕ) = 0 then genFrac F n p
  else genFrac F n p / genFrac F n (⟨p.1 - 1, by omega⟩, ⟨p.1 - 1, by omega⟩)
end FlagPivotAlgIndep
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


