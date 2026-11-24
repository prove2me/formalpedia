-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMinorsTrdeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:53.586248+00:00
-- url     : https://prove2.me/theorems/6cff429b-d4d2-49fb-a750-2f7c4050eb1d
-- title:
--   PFlag Minors Trdeg
-- statement:
--   Definitions and structural lemmas for PFlag Minors Trdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMinorsTrdeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMinorsTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotIdentity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagPivotAlgIndep
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_pivotMinor_eq_flagMinor_63644bd2805c

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
section
variable (F : Type) [Field F] (n : ℕ)
def flagMinorAlg : Subalgebra F (MvPolynomial (Fin n × Fin n) F) :=
  Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2)
abbrev PivotIdx := Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b}
theorem pivotMinor_mem_flagMinorAlg (q : PivotIdx n) : pivotMinor (genMat F n) q.1 q.2.1 ∈ flagMinorAlg F n := by
  rw [pivotMinor_eq_flagMinor _ q.1 q.2.1 q.2.2]
  exact Algebra.subset_adjoin ⟨⟨q.1, _⟩, rfl⟩
def pivotElt (q : PivotIdx n) : flagMinorAlg F n := ⟨_, pivotMinor_mem_flagMinorAlg F n q⟩
def pivotAlg : Subalgebra F (flagMinorAlg F n) := Algebra.adjoin F (Set.range (pivotElt F n))
def pivotAlgP : Subalgebra F (MvPolynomial (Fin n × Fin n) F) :=
  Algebra.adjoin F (Set.range fun q : PivotIdx n => pivotMinor (genMat F n) q.1 q.2.1)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


