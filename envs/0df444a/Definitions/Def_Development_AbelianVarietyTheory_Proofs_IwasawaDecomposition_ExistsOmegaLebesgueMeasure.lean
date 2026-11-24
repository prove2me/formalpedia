-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsOmegaLebesgueMeasure
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsOmegaLebesgueMeasure
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T23:28:01.483498+00:00
-- url     : https://prove2.me/theorems/ac2cafff-67d8-4eba-9a8f-7d1a51904d3e
-- title:
--   Exists Omega Lebesgue Measure
-- statement:
--   Definitions and structural lemmas for Exists Omega Lebesgue Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsOmegaLebesgueMeasure.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal
noncomputable section
namespace GlobalTheory.OmegaLebExists
def cplxMap (P Q : ℕ) :
    (lieU P Q × lieU P Q) →ₗ[ℝ] ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) where
  toFun ab := entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))
  map_add' x y := by
    funext ij
    simp [entries]
    ring
  map_smul' c x := by
    funext ij
    simp [entries]
    ring
end GlobalTheory.OmegaLebExists


