-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HaarUpqHasOmegaDensity
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HaarUpqHasOmegaDensity
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:26.086292+00:00
-- url     : https://prove2.me/theorems/1ad2d9c6-e1e3-4ea1-8258-bc13ed6a50c9
-- title:
--   Haar Upq Has Omega Density
-- statement:
--   Definitions and structural lemmas for Haar Upq Has Omega Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HaarUpqHasOmegaDensity.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousMatExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDensityOriginOfAlmostHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsOmegaLebesgueMeasure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqExpLocalChart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UpqLocallyCompactGroup
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
noncomputable section
namespace GlobalTheory.HaarDensityUpq
def toL1 (P Q : ℕ) : lieU P Q →ₗ[ℝ] PiLp 1 (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) where
  toFun X := WithLp.toLp 1 (entries (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem toL1_injective (P Q : ℕ) : Function.Injective (toL1 P Q) := by
  intro X Y h
  ext i j
  exact congrFun (congrArg WithLp.ofLp h) (i, j)
theorem isInducing_toL1 (P Q : ℕ) : IsInducing (toL1 P Q) := by
  have h1 : IsInducing (entries : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → _) :=
    (Homeomorph.piCurry (X := Fin P ⊕ Fin Q) (Y := Fin P ⊕ Fin Q) (Z := ℂ)).symm.isInducing
  exact (PiLp.homeomorph 1 (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ)).symm.isInducing.comp
    (h1.comp IsInducing.subtypeVal)
@[reducible] def sumNorm (P Q : ℕ) : NormedAddCommGroup (lieU P Q) :=
  let N := NormedAddCommGroup.induced (lieU P Q) _ (toL1 P Q) (toL1_injective P Q)
  { toNorm := N.toNorm
    toAddCommGroup := inferInstance
    toMetricSpace := N.toMetricSpace.replaceTopology (isInducing_toL1 P Q).eq_induced
    dist_eq := N.dist_eq }
end GlobalTheory.HaarDensityUpq


