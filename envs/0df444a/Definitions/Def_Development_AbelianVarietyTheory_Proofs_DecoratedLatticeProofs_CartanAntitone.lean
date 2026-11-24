-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CartanAntitone
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_CartanAntitone
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:03:02.682549+00:00
-- url     : https://prove2.me/theorems/c6ceb13f-dd19-48b4-89c9-293146cbfdeb
-- title:
--   Cartan Antitone
-- statement:
--   Definitions and structural lemmas for Cartan Antitone, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/CartanAntitone.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_IsCoType
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ValuationDivZpowOrd
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
noncomputable section
namespace GlobalTheory.SortedCartan
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def permUnitO {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) 𝒪[k] where
  val := σ.toPEquiv.toMatrix
  inv := σ.symm.toPEquiv.toMatrix
  val_inv := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
  inv_val := by
    rw [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl,
      PEquiv.toMatrix_refl]
def permUnit {N : ℕ} (σ : Equiv.Perm (Fin N)) : GL (Fin N) k :=
  Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) (permUnitO σ)
end GlobalTheory.SortedCartan
end


