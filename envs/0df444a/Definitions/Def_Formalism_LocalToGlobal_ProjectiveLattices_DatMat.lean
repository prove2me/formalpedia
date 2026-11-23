-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_DatMat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:18.994673+00:00
-- url     : https://prove2.me/theorems/16a15c72-e057-4980-845b-132b53e22882
-- title:
--   Dat Mat
-- statement:
--   Definitions and structural lemmas for Dat Mat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.DatLin
open Matrix Complex
section Mat
variable {m : Type} [Fintype m] [DecidableEq m]
end Mat
section GlobalTheory
variable {ι n : Type} [Fintype ι] [Fintype n]
def blk (N : ι → Matrix n n ℂ) : (ι → n → ℂ) →ₗ[ℝ] (ι → n → ℂ) where
  toFun u τ := N τ *ᵥ u τ
  map_add' u v := by ext τ : 1; simp [Matrix.mulVec_add]
  map_smul' c u := by
    ext τ i
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Matrix.mulVec_smul]
    rfl
def blkC (N : ι → Matrix n n ℂ) : (ι → n → ℂ) →ₗ[ℂ] (ι → n → ℂ) where
  toFun u τ := N τ *ᵥ u τ
  map_add' u v := by ext τ : 1; simp [Matrix.mulVec_add]
  map_smul' c u := by ext τ : 1; simp [Matrix.mulVec_smul]
end GlobalTheory
end Formalism.L2.Pj.DatLin


