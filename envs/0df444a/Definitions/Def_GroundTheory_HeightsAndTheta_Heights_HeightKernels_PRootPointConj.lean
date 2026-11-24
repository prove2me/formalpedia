-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointConj
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootPointConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:48.560342+00:00
-- url     : https://prove2.me/theorems/a105f1d8-0810-40a8-9b29-65d17090400a
-- title:
--   PRoot Point Conj
-- statement:
--   Definitions and structural lemmas for PRoot Point Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootPointConj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeightNE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
namespace RootPointConjugation
def colAB {j m : ℕ} (a : Fin j) (b : Fin m) (c : Fin j) : Fin (j + m) :=
  if c = a then Fin.natAdd j b else Fin.castAdd m c
theorem colAB_injective {j m : ℕ} (a : Fin j) (b : Fin m) : Function.Injective (colAB a b) := by
  intro c d h
  by_cases hc : c = a <;> by_cases hd : d = a <;>
    simp_all [colAB, Fin.ext_iff] <;> omega
def idxAB {j m : ℕ} (a : Fin j) (b : Fin m) : PlIdx j m :=
  ⟨Finset.univ.map ⟨colAB a b, colAB_injective a b⟩, by simp⟩
end RootPointConjugation
end
end GroundTheory.Heights₂.Heights


