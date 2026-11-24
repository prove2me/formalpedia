-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassArithVar
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassArithVar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:46.921698+00:00
-- url     : https://prove2.me/theorems/f4c03b96-bbd5-4b12-b8f0-f8837c6a75a0
-- title:
--   PGrass Arith Var
-- statement:
--   Definitions and structural lemmas for PGrass Arith Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassArithVar.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
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
namespace GrassmannianArithmeticVariety
def col {j m : ℕ} (a : Fin j) (b : Fin m) (i : Fin j) : Fin (j + m) :=
  if i = a then Fin.natAdd j b else Fin.castAdd m i
theorem col_injective {j m : ℕ} (a : Fin j) (b : Fin m) : Function.Injective (col a b) := by
  intro x y hxy
  simp only [col] at hxy
  split_ifs at hxy with h1 h2 h2
  · exact h1.trans h2.symm
  · rw [Fin.ext_iff] at hxy; simp at hxy; omega
  · rw [Fin.ext_iff] at hxy; simp at hxy; omega
  · rw [Fin.ext_iff] at hxy; exact Fin.ext (by simpa using hxy)
def idx {j m : ℕ} (a : Fin j) (b : Fin m) : PlIdx j m :=
  ⟨Finset.univ.map ⟨col a b, col_injective a b⟩, by simp⟩
end GrassmannianArithmeticVariety
end
end GroundTheory.Heights₂.Heights


