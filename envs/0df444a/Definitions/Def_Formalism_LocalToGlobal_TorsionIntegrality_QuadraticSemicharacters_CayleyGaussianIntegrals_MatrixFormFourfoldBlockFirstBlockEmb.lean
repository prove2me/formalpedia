-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:47.918587+00:00
-- url     : https://prove2.me/theorems/f778ab86-ea95-483a-a108-7876c3344c9e
-- title:
--   Matrix Form Fourfold Block First Block Emb
-- statement:
--   Definitions and structural lemmas for Matrix Form Fourfold Block First Block Emb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/MatrixFormFourfoldBlockFirstBlockEmb.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_LineTransport
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
section Blocks
variable {n : Type*} [Fintype n]
def sliceL (a : Fin 4) : (Fin 4 × n → ℂ) →ₗ[ℂ] (n → ℂ) where
  toFun := slice a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def mk4 (u : Fin 4 → n → ℂ) : Fin 4 × n → ℂ := fun p => u p.1 p.2
def emb0 : (n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun v := fun p => if p.1 = 0 then v p.2 else 0
  map_add' u v := by
    funext p
    by_cases hp : p.1 = 0 <;> simp [hp]
  map_smul' c v := by
    funext p
    by_cases hp : p.1 = 0 <;> simp [hp]
end Blocks
end Formalism.L2.Th1.H


