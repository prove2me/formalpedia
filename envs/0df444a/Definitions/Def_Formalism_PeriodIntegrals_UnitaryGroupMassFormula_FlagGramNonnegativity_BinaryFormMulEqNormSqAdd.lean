-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_BinaryFormMulEqNormSqAdd
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_BinaryFormMulEqNormSqAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:48.633723+00:00
-- url     : https://prove2.me/theorems/5c07cc67-5269-4fcb-89c9-c5faa71c71dc
-- title:
--   Binary Form Mul Eq Norm Sq Add
-- statement:
--   Definitions and structural lemmas for Binary Form Mul Eq Norm Sq Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/BinaryFormMulEqNormSqAdd.lean

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
open Matrix ComplexConjugate
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
def gamma (r : ℕ) (T T' : ℝ) (s : ℂ) : Matrix (Fin r ⊕ Fin 2) (Fin r ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks ((-2 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ)) 0 0 !![(-T : ℂ), s; conj s, (-T' : ℂ)]
end PI.UnitaryGroupMassFormula.FlagGramNonneg


