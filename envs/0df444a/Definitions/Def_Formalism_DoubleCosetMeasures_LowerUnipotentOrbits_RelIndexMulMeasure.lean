-- Prove2me | Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
-- name    : Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:17:24.35404+00:00
-- url     : https://prove2.me/theorems/e0bfd61b-050a-4ad7-81e5-039c627950f8
-- title:
--   Rel Index Mul Measure
-- statement:
--   Definitions and structural lemmas for Rel Index Mul Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Set Pointwise
namespace Formalism.DoubleCosetMeasures.P.GLRed
variable {F : Type} [Field F] (O : Subring F) {a : ℕ}
def intM (M : Matrix (Fin a) (Fin a) F) (h : IsInt O M) : Matrix (Fin a) (Fin a) O :=
  fun i j => ⟨M i j, h i j⟩
theorem map_intM (M : Matrix (Fin a) (Fin a) F) (h : IsInt O M) : (intM O M h).map O.subtype = M :=
  rfl
theorem map_sub_inj : Function.Injective
    (fun M : Matrix (Fin a) (Fin a) O => M.map O.subtype) :=
  Matrix.map_injective Subtype.val_injective
theorem intM_mul (M N : Matrix (Fin a) (Fin a) F) (hM : IsInt O M) (hN : IsInt O N)
    (hMN : IsInt O (M * N)) : intM O (M * N) hMN = intM O M hM * intM O N hN := by
  apply map_sub_inj O
  simp only [Matrix.map_mul, map_intM]
theorem intM_one (h : IsInt O (1 : Matrix (Fin a) (Fin a) F)) :
    intM O (1 : Matrix (Fin a) (Fin a) F) h = 1 := by
  apply map_sub_inj O
  simp only [map_intM, Matrix.map_one _ (map_zero O.subtype) (map_one O.subtype)]
variable (a)
def toO : GLint O a →* GL (Fin a) O where
  toFun g :=
    { val := intM O _ g.2.1
      inv := intM O _ g.2.2
      val_inv := by
        apply map_sub_inj O
        simp only [Matrix.map_mul, map_intM, Matrix.map_one _ (map_zero O.subtype) (map_one O.subtype)]
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      inv_val := by
        apply map_sub_inj O
        simp only [Matrix.map_mul, map_intM, Matrix.map_one _ (map_zero O.subtype) (map_one O.subtype)]
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one] }
  map_one' := by
    ext1
    exact intM_one O _
  map_mul' g h := by
    ext1
    exact intM_mul O _ _ _ _ _
variable (ϖ : F) (hϖ : ϖ ∈ O)
def red : GLint O a →* GL (Fin a) (kF O ϖ hϖ) :=
  (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}))).comp (toO O a)
variable {a}
variable (a)
end Formalism.DoubleCosetMeasures.P.GLRed
namespace Formalism.DoubleCosetMeasures.P
end Formalism.DoubleCosetMeasures.P
namespace Formalism.DoubleCosetMeasures.P.GLRed
section Top
variable {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
end Top
end Formalism.DoubleCosetMeasures.P.GLRed
namespace Formalism.DoubleCosetMeasures.P
end Formalism.DoubleCosetMeasures.P


