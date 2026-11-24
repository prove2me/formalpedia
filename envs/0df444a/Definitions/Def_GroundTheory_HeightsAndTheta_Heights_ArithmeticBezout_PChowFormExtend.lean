-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormExtend
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:21.799+00:00
-- url     : https://prove2.me/theorems/ecc09ba2-2fbd-4053-9cbe-ceb6346d077f
-- title:
--   PChow Form Extend
-- statement:
--   Definitions and structural lemmas for PChow Form Extend, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChowFormExtend.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
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
open MvPolynomial
noncomputable section
namespace ChowFormExtend
section Incidence
variable {F : Type*} [Field F] {n : ℕ}
def incidenceIdeal (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) :
    Ideal (MvPolynomial ((Fin k × Fin n) ⊕ Fin n) F) :=
  I.map (rename Sum.inr) ⊔
    Ideal.span (Set.range fun i : Fin k => ∑ j, X (Sum.inl (i, j)) * X (Sum.inr j))
end Incidence
section Coord
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}
def coordPoly (φ : L →ₗ[K] K) : MvPolynomial Y L →+ MvPolynomial Y K where
  toFun p := AddMonoidAlgebra.map φ.toAddMonoidHom p
  map_zero' := by
    ext m
    rw [coeff_addMonoidAlgebraMap, coeff_zero, coeff_zero, map_zero]
  map_add' p q := by
    ext m
    simp only [coeff_addMonoidAlgebraMap, coeff_add, map_add]
variable {β : Type*} [DecidableEq β]
def coordSupport (b : Module.Basis β K L) (p : MvPolynomial Y L) : Finset β :=
  p.support.biUnion fun m => (b.repr (coeff m p)).support
end Coord
end ChowFormExtend
end
end GroundTheory.Heights₂.Heights


