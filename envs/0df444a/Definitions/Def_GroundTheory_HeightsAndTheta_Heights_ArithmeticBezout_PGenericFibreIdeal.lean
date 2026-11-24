-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreIdeal
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGenericFibreIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:11:31.561171+00:00
-- url     : https://prove2.me/theorems/9350fdc7-1315-4357-a878-6d62ec3cd2cc
-- title:
--   PGeneric Fibre Ideal
-- statement:
--   Definitions and structural lemmas for PGeneric Fibre Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGenericFibreIdeal.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LinFormOneZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ObjectsChow
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)
namespace GenericFibreIdeal
variable {n : ℕ}
def blkEquiv (n : ℕ) : Fin n ≃ (Σ _ : Unit, PBlk n ()) where
  toFun i := ⟨(), i⟩
  invFun p := p.2
  left_inv _ := rfl
  right_inv p := by rcases p with ⟨⟨⟩, i⟩; rfl
def blkRingEquiv (n : ℕ) : MvPolynomial (Fin n) ℤ ≃+* MRing (PBlk n) :=
  (renameEquiv ℤ (blkEquiv n)).toRingEquiv
attribute [local instance] MvPolynomial.algebraMvPolynomial
abbrev intUnits (n : ℕ) : Submonoid (MvPolynomial (Fin n) ℤ) :=
  (nonZeroDivisors ℤ).map (C : ℤ →+* MvPolynomial (Fin n) ℤ)
instance : IsLocalization (intUnits n) (MvPolynomial (Fin n) ℚ) :=
  MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
section Homog
attribute [local instance] MvPolynomial.gradedAlgebra
end Homog
end GenericFibreIdeal
end ObjectsChow
end GroundTheory.Heights₂.Heights


