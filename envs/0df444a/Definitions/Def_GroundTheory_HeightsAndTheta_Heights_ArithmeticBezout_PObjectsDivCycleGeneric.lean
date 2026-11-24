-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PObjectsDivCycleGeneric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:43.188232+00:00
-- url     : https://prove2.me/theorems/3744cc23-9fdd-41e6-b828-d7ad7845f8f7
-- title:
--   PObjects Div Cycle Generic
-- statement:
--   Definitions and structural lemmas for PObjects Div Cycle Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PObjectsDivCycleGeneric.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ImportsAlt
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
namespace DivCycleGeneric
open MvPolynomial
section Localization
variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] (S : Submonoid A)
  [IsLocalization S A']
end Localization
section Generic
variable {n : ℕ}
def blkEquiv (n : ℕ) : (Σ _ : Unit, ReciprocityTheory.ChartRestriction.G.Geo.PBlk n ()) ≃ Fin n where
  toFun p := p.2
  invFun := blk n
  left_inv _ := rfl
  right_inv _ := rfl
def toGeneric (n : ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n) →+* MvPolynomial (Fin n) ℚ :=
  (MvPolynomial.map (Int.castRingHom ℚ)).comp (rename (R := ℤ) (blkEquiv n)).toRingHom
abbrev genericAlgebra (n : ℕ) :
    Algebra (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) (MvPolynomial (Fin n) ℚ) :=
  (toGeneric n).toAlgebra
attribute [local instance] genericAlgebra
abbrev intUnits (n : ℕ) : Submonoid (ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n)) :=
  (nonZeroDivisors ℤ).map (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing (ReciprocityTheory.ChartRestriction.G.Geo.PBlk n))
instance isLocalization_generic (n : ℕ) : IsLocalization (intUnits n) (MvPolynomial (Fin n) ℚ) := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Σ _ : Unit, ReciprocityTheory.ChartRestriction.G.Geo.PBlk n ()) (R := ℤ) (S := ℚ)
  have : IsLocalization (intUnits n) (MvPolynomial (Σ _ : Unit, ReciprocityTheory.ChartRestriction.G.Geo.PBlk n ()) ℚ) :=
    MvPolynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  refine IsLocalization.isLocalization_of_algEquiv (intUnits n)
    (AlgEquiv.ofRingEquiv (f := (renameEquiv ℚ (blkEquiv n)).toRingEquiv) fun x => ?_)
  show (renameEquiv ℚ (blkEquiv n)) (MvPolynomial.map (algebraMap ℤ ℚ) x) =
    MvPolynomial.map (Int.castRingHom ℚ) (rename (blkEquiv n) x)
  rw [renameEquiv_apply, map_rename, algebraMap_int_eq]
end Generic
end DivCycleGeneric
end ObjectsChow
end GroundTheory.Heights₂.Heights


