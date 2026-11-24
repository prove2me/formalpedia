-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FirstPointNeSecondPoint
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FirstPointNeSecondPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:38.874913+00:00
-- url     : https://prove2.me/theorems/aa9cfcab-5e4f-4295-9d63-a1a00bfe0920
-- title:
--   First Point Ne Second Point
-- statement:
--   Definitions and structural lemmas for First Point Ne Second Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/FirstPointNeSecondPoint.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_FderivFderivLogRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial
noncomputable section
namespace P1
abbrev Fld : Type := FractionRing (Polynomial ℤ)
instance : CharZero Fld :=
  charZero_of_injective_algebraMap (IsFractionRing.injective (Polynomial ℤ) Fld)
instance (priority := 10000) fldAlgInt : Algebra ℤ Fld := Ring.toIntAlgebra Fld
abbrev J2 : Type := Ix (Fin 2)
def p0 : J2 := ⟨(), 0⟩
def p1 : J2 := ⟨(), 1⟩
def val (q : J2) : Polynomial ℤ := if q.2 = 0 then 1 else Polynomial.X
def x : J2 → Fld := fun q ↦ algebraMap (Polynomial ℤ) Fld (val q)
def dehom : MvPolynomial J2 ℤ →+* Polynomial ℤ := eval₂Hom (Int.castRingHom _) val
def homog (p : Polynomial ℤ) (d : ℕ) : MvPolynomial J2 ℤ :=
  ∑ i ∈ Finset.range (d + 1), monomial (Finsupp.single p1 i + Finsupp.single p0 (d - i)) (p.coeff i)
abbrev fs : ConeMetric ℂ J2 := fsMetric J2
end P1
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel


