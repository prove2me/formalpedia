-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNormalizationOrderTransport_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianNormalizationOrderTransport_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:18:20.44383+00:00
-- url     : https://prove2.me/theorems/a99776a5-dddd-49f7-a3ed-21736ccfa2cd
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianNormalizationOrderTransport source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianNormalizationOrderTransport

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianNormalizationOrderTransport
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerPID_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianCandidateUnitAssembly_p0

set_option autoImplicit false




/-!
# Transport from the N13 normalization order

The global Kummer normalization and the structural class-number computation
use definitionally different presentations of the same integral closure.
This file crosses that seam once through the compiled ring equivalence, then
transports a unit-times-square identity to the sextic presentation.

When every principal count is even there is no exceptional prime carrier.
Consequently the fourth candidate coordinate is literally zero.
-/

namespace MazurProof.N13GaussianNormalizationOrderTransport

noncomputable section

abbrev Lg := N13GaussianCubicField.L
abbrev Ls := N13SexticSquareclass.SexticAlgebra
abbrev Oi : Type := N13GlobalKummerIdealSquare.O
abbrev On : Type := N13GaussianNamedUnitTransport.O

local instance fieldLs : Field Ls :=
  N13SexticIrreducible.sexticAlgebraField

/-- The compiled equivalence between the normalization order and the
maximal-order presentation carrying the named-unit theorem. -/
abbrev normalizationOrderEquiv : Oi ≃+* On :=
  N13GlobalKummerPID.integralClosureEquivClassNumberOrder

/-- Direct transport from the normalization order to the sextic field. -/
def normalizationOrderToSextic : Oi →+* Ls :=
  N13GaussianNamedUnitTransport.orderToSextic.comp
    normalizationOrderEquiv.toRingHom

/-- The direct transport preserves the underlying Gaussian field element.
The proof uses only the two small carrier interfaces and never unfolds the
integral-closure equivalence. -/
@[simp] theorem normalizationOrderToSextic_apply
    (x : Oi) :
    normalizationOrderToSextic x =
      N13GaussianFieldEquiv.sexticEquivGaussian.symm
        (x : Lg) := by
  calc
    normalizationOrderToSextic x =
        N13GaussianNamedUnitTransport.orderToSextic
          (normalizationOrderEquiv x) := rfl
    _ =
        N13GaussianFieldEquiv.sexticEquivGaussian.symm
          ((normalizationOrderEquiv x : On) : Lg) :=
      N13GaussianNamedUnitTransport.orderToSextic_apply
        (normalizationOrderEquiv x)
    _ =
        N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (x : Lg) := by
      have hfun :
          normalizationOrderEquiv x =
            N13GlobalKummerPID.integralClosureEquivClassNumberOrder.toFun x := rfl
      rw [hfun]
      exact
        congrArg N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (N13GlobalKummerPID.coe_integralClosureEquivClassNumberOrder x)

theorem normalizationOrderToSextic_injective :
    Function.Injective normalizationOrderToSextic :=
  N13GaussianNamedUnitTransport.orderToSextic_injective.comp
    normalizationOrderEquiv.injective

/-- The unit map induced by the composite order embedding factors through
the compiled maximal-order unit transport. -/
theorem unitsMap_normalizationOrderToSextic_eq :
    Units.map normalizationOrderToSextic.toMonoidHom =
      N13GaussianNamedUnitTransport.orderUnitsToSextic.comp
        (Units.map normalizationOrderEquiv.toMonoidHom) := by
  rw [← N13GaussianNamedUnitTransport.unitsMap_orderToSextic_eq]
  exact
    Units.map_comp normalizationOrderEquiv.toMonoidHom
      N13GaussianNamedUnitTransport.orderToSextic.toMonoidHom

@[simp] theorem unitsMap_normalizationOrderToSextic_apply
    (ε : Oiˣ) :
    Units.map normalizationOrderToSextic.toMonoidHom ε =
      N13GaussianNamedUnitTransport.orderUnitsToSextic
        (Units.map normalizationOrderEquiv.toMonoidHom ε) := by
  rw [unitsMap_normalizationOrderToSextic_eq]
  rfl

/-- Package a nonzero normalization-order element as a sextic-field unit. -/
def unitOfNonzero (x : Oi) (hx : x ≠ 0) : Lsˣ :=
  Units.mk0 (normalizationOrderToSextic x)
    (by
      intro hzero
      apply hx
      apply normalizationOrderToSextic_injective
      simpa using hzero)

@[simp] theorem coe_unitOfNonzero
    (x : Oi) (hx : x ≠ 0) :
    (unitOfNonzero x hx : Ls) =
      normalizationOrderToSextic x :=
  rfl

/-- An exact unit-times-square identity in the normalization order transports
to an exact unit-times-square identity in the sextic field. -/
theorem exists_transportedUnit_mul_sq
    (x : Oi) (hx : x ≠ 0)
    (ε : Oiˣ) (y : Oi)
    (h : x = (ε : Oi) * y ^ 2) :
    ∃ s : Lsˣ,
      unitOfNonzero x hx =
        N13GaussianNamedUnitTransport.orderUnitsToSextic
            (Units.map normalizationOrderEquiv.toMonoidHom ε) *
          s ^ 2 := by
  have hy : y ≠ 0 := by
    intro hy0
    apply hx
    rw [h, hy0]
    simp
  refine ⟨unitOfNonzero y hy, ?_⟩
  apply Units.ext
  change
    normalizationOrderToSextic x =
      (N13GaussianNamedUnitTransport.orderUnitsToSextic
          (Units.map normalizationOrderEquiv.toMonoidHom ε) : Ls) *
        normalizationOrderToSextic y ^ 2
  rw [← unitsMap_normalizationOrderToSextic_apply]
  change
    normalizationOrderToSextic x =
      normalizationOrderToSextic (ε : Oi) *
        normalizationOrderToSextic y ^ 2
  simpa only [map_mul, map_pow] using
    congrArg normalizationOrderToSextic h

/-- With no exceptional carrier, the transported unit is one of the three
named-unit candidates, times a square. -/
theorem exists_candidateUnit_zeroCarrier_mul_sq
    (x : Oi) (hx : x ≠ 0)
    (ε : Oiˣ) (y : Oi)
    (h : x = (ε : Oi) * y ^ 2) :
    ∃ i j k : ZMod 2, ∃ t : Lsˣ,
      unitOfNonzero x hx =
        N13CandidateCollapse.candidateUnit
          i j k 0 * t ^ 2 := by
  obtain ⟨s, hs⟩ :=
    exists_transportedUnit_mul_sq x hx ε y h
  apply
    N13GaussianCandidateUnitAssembly.exists_candidateUnit_mul_sq
      (unitOfNonzero x hx)
      (Units.map normalizationOrderEquiv.toMonoidHom ε)
      0 s
  simpa using hs

/-- Passing the zero-carrier identity to fake squareclasses fixes the fourth
candidate coordinate to zero. -/
theorem fakeClass_eq_candidateClass_zeroCarrier
    (x : Oi) (hx : x ≠ 0)
    (ε : Oiˣ) (y : Oi)
    (h : x = (ε : Oi) * y ^ 2) :
    ∃ i j k : ZMod 2,
      ((unitOfNonzero x hx : Lsˣ) :
        FakeSquareClass.Target (algebraMap ℚ Ls)) =
        N13CandidateCollapse.candidateClass
          i j k 0 := by
  obtain ⟨s, hs⟩ :=
    exists_transportedUnit_mul_sq x hx ε y h
  apply
    N13GaussianCandidateUnitAssembly.fakeClass_eq_candidateClass
      (unitOfNonzero x hx)
      (Units.map normalizationOrderEquiv.toMonoidHom ε)
      0 s
  simpa using hs

end

end MazurProof.N13GaussianNormalizationOrderTransport


