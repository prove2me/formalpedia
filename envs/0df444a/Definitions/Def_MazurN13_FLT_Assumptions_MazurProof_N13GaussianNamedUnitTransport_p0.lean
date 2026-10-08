-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNamedUnitTransport_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianNamedUnitTransport_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:31:18.920713+00:00
-- url     : https://prove2.me/theorems/1c01b598-eccb-4cfc-8980-61f3cbb1f674
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianNamedUnitTransport source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianNamedUnitTransport

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianNamedUnitTransport
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNamedUnitSquareclasses_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CandidateCollapse_p0

set_option autoImplicit false




/-!
# Transport of the named N13 units

The unit squareclass computation is carried out in the maximal order of the
Gaussian cubic presentation, while the fake-descent candidates use the sextic
presentation.  This file gives the literal carrier-preserving map between the
two and proves that the three named units agree under it.

Consequently the structural maximal-order unit decomposition transports to the
same three units appearing in `N13CandidateCollapse`, without enumerating the
eight unit squareclasses.
-/

namespace MazurProof.N13GaussianNamedUnitTransport

noncomputable section

abbrev Lg := N13GaussianCubicField.L
abbrev Ls := N13SexticSquareclass.SexticAlgebra

local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact

@[reducible] local instance fieldLg : Field Lg :=
  AdjoinRoot.instField

abbrev O := NumberField.RingOfIntegers Lg

/-- The maximal-order carrier embedded into its Gaussian cubic fraction
field.  It is written explicitly to avoid choosing between definitionally
different `Algebra O Lg` instances. -/
def orderToGaussian : O →+* Lg :=
  (Subalgebra.val
      (integralClosure N13GaussianGlobalArithmetic.GI Lg)).toRingHom.comp
    N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm.toRingHom

/-- The explicit maximal-order map has the same underlying field value as
the canonical ring-of-integers coercion. -/
@[simp] theorem orderToGaussian_apply (x : O) :
    orderToGaussian x = (x : Lg) := by
  letI intAlgebraLg : Algebra ℤ Lg :=
    Ring.toIntAlgebra Lg
  letI hO : IsIntegralClosure O ℤ Lg :=
    NumberField.RingOfIntegers.instIsIntegralClosureInt
  change
    ((N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm x :
        N13GaussianGlobalReductionTwo.RelativeO) : Lg) =
      (x : Lg)
  simp [N13GaussianGlobalReductionTwo.relativeToRingOfIntegers,
    N13GaussianNumberField.integralClosureToRingOfIntegersRingEquiv,
    N13GaussianNumberField.relativeToAbsoluteAlgEquiv]
  let e :
      (integralClosure ℤ Lg) ≃ₐ[ℤ] O :=
    IsIntegralClosure.equiv
      ℤ (integralClosure ℤ Lg) Lg O
  have he :=
    IsIntegralClosure.algebraMap_equiv
      ℤ (integralClosure ℤ Lg) Lg O (e.symm x)
  calc
    algebraMap (integralClosure ℤ Lg) Lg (e.symm x) =
        algebraMap O Lg (e (e.symm x)) :=
      he.symm
    _ = algebraMap O Lg x := by
      rw [e.apply_symm_apply]

/-- The explicit maximal-order embedding is injective. -/
theorem orderToGaussian_injective :
    Function.Injective orderToGaussian := by
  intro x y hxy
  apply NumberField.RingOfIntegers.ext
  simpa only [orderToGaussian_apply] using hxy

/-- The carrier-preserving ring map from the maximal order directly to the
sextic presentation.  No additional algebra instance is introduced. -/
def orderToSextic : O →+* Ls :=
  N13GaussianFieldEquiv.sexticEquivGaussian.symm.toRingEquiv.toRingHom.comp
    orderToGaussian

@[simp] theorem orderToSextic_apply (x : O) :
    orderToSextic x =
      N13GaussianFieldEquiv.sexticEquivGaussian.symm (x : Lg) := by
  simp [orderToSextic]

theorem orderToSextic_injective :
    Function.Injective orderToSextic :=
  N13GaussianFieldEquiv.sexticEquivGaussian.symm.injective.comp
    orderToGaussian_injective

def orderUnitsToGaussian : Oˣ →* Lgˣ :=
  Units.map orderToGaussian.toMonoidHom

/-- Transport maximal-order units through the proved equivalence between the
sextic and Gaussian cubic presentations. -/
def orderUnitsToSextic : Oˣ →* Lsˣ :=
  (Units.map
      N13GaussianFieldEquiv.sexticEquivGaussian.symm.toMonoidHom).comp
    orderUnitsToGaussian

/-- The previously defined unit transport is exactly the unit map induced by
the direct carrier-preserving ring homomorphism. -/
theorem unitsMap_orderToSextic_eq :
    Units.map orderToSextic.toMonoidHom =
      orderUnitsToSextic := by
  ext u
  rfl

theorem map_relativeTheta :
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianGlobalReductionTwo.relativeTheta =
      N13GaussianFieldEquiv.gaussianTheta := by
  change
    ((N13GaussianCubicField.relativeIntegralPowerBasis.gen :
        N13GaussianGlobalReductionTwo.RelativeO) : Lg) + 9 =
      N13GaussianCubicField.alpha + 9
  rw [N13GaussianCubicField.coe_relativeIntegralPowerBasis_gen]

theorem map_relativeZeta :
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianNamedUnitSquareclasses.relativeZeta =
      N13GaussianFieldEquiv.gaussianI := by
  change
    algebraMap N13GaussianGlobalArithmetic.GI Lg
        N13GaussianGlobalArithmetic.i =
      N13GaussianFieldEquiv.gaussianI
  rw [N13GaussianFieldEquiv.gaussianI,
    IsScalarTower.algebraMap_apply
      N13GaussianGlobalArithmetic.GI
      N13GaussianCubicField.K Lg]

theorem orderUnitsToGaussian_zeta_val :
    orderToGaussian
        (N13GaussianNamedUnitSquareclasses.zetaUnit : O) =
      N13GaussianFieldEquiv.gaussianI := by
  change
    ((N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm
      (N13GaussianGlobalReductionTwo.relativeToRingOfIntegers
        N13GaussianNamedUnitSquareclasses.relativeZeta) :
      N13GaussianGlobalReductionTwo.RelativeO) : Lg) =
      N13GaussianFieldEquiv.gaussianI
  rw [N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm_apply_apply]
  exact map_relativeZeta

theorem orderUnitsToGaussian_e1_val :
    orderToGaussian
        (N13GaussianNamedUnitSquareclasses.e1Unit : O) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e1 := by
  change
    ((N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm
      (N13GaussianGlobalReductionTwo.relativeToRingOfIntegers
        N13GaussianNamedUnitSquareclasses.relativeE1) :
      N13GaussianGlobalReductionTwo.RelativeO) : Lg) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e1
  rw [N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm_apply_apply,
    N13GaussianFieldEquiv.sexticEquivGaussian_e1]
  change
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianNamedUnitSquareclasses.relativeE1 =
      1 - N13GaussianFieldEquiv.gaussianTheta ^ 2 +
        (N13GaussianFieldEquiv.gaussianI - 1) *
          N13GaussianFieldEquiv.gaussianTheta
  simp only [N13GaussianNamedUnitSquareclasses.relativeE1,
    map_add, map_sub, map_pow, map_mul, map_one,
    map_relativeTheta, map_relativeZeta]

theorem orderUnitsToGaussian_e2_val :
    orderToGaussian
        (N13GaussianNamedUnitSquareclasses.e2Unit : O) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e2 := by
  change
    ((N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm
      (N13GaussianGlobalReductionTwo.relativeToRingOfIntegers
        N13GaussianNamedUnitSquareclasses.relativeE2) :
      N13GaussianGlobalReductionTwo.RelativeO) : Lg) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e2
  rw [N13GaussianGlobalReductionTwo.relativeToRingOfIntegers.symm_apply_apply,
    N13GaussianFieldEquiv.sexticEquivGaussian_e2]
  change
    algebraMap N13GaussianGlobalReductionTwo.RelativeO Lg
        N13GaussianNamedUnitSquareclasses.relativeE2 =
      1 + N13GaussianFieldEquiv.gaussianI *
          N13GaussianFieldEquiv.gaussianTheta ^ 2 +
        (1 + 2 * N13GaussianFieldEquiv.gaussianI) *
          N13GaussianFieldEquiv.gaussianTheta
  simp only [N13GaussianNamedUnitSquareclasses.relativeE2,
    map_add, map_mul, map_pow, map_one, map_ofNat,
    map_relativeTheta, map_relativeZeta]

@[simp] theorem orderUnitsToSextic_zeta :
    orderUnitsToSextic
        N13GaussianNamedUnitSquareclasses.zetaUnit =
      N13CandidateCollapse.zetaUnit := by
  apply Units.ext
  apply N13GaussianFieldEquiv.sexticEquivGaussian.injective
  change
    N13GaussianFieldEquiv.sexticEquivGaussian
        (N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (orderToGaussian
            (N13GaussianNamedUnitSquareclasses.zetaUnit : O))) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.zeta
  rw [N13GaussianFieldEquiv.sexticEquivGaussian.apply_symm_apply,
    N13GaussianFieldEquiv.sexticEquivGaussian_zeta]
  exact orderUnitsToGaussian_zeta_val

@[simp] theorem orderUnitsToSextic_e1 :
    orderUnitsToSextic
        N13GaussianNamedUnitSquareclasses.e1Unit =
      N13CandidateCollapse.e1Unit := by
  apply Units.ext
  apply N13GaussianFieldEquiv.sexticEquivGaussian.injective
  change
    N13GaussianFieldEquiv.sexticEquivGaussian
        (N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (orderToGaussian
            (N13GaussianNamedUnitSquareclasses.e1Unit : O))) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e1
  rw [N13GaussianFieldEquiv.sexticEquivGaussian.apply_symm_apply]
  exact orderUnitsToGaussian_e1_val

@[simp] theorem orderUnitsToSextic_e2 :
    orderUnitsToSextic
        N13GaussianNamedUnitSquareclasses.e2Unit =
      N13CandidateCollapse.e2Unit := by
  apply Units.ext
  apply N13GaussianFieldEquiv.sexticEquivGaussian.injective
  change
    N13GaussianFieldEquiv.sexticEquivGaussian
        (N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (orderToGaussian
            (N13GaussianNamedUnitSquareclasses.e2Unit : O))) =
      N13GaussianFieldEquiv.sexticEquivGaussian
        N13SexticSquareclass.e2
  rw [N13GaussianFieldEquiv.sexticEquivGaussian.apply_symm_apply]
  exact orderUnitsToGaussian_e2_val

/-- Every maximal-order unit becomes the same named binary word used by the
sextic candidate calculation, times a square. -/
theorem orderUnitsToSextic_decompose_named (ε : Oˣ) :
    ∃ i j k : ZMod 2, ∃ η : Lsˣ,
      orderUnitsToSextic ε =
        N13CandidateCollapse.zetaUnit ^ i.val *
          N13CandidateCollapse.e1Unit ^ j.val *
          N13CandidateCollapse.e2Unit ^ k.val * η ^ 2 := by
  obtain ⟨i, j, k, η, hη⟩ :=
    N13GaussianNamedUnitSquareclasses.unit_modSq_decompose_named ε
  refine ⟨i, j, k, orderUnitsToSextic η, ?_⟩
  simpa only [map_mul, map_pow, orderUnitsToSextic_zeta,
    orderUnitsToSextic_e1, orderUnitsToSextic_e2] using
    congrArg (fun u : Oˣ => orderUnitsToSextic u) hη

end

end MazurProof.N13GaussianNamedUnitTransport


