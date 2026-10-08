-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerPID_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerPID_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:11:38.436727+00:00
-- url     : https://prove2.me/theorems/20379345-14a9-48ca-89e2-4c60f829f66a
-- title:
--   FLT.Assumptions.MazurProof.N13GlobalKummerPID source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GlobalKummerPID

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GlobalKummerPID
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianClassNumberOne_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerIdealSquare_p0

set_option autoImplicit false




/-!
# Class-number-one endpoint for normalized N13 Kummer ideals

The structural class-number-one theorem supplies the sole global
principality input in the good-locus ideal-square theorem.  Consequently
every normalized N13 Kummer value becomes a unit times a square after
removing its denominator scale and the different.
-/

namespace MazurProof.N13GlobalKummerPID

noncomputable section

open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare

abbrev L := N13GaussianCubicField.L

local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact

@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField

local instance intAlgebraL : Algebra ℤ L :=
  Ring.toIntAlgebra L

/-- Principality transports across a ring equivalence. -/
theorem isPrincipalIdealRing_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    [IsPrincipalIdealRing S]
    (e : R ≃+* S) :
    IsPrincipalIdealRing R := by
  constructor
  intro I
  let J : Ideal S := I.map e
  obtain ⟨y, hy⟩ :=
    Submodule.IsPrincipal.principal
      (J : Submodule S S)
  have hyIdeal :
      J = Ideal.span ({y} : Set S) :=
    hy
  let x : R := e.symm y
  refine ⟨x, ?_⟩
  apply e.idealComapOrderIso.symm.injective
  change
    I.map e =
      (Ideal.span ({x} : Set R)).map e
  calc
    I.map e = J := rfl
    _ = Ideal.span ({y} : Set S) := hyIdeal
    _ =
        Ideal.map e
          (Ideal.span ({x} : Set R)) := by
      rw [Ideal.map_span, Set.image_singleton]
      simp only [x, e.apply_symm_apply]

private theorem isIntegralElem_int_of
    {A : Type*} [Ring A]
    {f g : ℤ →+* A} {x : A}
    (hx : f.IsIntegralElem x) :
    g.IsIntegralElem x := by
  have hfg : g = f :=
    RingHom.ext_int _ _
  rwa [hfg]

private def integralClosureToClassNumberOrder (x : O) :
    N13GaussianClassNumberOne.O :=
  ⟨x.val, isIntegralElem_int_of x.property⟩

private theorem subtypeConstructor_val {A : Type*} {p : A → Prop}
    (a : A) (ha : p a) :
    (⟨a, ha⟩ : Subtype p).val = a := rfl

private theorem integralClosureToClassNumberOrder_val (x : O) :
    (integralClosureToClassNumberOrder x).val = x.val :=
  subtypeConstructor_val x.val
    (isIntegralElem_int_of (g := algebraMap ℤ L) x.property)

/-- The integral-closure presentation used by normalization is canonically
ring-equivalent to Mathlib's ring-of-integers presentation used by the
class-number proof.  The only apparent discrepancy is the chosen
`ℤ`-algebra instance; integer ring homomorphisms are unique. -/
def integralClosureEquivClassNumberOrder :
    O ≃+* N13GaussianClassNumberOne.O where
  toFun := integralClosureToClassNumberOrder
  invFun x :=
    ⟨x.1, isIntegralElem_int_of x.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The normalization order and the class-number order have literally the
same underlying element of the ambient number field.  Exporting this small
carrier theorem prevents downstream proofs from unfolding the full ring
equivalence. -/
@[simp] theorem coe_integralClosureEquivClassNumberOrder
    (x : O) :
    (integralClosureEquivClassNumberOrder.toEquiv.toFun x).val =
      x.val :=
  integralClosureToClassNumberOrder_val x

/-- The unconditional class-number-one specialization of the good-locus
square factorization. -/
theorem normalizedKummerInteger_associated_square
    (D : N13LowDegreeKummerHom.LowRep) :
    ∃ z : GoodOrder D,
      Associated
        (algebraMap O (GoodOrder D)
          (normalizedKummerInteger D))
        (z ^ 2) := by
  letI : IsPrincipalIdealRing O :=
    @isPrincipalIdealRing_of_ringEquiv
      O N13GaussianClassNumberOne.O
      inferInstance inferInstance
      N13GaussianClassNumberOne.isPrincipalIdealRingO
      integralClosureEquivClassNumberOrder
  exact
    N13GlobalKummerIdealSquare.normalizedKummerInteger_associated_square D

end

end MazurProof.N13GlobalKummerPID


