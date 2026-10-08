-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNamedUnitSquareclasses_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianNamedUnitSquareclasses_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:26:59.477773+00:00
-- url     : https://prove2.me/theorems/47cf30ea-77e5-42a7-88b0-1269ecdec86a
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianNamedUnitSquareclasses source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianNamedUnitSquareclasses

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianNamedUnitSquareclasses
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianGlobalReductionTwo_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianUnitSquareclasses_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianFieldEquiv_p0
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Module.NatInt
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.SetTheory.Cardinal.NatCard

set_option autoImplicit false




/-!
# Named unit squareclasses in the N13 field

The three displayed N13 units are literal units of the maximal order.  Their
first ramified logarithms are `1`, `α²`, and `α + α²`, hence they are
independent modulo squares.  Dirichlet's theorem gives exactly eight unit
squareclasses, so these three classes form a basis and every maximal-order
unit is their binary product times a square.

The proof uses the genuine global reduction homomorphism from
`N13GaussianGlobalReductionTwo`; no field-unit surrogate or enumeration of
the eight classes is used.
-/

open Function
open Polynomial

namespace MazurProof.N13GaussianNamedUnitSquareclasses

noncomputable section

open N13GaussianGlobalArithmetic
open N13GaussianCubicField
open N13GaussianGlobalReductionTwo
open N13GaussianOrderTwo
open N13LocalDlogTwo

abbrev L := N13GaussianGlobalReductionTwo.L

local instance hKIrreducibleFact :
    Fact (Irreducible N13GaussianCubicField.hK) :=
  N13GaussianCubicField.hKIrreducibleFact

@[reducible] local instance fieldL : Field L :=
  AdjoinRoot.instField

local instance intAlgebraL : Algebra ℤ L :=
  Ring.toIntAlgebra L

local instance intAlgebraGI : Algebra ℤ GI :=
  Ring.toIntAlgebra GI

abbrev RelativeO := integralClosure GI L
abbrev O := NumberField.RingOfIntegers L
abbrev F8 := N13LocalDlogTwo.F8

local instance intAlgebraRelativeO : Algebra ℤ RelativeO :=
  Ring.toIntAlgebra RelativeO

local instance intAlgebraAbsoluteO :
    Algebra ℤ (integralClosure ℤ L) :=
  Ring.toIntAlgebra (integralClosure ℤ L)

/-! ## Literal units of the relative and absolute maximal orders -/

def relativeZeta : RelativeO :=
  N13GaussianGlobalReductionTwo.relativeI

def relativeE1 : RelativeO :=
  1 - relativeTheta ^ 2 +
    (relativeZeta - 1) * relativeTheta

def relativeE2 : RelativeO :=
  1 + relativeZeta * relativeTheta ^ 2 +
    (1 + 2 * relativeZeta) * relativeTheta

def relativeE1Inv : RelativeO :=
  1 + relativeZeta + relativeZeta * relativeTheta

def relativeE2Inv : RelativeO :=
  -relativeZeta * relativeTheta ^ 2 -
    (2 + 2 * relativeZeta) * relativeTheta -
    1 + relativeZeta

theorem relativeZeta_sq :
    relativeZeta ^ 2 = (-1 : RelativeO) := by
  rw [relativeZeta, relativeI, ← map_pow,
    N13GaussianGlobalArithmetic.i_sq, map_neg, map_one]

/-- The translated relative power-basis generator satisfies the displayed
Gaussian cubic already inside the relative maximal order. -/
theorem relativeTheta_gaussian_cubic :
    relativeTheta ^ 3 + 2 * relativeTheta ^ 2 -
        relativeTheta - 1 -
      relativeZeta *
        (2 * relativeTheta * (relativeTheta + 1)) = 0 := by
  have hroot :
      aeval
          N13GaussianCubicField.relativeIntegralPowerBasis.gen
          N13GaussianGlobalArithmetic.h = 0 := by
    rw [← minpoly_relative_gen]
    exact minpoly.aeval GI
      N13GaussianCubicField.relativeIntegralPowerBasis.gen
  rw [N13GaussianGlobalArithmetic.h, aeval_def,
    eval₂_comp] at hroot
  have hinner :
      eval₂ (algebraMap GI RelativeO)
          N13GaussianCubicField.relativeIntegralPowerBasis.gen
          (Polynomial.X + Polynomial.C 9) =
        relativeTheta := by
    simp only [eval₂_add, eval₂_X, eval₂_C]
    change
      N13GaussianCubicField.relativeIntegralPowerBasis.gen +
          algebraMap GI RelativeO (9 : GI) =
        N13GaussianCubicField.relativeIntegralPowerBasis.gen + 9
    congr 1
    exact map_natCast (algebraMap GI RelativeO) 9
  rw [hinner] at hroot
  simp only [N13GaussianGlobalArithmetic.g,
    eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, eval₂_one, eval₂_ofNat,
    eval₂_neg, map_ofNat, map_one, map_neg, map_sub,
    map_mul] at hroot
  change
    relativeTheta ^ 3 +
        (2 - 2 * relativeZeta) * relativeTheta ^ 2 +
        (-1 - 2 * relativeZeta) * relativeTheta - 1 = 0
    at hroot
  linear_combination hroot

theorem relativeE1_mul_inv :
    relativeE1 * relativeE1Inv = 1 := by
  simp only [relativeE1, relativeE1Inv]
  rw [← sub_eq_zero]
  calc
    (1 - relativeTheta ^ 2 +
          (relativeZeta - 1) * relativeTheta) *
          (1 + relativeZeta +
            relativeZeta * relativeTheta) - 1 =
      -relativeZeta *
        (relativeTheta ^ 3 + 2 * relativeTheta ^ 2 -
          relativeTheta - 1 -
          relativeZeta *
            (2 * relativeTheta * (relativeTheta + 1))) := by
        ring_nf
        rw [relativeZeta_sq]
        ring
    _ = 0 := by
      rw [relativeTheta_gaussian_cubic, mul_zero]

theorem relativeE2_mul_inv :
    relativeE2 * relativeE2Inv = 1 := by
  simp only [relativeE2, relativeE2Inv]
  rw [← sub_eq_zero]
  calc
    (1 + relativeZeta * relativeTheta ^ 2 +
          (1 + 2 * relativeZeta) * relativeTheta) *
          (-relativeZeta * relativeTheta ^ 2 -
            (2 + 2 * relativeZeta) * relativeTheta -
            1 + relativeZeta) - 1 =
      (relativeTheta + 2 - relativeZeta) *
        (relativeTheta ^ 3 + 2 * relativeTheta ^ 2 -
          relativeTheta - 1 -
          relativeZeta *
            (2 * relativeTheta * (relativeTheta + 1))) := by
        ring_nf
        rw [relativeZeta_sq]
        ring
    _ = 0 := by
      rw [relativeTheta_gaussian_cubic, mul_zero]

def relativeZetaUnit : RelativeOˣ where
  val := relativeZeta
  inv := -relativeZeta
  val_inv := by
    rw [mul_neg, ← pow_two, relativeZeta_sq]
    simp
  inv_val := by
    rw [neg_mul, ← pow_two, relativeZeta_sq]
    simp

def relativeE1Unit : RelativeOˣ where
  val := relativeE1
  inv := relativeE1Inv
  val_inv := relativeE1_mul_inv
  inv_val := by
    rw [mul_comm]
    exact relativeE1_mul_inv

def relativeE2Unit : RelativeOˣ where
  val := relativeE2
  inv := relativeE2Inv
  val_inv := relativeE2_mul_inv
  inv_val := by
    rw [mul_comm]
    exact relativeE2_mul_inv

def zetaUnit : Oˣ :=
  Units.map relativeToRingOfIntegers.toMonoidHom
    relativeZetaUnit

def e1Unit : Oˣ :=
  Units.map relativeToRingOfIntegers.toMonoidHom
    relativeE1Unit

def e2Unit : Oˣ :=
  Units.map relativeToRingOfIntegers.toMonoidHom
    relativeE2Unit

/-! ## The global first-jet logarithm -/

def globalDlogHom : Oˣ →* Multiplicative F8 :=
  RamifiedDlog.dlogHom.comp
    (Units.map globalReduction.toMonoidHom)

def globalDlogAdd : Additive Oˣ →+ F8 :=
  globalDlogHom.toAdditiveLeft

@[simp] theorem globalReduction_zetaUnit :
    Units.map globalReduction.toMonoidHom zetaUnit =
      zetaJet := by
  apply Units.ext
  change
    globalReduction
        (relativeToRingOfIntegers relativeZeta) =
      (zetaJet : DualNumber F8)
  rw [globalReduction_relative]
  simp only [relativeZeta, relativeToOrder_i,
    reduction_i]
  ext <;>
    simp [N13LocalDlogRegimes.gaussianIDual,
      zetaJet, RamifiedDlog.unitOf_val]

@[simp] theorem globalReduction_e1Unit :
    Units.map globalReduction.toMonoidHom e1Unit =
      e1Jet := by
  apply Units.ext
  change
    globalReduction
        (relativeToRingOfIntegers relativeE1) =
      (e1Jet : DualNumber F8)
  rw [globalReduction_relative]
  have hmap :
      relativeToOrder relativeE1 =
        N13GaussianOrderTwo.e1Order := by
    simp [relativeE1, relativeZeta,
      N13GaussianOrderTwo.e1Order]
  rw [hmap, N13GaussianOrderTwo.reduction_e1Order]

@[simp] theorem globalReduction_e2Unit :
    Units.map globalReduction.toMonoidHom e2Unit =
      e2Jet := by
  apply Units.ext
  change
    globalReduction
        (relativeToRingOfIntegers relativeE2) =
      (e2Jet : DualNumber F8)
  rw [globalReduction_relative]
  have hmap :
      relativeToOrder relativeE2 =
        N13GaussianOrderTwo.e2Order := by
    have h2 :
        relativeToOrder (2 : RelativeO) =
          (2 : N13GaussianOrderTwo.Order) :=
      map_natCast relativeToOrder 2
    simp [relativeE2, relativeZeta,
      N13GaussianOrderTwo.e2Order, h2]
  rw [hmap, N13GaussianOrderTwo.reduction_e2Order]

@[simp] theorem globalDlogAdd_zeta :
    globalDlogAdd (Additive.ofMul zetaUnit) = 1 := by
  change
    RamifiedDlog.dlog
        (Units.map globalReduction.toMonoidHom zetaUnit) =
      1
  rw [globalReduction_zetaUnit]
  exact dlog_zeta

@[simp] theorem globalDlogAdd_e1 :
    globalDlogAdd (Additive.ofMul e1Unit) =
      N13LocalDlogTwo.alpha ^ 2 := by
  change
    RamifiedDlog.dlog
        (Units.map globalReduction.toMonoidHom e1Unit) =
      N13LocalDlogTwo.alpha ^ 2
  rw [globalReduction_e1Unit]
  exact dlog_e1

@[simp] theorem globalDlogAdd_e2 :
    globalDlogAdd (Additive.ofMul e2Unit) =
      N13LocalDlogTwo.alpha +
        N13LocalDlogTwo.alpha ^ 2 := by
  change
    RamifiedDlog.dlog
        (Units.map globalReduction.toMonoidHom e2Unit) =
      N13LocalDlogTwo.alpha +
        N13LocalDlogTwo.alpha ^ 2
  rw [globalReduction_e2Unit]
  exact dlog_e2

/-! ## Structural generation of all unit squareclasses -/

abbrev F2 := ZMod 2

/-- Three binary exponents, kept as a product so no class is enumerated. -/
abbrev Exp3 := F2 × F2 × F2

/-- Literal quotient of maximal-order units by the range of squaring. -/
abbrev UnitModSq :=
  Oˣ ⧸ (powMonoidHom 2 : Oˣ →* Oˣ).range

/-- The canonical squareclass map. -/
def unitClassHom : Oˣ →* UnitModSq :=
  QuotientGroup.mk'
    (powMonoidHom 2 : Oˣ →* Oˣ).range

/-- The named representative attached to three binary exponents. -/
def namedWord (c : Exp3) : Oˣ :=
  zetaUnit ^ c.1.val *
    e1Unit ^ c.2.1.val *
    e2Unit ^ c.2.2.val

/-- The corresponding unit squareclass. -/
def namedExponentClass : Exp3 → UnitModSq :=
  fun c => unitClassHom (namedWord c)

/-- In characteristic two, the global logarithm kills every square. -/
theorem globalDlogAdd_sq (u : Oˣ) :
    globalDlogAdd (Additive.ofMul (u ^ 2)) = 0 := by
  simpa only [pow_two, ofMul_mul, map_add] using
    CharTwo.add_self_eq_zero
      (globalDlogAdd (Additive.ofMul u))

/-- Equal literal unit squareclasses have equal logarithms.  This direct
quotient argument avoids constructing any list of representatives. -/
theorem globalDlogAdd_eq_of_unitClass_eq
    {x y : Oˣ}
    (hxy : unitClassHom x = unitClassHom y) :
    globalDlogAdd (Additive.ofMul x) =
      globalDlogAdd (Additive.ofMul y) := by
  have hsquare :
      x / y ∈ (powMonoidHom 2 : Oˣ →* Oˣ).range :=
    (QuotientGroup.eq_iff_div_mem
      (N := (powMonoidHom 2 : Oˣ →* Oˣ).range)).mp hxy
  rcases hsquare with ⟨u, hu⟩
  have hzero :
      globalDlogAdd (Additive.ofMul (x / y)) = 0 := by
    rw [← hu]
    exact globalDlogAdd_sq u
  have hsub :
      globalDlogAdd (Additive.ofMul x) -
          globalDlogAdd (Additive.ofMul y) = 0 := by
    simpa using hzero
  exact sub_eq_zero.mp hsub

/-- The logarithm of a named word, expanded in the structural power basis
`1, α, α²` of the residue field. -/
theorem globalDlogAdd_namedWord (c : Exp3) :
    globalDlogAdd (Additive.ofMul (namedWord c)) =
      (c.1 : F8) +
        (c.2.2 : F8) * N13LocalDlogTwo.alpha +
        (c.2.1 + c.2.2 : F2) *
          N13LocalDlogTwo.alpha ^ 2 := by
  simp [namedWord, ← Nat.cast_smul_eq_nsmul (R := F2),
    Algebra.smul_def]
  ring

/-- No polynomial of degree below three vanishes at the residue generator.
This is the only independence input; it uses divisibility by the defining
cubic, not an enumeration of `F₈`. -/
private theorem residue_coeffs_zero
    (c0 c1 c2 : F2)
    (h :
      (c0 : F8) + (c1 : F8) * N13LocalDlogTwo.alpha +
          (c2 : F8) * N13LocalDlogTwo.alpha ^ 2 = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 := by
  let p : F2[X] :=
    C c0 + C c1 * X + C c2 * X ^ 2
  have hm :
      AdjoinRoot.mk N13LocalDlogTwo.residueCubic p = 0 := by
    simpa [p, N13LocalDlogTwo.alpha, map_add, map_mul,
      map_pow] using h
  have hdvd : N13LocalDlogTwo.residueCubic ∣ p :=
    AdjoinRoot.mk_eq_zero.mp hm
  have hpdeg : p.natDegree ≤ 2 := by
    dsimp [p]
    compute_degree
  have hdeg :
      p.natDegree <
        N13LocalDlogTwo.residueCubic.natDegree := by
    rw [N13LocalDlogTwo.residueCubic_natDegree]
    omega
  have hpzero : p = 0 :=
    Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg
  have h0 :=
    congrArg (fun q : F2[X] => q.coeff 0) hpzero
  have h1 :=
    congrArg (fun q : F2[X] => q.coeff 1) hpzero
  have h2 :=
    congrArg (fun q : F2[X] => q.coeff 2) hpzero
  simp [p, coeff_X_pow] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

/-- The three named exponent bits give distinct unit squareclasses. -/
theorem namedExponentClass_injective :
    Function.Injective namedExponentClass := by
  rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ hclass
  have hclass' :
      unitClassHom (namedWord (i, j, k)) =
        unitClassHom (namedWord (i', j', k')) := by
    simpa [namedExponentClass] using hclass
  have hdlog :=
    globalDlogAdd_eq_of_unitClass_eq hclass'
  have hdlog' :
      (i : F8) + (k : F8) * N13LocalDlogTwo.alpha +
          (j + k : F2) * N13LocalDlogTwo.alpha ^ 2 =
        (i' : F8) + (k' : F8) * N13LocalDlogTwo.alpha +
          (j' + k' : F2) *
            N13LocalDlogTwo.alpha ^ 2 := by
    simpa [namedExponentClass, globalDlogAdd_namedWord]
      using hdlog
  simp only [map_add] at hdlog'
  have hzero :
      ((i - i' : F2) : F8) +
          ((k - k' : F2) : F8) *
            N13LocalDlogTwo.alpha +
          (((j + k) - (j' + k') : F2) : F8) *
            N13LocalDlogTwo.alpha ^ 2 = 0 := by
    simp only [map_sub, map_add]
    linear_combination hdlog'
  obtain ⟨hi0, hk0, hjk0⟩ :=
    residue_coeffs_zero
      (i - i') (k - k') ((j + k) - (j' + k'))
      hzero
  have hi : i = i' := sub_eq_zero.mp hi0
  have hk : k = k' := sub_eq_zero.mp hk0
  have hjk : j + k = j' + k' := sub_eq_zero.mp hjk0
  have hj : j = j' := by
    calc
      j = (j + k) - k := by simp
      _ = (j' + k') - k := by rw [hjk]
      _ = (j' + k) - k := by rw [hk]
      _ = j' := by simp
  exact Prod.ext hi (Prod.ext hj hk)

@[simp] theorem unitModSq_natCard :
    Nat.card UnitModSq = 8 :=
  N13GaussianUnitSquareclasses.unit_squareclass_natCard

/-- Cardinality eight turns the structural independence theorem into
generation of every unit squareclass. -/
theorem namedExponentClass_bijective :
    Function.Bijective namedExponentClass := by
  have hcard0 : Nat.card UnitModSq ≠ 0 := by
    rw [unitModSq_natCard]
    norm_num
  letI : Finite UnitModSq :=
    Nat.finite_of_card_ne_zero hcard0
  apply
    (Nat.bijective_iff_injective_and_card
      namedExponentClass).2
  refine ⟨namedExponentClass_injective, ?_⟩
  calc
    Nat.card Exp3 = 8 := by
      norm_num [Exp3, F2, Nat.card_prod, Nat.card_zmod]
    _ = Nat.card UnitModSq := unitModSq_natCard.symm

/-- Every maximal-order unit is a named binary product times a square.
The proof never examines the eight possible exponent triples. -/
theorem unit_modSq_decompose_named (ε : Oˣ) :
    ∃ i j k : F2, ∃ η : Oˣ,
      ε =
        zetaUnit ^ i.val *
          e1Unit ^ j.val *
          e2Unit ^ k.val * η ^ 2 := by
  obtain ⟨c, hc⟩ :=
    namedExponentClass_bijective.2 (unitClassHom ε)
  rcases c with ⟨i, j, k⟩
  have hq :
      (ε : UnitModSq) =
        (namedWord (i, j, k) : UnitModSq) := by
    simpa [namedExponentClass, unitClassHom] using hc.symm
  have hsquare :
      ε / namedWord (i, j, k) ∈
        (powMonoidHom 2 : Oˣ →* Oˣ).range :=
    (QuotientGroup.eq_iff_div_mem
      (N := (powMonoidHom 2 : Oˣ →* Oˣ).range)).mp hq
  rcases hsquare with ⟨η, hη⟩
  refine ⟨i, j, k, η, ?_⟩
  calc
    ε =
        (ε / namedWord (i, j, k)) *
          namedWord (i, j, k) := by simp
    _ = η ^ 2 * namedWord (i, j, k) := by
      rw [← hη]
      rfl
    _ = namedWord (i, j, k) * η ^ 2 := mul_comm _ _
    _ =
        zetaUnit ^ i.val *
          e1Unit ^ j.val *
          e2Unit ^ k.val * η ^ 2 := by rfl

end

end MazurProof.N13GaussianNamedUnitSquareclasses


