-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialCechObstruction_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialCechObstruction_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:32:36.893801+00:00
-- url     : https://prove2.me/theorems/ad028f3b-8e5d-44f3-a24f-608f9ea3ad24
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialCechObstruction source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialCechObstruction

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialCechObstruction
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GoodModelTwo_p0
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false




/-!
# The special-fibre Čech obstruction at the N13 base divisor

Put `t = 1/x` and `v = y/x³` on the infinity chart.  For the structure
sheaf, the two classes missing from the affine and infinity chart images
are represented by

`v t⁻², v t⁻¹`.

The two simple principal parts at `(0,0)` and `(1,0)` map to `(1,0)` and
`(1,1)` in this obstruction basis.  The resulting triangular matrix has
determinant one.  This is the explicit special-fibre Čech form of the
nonspeciality of the divisor `(0,0)+(1,0)`.

The polynomial identities below are the cleared-denominator transition
calculation.  They use the actual infinity-chart coefficient
`1+t²+t³`; no point enumeration or certificate table is involved.
-/

namespace MazurProof.N13SpecialCechObstruction

noncomputable section

abbrev K : Type :=
  N13GoodModelTwo.F2

/-- The numerator `v + 1 + t² + t³` occurring after changing from the
affine `y` coordinate to the infinity-chart `v` coordinate. -/
def conjugateNumerator (t v : K) : K :=
  v + (1 + t ^ 2 + t ^ 3)

/-- At `(0,0)`, removing the two negative powers leaves a polynomial
regular at infinity. -/
theorem zeroPrincipal_transition (t v : K) :
    conjugateNumerator t v =
      (v + 1) + t ^ 2 * (1 + t) := by
  simp only [conjugateNumerator]
  ring

/-- At `(1,0)`, after inverting `1+t`, the negative part has two
coefficients.  This is the exact identity behind the obstruction vector
`(1,1)`. -/
theorem onePrincipal_transition (t v : K) :
    conjugateNumerator t v =
      (1 + t) ^ 2 * (v + 1) +
        t ^ 2 * (v + t) := by
  have htwo : (2 : K) = 0 :=
    CharP.cast_eq_zero K 2
  simp only [conjugateNumerator]
  linear_combination
    -(t * (v + 1) + t ^ 2 * v) * htwo

/-- Coefficients of the two missing Čech classes
`v t⁻², v t⁻¹`. -/
abbrev Obstruction : Type :=
  Fin 2 → K

/-- Coefficients of the simple principal parts at `(0,0)` and `(1,0)`. -/
abbrev PrincipalParts : Type :=
  Fin 2 → K

/-- The special-fibre connecting map in the bases fixed above.  The first
principal part contributes only `v t⁻²`; the second contributes both
missing classes. -/
def connectingMap :
    PrincipalParts →ₗ[K] Obstruction where
  toFun a := ![a 0 + a 1, a 1]
  map_add' a b := by
    funext i
    fin_cases i <;> simp [add_assoc, add_left_comm, add_comm]
  map_smul' c a := by
    funext i
    fin_cases i <;> simp [mul_add]

/-- Matrix of the special connecting map. -/
def connectingMatrix : Matrix (Fin 2) (Fin 2) K :=
  !![1, 1; 0, 1]

@[simp] theorem connectingMatrix_det :
    connectingMatrix.det = 1 := by
  rw [Matrix.det_fin_two]
  simp [connectingMatrix]

theorem connectingMatrix_det_isUnit :
    IsUnit connectingMatrix.det := by
  rw [connectingMatrix_det]
  exact isUnit_one

/-- The two principal parts kill the full two-dimensional Čech
obstruction space. -/
def connectingEquiv :
    PrincipalParts ≃ₗ[K] Obstruction where
  toFun := connectingMap
  invFun b := ![b 0 - b 1, b 1]
  left_inv a := by
    funext i
    fin_cases i <;> simp [connectingMap]
  right_inv b := by
    funext i
    fin_cases i <;> simp [connectingMap]
  map_add' := connectingMap.map_add
  map_smul' := connectingMap.map_smul

theorem connectingMap_surjective :
    Function.Surjective connectingMap :=
  connectingEquiv.surjective

theorem connectingMap_range_eq_top :
    LinearMap.range connectingMap = ⊤ :=
  LinearMap.range_eq_top.mpr connectingMap_surjective

@[simp] theorem connectingMap_zeroPrincipal :
    connectingMap ![(1 : K), 0] = ![(1 : K), 0] := by
  ext i
  fin_cases i <;> simp [connectingMap]

@[simp] theorem connectingMap_onePrincipal :
    connectingMap ![0, (1 : K)] = ![(1 : K), 1] := by
  ext i
  fin_cases i <;> simp [connectingMap]

/-! ## The two-chart Laurent obstruction -/

open LaurentPolynomial
open scoped LaurentPolynomial

/-- Laurent coefficients in the infinity parameter `t`. -/
abbrev Laurent : Type :=
  LaurentPolynomial K

local instance instCoeFunLaurentForallIntK : CoeFun Laurent (fun _ => ℤ → K) where
  coe f := f.coeff

/-- An overlap function is written in the basis `1,v`.  The curve equation
is irrelevant for this additive Čech calculation. -/
abbrev Overlap : Type :=
  Laurent × Laurent

/-- Keep the Laurent terms of exponent at most `c`. -/
def lowerPart (c : ℤ) :
    Laurent →ₗ[K] Laurent where
  toFun f := AddMonoidAlgebra.ofCoeff (f.coeff.filter fun n => n ≤ c)
  map_add' f g := by
    ext n
    by_cases hn : n ≤ c <;>
      simp [hn]
  map_smul' a f := by
    ext n
    by_cases hn : n ≤ c <;>
      simp [hn]

@[simp] theorem lowerPart_apply_of_le
    (c n : ℤ) (f : Laurent) (hn : n ≤ c) :
    lowerPart c f n = f n := by
  simp [lowerPart, hn]

@[simp] theorem lowerPart_apply_of_lt
    (c n : ℤ) (f : Laurent) (hn : c < n) :
    lowerPart c f n = 0 := by
  have hnot : ¬n ≤ c := by omega
  simp [lowerPart, hnot]

/-- Image of the affine chart in Laurent coordinates.  Polynomial functions
in `x=t⁻¹` have scalar exponents at most zero; their `y=t⁻³v`
coefficients have exponents at most `-3`. -/
def affineSections : Submodule K Overlap where
  carrier z :=
    (∀ n : ℤ, 0 < n → z.1 n = 0) ∧
      (∀ n : ℤ, -3 < n → z.2 n = 0)
  zero_mem' :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  add_mem' := by
    rintro a b ha hb
    constructor
    · intro n hn
      simp [ha.1 n hn, hb.1 n hn]
    · intro n hn
      simp [ha.2 n hn, hb.2 n hn]
  smul_mem' := by
    intro c z hz
    constructor
    · intro n hn
      simp [hz.1 n hn]
    · intro n hn
      simp [hz.2 n hn]

/-- Image of the infinity chart in Laurent coordinates. -/
def infinitySections : Submodule K Overlap where
  carrier z :=
    (∀ n : ℤ, n < 0 → z.1 n = 0) ∧
      (∀ n : ℤ, n < 0 → z.2 n = 0)
  zero_mem' :=
    ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  add_mem' := by
    rintro a b ha hb
    constructor
    · intro n hn
      simp [ha.1 n hn, hb.1 n hn]
    · intro n hn
      simp [ha.2 n hn, hb.2 n hn]
  smul_mem' := by
    intro c z hz
    constructor
    · intro n hn
      simp [hz.1 n hn]
    · intro n hn
      simp [hz.2 n hn]

/-- The two Laurent coefficients not supplied by either affine chart. -/
def obstruction :
    Overlap →ₗ[K] Obstruction where
  toFun z := ![z.2 (-2), z.2 (-1)]
  map_add' z w := by
    funext i
    fin_cases i <;> simp
  map_smul' c z := by
    funext i
    fin_cases i <;> simp

@[simp] theorem obstruction_apply_zero (z : Overlap) :
    obstruction z 0 = z.2 (-2) := rfl

@[simp] theorem obstruction_apply_one (z : Overlap) :
    obstruction z 1 = z.2 (-1) := rfl

theorem affineSections_le_ker :
    affineSections ≤ LinearMap.ker obstruction := by
  intro z hz
  rw [LinearMap.mem_ker]
  funext i
  fin_cases i
  · simpa using hz.2 (-2) (by norm_num)
  · simpa using hz.2 (-1) (by norm_num)

theorem infinitySections_le_ker :
    infinitySections ≤ LinearMap.ker obstruction := by
  intro z hz
  rw [LinearMap.mem_ker]
  funext i
  fin_cases i
  · simpa using hz.2 (-2) (by norm_num)
  · simpa using hz.2 (-1) (by norm_num)

/-- Every Laurent overlap function splits into the two chart images once
the two obstruction coefficients vanish. -/
theorem ker_obstruction :
    LinearMap.ker obstruction =
      affineSections ⊔ infinitySections := by
  apply le_antisymm
  · intro z hz
    have hobs : obstruction z = 0 :=
      LinearMap.mem_ker.mp hz
    have hm2 : z.2 (-2) = 0 := by
      simpa using congrFun hobs 0
    have hm1 : z.2 (-1) = 0 := by
      simpa using congrFun hobs 1
    let a : Overlap :=
      (lowerPart 0 z.1, lowerPart (-3) z.2)
    have ha : a ∈ affineSections := by
      constructor
      · intro n hn
        exact lowerPart_apply_of_lt 0 n z.1 hn
      · intro n hn
        exact lowerPart_apply_of_lt (-3) n z.2 hn
    have hi : z - a ∈ infinitySections := by
      constructor
      · intro n hn
        change z.1 n - lowerPart 0 z.1 n = 0
        rw [lowerPart_apply_of_le 0 n z.1 hn.le, sub_self]
      · intro n hn
        by_cases hn3 : n ≤ -3
        · change z.2 n - lowerPart (-3) z.2 n = 0
          rw [lowerPart_apply_of_le (-3) n z.2 hn3, sub_self]
        · have hcases : n = -2 ∨ n = -1 := by omega
          rcases hcases with rfl | rfl
          · change z.2 (-2) - lowerPart (-3) z.2 (-2) = 0
            rw [lowerPart_apply_of_lt (-3) (-2) z.2 (by norm_num),
              hm2, sub_zero]
          · change z.2 (-1) - lowerPart (-3) z.2 (-1) = 0
            rw [lowerPart_apply_of_lt (-3) (-1) z.2 (by norm_num),
              hm1, sub_zero]
    have hsum : a + (z - a) = z := by
      abel
    rw [← hsum]
    exact Submodule.add_mem_sup ha hi
  · exact sup_le affineSections_le_ker infinitySections_le_ker

/-- The obstruction map is onto: the two missing Laurent monomials provide
canonical representatives. -/
def obstructionRepresentative (b : Obstruction) : Laurent :=
  AddMonoidAlgebra.single (-2) (b 0) +
    AddMonoidAlgebra.single (-1) (b 1)

@[simp] theorem obstructionRepresentative_apply_negTwo
    (b : Obstruction) :
    obstructionRepresentative b (-2) = b 0 := by
  simp only [obstructionRepresentative, AddMonoidAlgebra.coeff_add,
    ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  norm_num

@[simp] theorem obstructionRepresentative_apply_negOne
    (b : Obstruction) :
    obstructionRepresentative b (-1) = b 1 := by
  simp only [obstructionRepresentative, AddMonoidAlgebra.coeff_add,
    ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  norm_num

/-- Canonical Laurent representatives of the principal-part obstruction
classes computed by the two transition identities. -/
def principalOverlap (a : PrincipalParts) : Overlap :=
  (0, obstructionRepresentative (connectingMap a))

@[simp] theorem obstruction_principalOverlap
    (a : PrincipalParts) :
    obstruction (principalOverlap a) = connectingMap a := by
  funext i
  fin_cases i <;> simp [principalOverlap, obstruction]

theorem obstruction_surjective :
    Function.Surjective obstruction := by
  intro b
  refine ⟨(0, obstructionRepresentative b), ?_⟩
  funext i
  fin_cases i <;> simp [obstruction]

theorem obstruction_range_eq_top :
    LinearMap.range obstruction = ⊤ :=
  LinearMap.range_eq_top.mpr obstruction_surjective

/-- First cohomology of the two-chart additive Čech complex. -/
abbrev StructureCechH1 : Type :=
  Overlap ⧸ (affineSections ⊔ infinitySections)

/-- The two missing Laurent coefficients give the complete special-fibre
Čech obstruction, not merely a pair of necessary conditions. -/
noncomputable def structureCechH1Equiv :
    StructureCechH1 ≃ₗ[K] Obstruction :=
  (Submodule.quotEquivOfEq
      (affineSections ⊔ infinitySections)
      (LinearMap.ker obstruction)
      ker_obstruction.symm).trans
    (obstruction.quotKerEquivOfSurjective
      obstruction_surjective)

theorem structureCechH1_finrank :
    Module.finrank K StructureCechH1 = 2 := by
  rw [structureCechH1Equiv.finrank_eq]
  simp

/-- The two principal parts map to the actual structure-sheaf Čech
cohomology through their computed obstruction vectors. -/
def principalToStructureCechH1 :
    PrincipalParts →ₗ[K] StructureCechH1 :=
  structureCechH1Equiv.symm.toLinearMap.comp connectingMap

/-- Nonspeciality in its exact Čech form: the principal parts of the base
divisor give all of `H¹(O)`. -/
def principalToStructureCechH1Equiv :
    PrincipalParts ≃ₗ[K] StructureCechH1 :=
  connectingEquiv.trans structureCechH1Equiv.symm

theorem principalToStructureCechH1_surjective :
    Function.Surjective principalToStructureCechH1 :=
  principalToStructureCechH1Equiv.surjective

theorem principalToStructureCechH1_range_eq_top :
    LinearMap.range principalToStructureCechH1 = ⊤ :=
  LinearMap.range_eq_top.mpr
    principalToStructureCechH1_surjective

/-- The additive Čech `H¹` after twisting by the nonspecial degree-two
base divisor: it is the cokernel of the principal-part connecting map. -/
abbrev TwistedCechH1 : Type :=
  StructureCechH1 ⧸
    LinearMap.range principalToStructureCechH1

noncomputable instance twistedCechH1_subsingleton :
    Subsingleton TwistedCechH1 := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  exact principalToStructureCechH1_range_eq_top

theorem twistedCechH1_eq_zero
    (z : TwistedCechH1) :
    z = 0 :=
  Subsingleton.elim _ _

end

end MazurProof.N13SpecialCechObstruction


