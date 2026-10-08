-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CechLaurentCore_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13CechLaurentCore_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:30:21.935218+00:00
-- url     : https://prove2.me/theorems/d76f0604-d9c5-46f9-aa9c-fb1b89c97bbe
-- title:
--   FLT.Assumptions.MazurProof.N13CechLaurentCore source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13CechLaurentCore

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CechLaurentCore
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false




/-!
# The two-chart Laurent Čech core

For a generalized hyperelliptic equation of degree six, write an overlap
function in the infinity coordinates as `a(t) + b(t)v`.  The affine chart
contributes scalar Laurent exponents at most zero and `v`-exponents at most
`-3`; the infinity chart contributes nonnegative exponents.  Their additive
Čech quotient is therefore represented exactly by the two coefficients

`b₋₂, b₋₁`.

This calculation is valid over every commutative coefficient ring.  Keeping
it ring-generic lets the N13 special fibre and its integral two-adic lift use
the same decomposition theorem.
-/

namespace MazurProof.N13CechLaurentCore

noncomputable section

open LaurentPolynomial
open scoped LaurentPolynomial

universe u

variable {R : Type u} [CommRing R]

/-- Laurent coefficients in the infinity parameter. -/
abbrev Laurent : Type u :=
  LaurentPolynomial R

local instance instCoeFunLaurentForallInt : CoeFun (Laurent (R := R)) (fun _ => ℤ → R) where
  coe f := f.coeff

/-- An overlap function in the basis `1,v`. -/
abbrev Overlap : Type u :=
  Laurent (R := R) × Laurent (R := R)

/-- The two missing Laurent coefficients. -/
abbrev Obstruction : Type u :=
  Fin 2 → R

/-- Keep the Laurent terms of exponent at most `c`. -/
def lowerPart (c : ℤ) :
    Laurent (R := R) →ₗ[R] Laurent (R := R) where
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
    (c n : ℤ) (f : Laurent (R := R)) (hn : n ≤ c) :
    lowerPart c f n = f n := by
  simp [lowerPart, hn]

@[simp] theorem lowerPart_apply_of_lt
    (c n : ℤ) (f : Laurent (R := R)) (hn : c < n) :
    lowerPart c f n = 0 := by
  have hnot : ¬n ≤ c := by omega
  simp [lowerPart, hnot]

/-- Image of the affine chart in Laurent coordinates. -/
def affineSections : Submodule R (Overlap (R := R)) where
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
def infinitySections : Submodule R (Overlap (R := R)) where
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

/-- Read the coefficients of `v t⁻²` and `v t⁻¹`. -/
def obstruction :
    Overlap (R := R) →ₗ[R] Obstruction (R := R) where
  toFun z := ![z.2 (-2), z.2 (-1)]
  map_add' z w := by
    funext i
    fin_cases i <;> simp
  map_smul' c z := by
    funext i
    fin_cases i <;> simp

@[simp] theorem obstruction_apply_zero
    (z : Overlap (R := R)) :
    obstruction z 0 = z.2 (-2) := rfl

@[simp] theorem obstruction_apply_one
    (z : Overlap (R := R)) :
    obstruction z 1 = z.2 (-1) := rfl

theorem affineSections_le_ker :
    affineSections (R := R) ≤
      LinearMap.ker (obstruction (R := R)) := by
  intro z hz
  rw [LinearMap.mem_ker]
  funext i
  fin_cases i
  · simpa using hz.2 (-2) (by norm_num)
  · simpa using hz.2 (-1) (by norm_num)

theorem infinitySections_le_ker :
    infinitySections (R := R) ≤
      LinearMap.ker (obstruction (R := R)) := by
  intro z hz
  rw [LinearMap.mem_ker]
  funext i
  fin_cases i
  · simpa using hz.2 (-2) (by norm_num)
  · simpa using hz.2 (-1) (by norm_num)

/-- Vanishing of the two missing coefficients is sufficient for a
two-chart decomposition. -/
theorem ker_obstruction :
    LinearMap.ker (obstruction (R := R)) =
      affineSections (R := R) ⊔
        infinitySections (R := R) := by
  apply le_antisymm
  · intro z hz
    have hobs : obstruction z = 0 :=
      LinearMap.mem_ker.mp hz
    have hm2 : z.2 (-2) = 0 := by
      simpa using congrFun hobs 0
    have hm1 : z.2 (-1) = 0 := by
      simpa using congrFun hobs 1
    let a : Overlap (R := R) :=
      (lowerPart 0 z.1, lowerPart (-3) z.2)
    have ha : a ∈ affineSections (R := R) := by
      constructor
      · intro n hn
        exact lowerPart_apply_of_lt 0 n z.1 hn
      · intro n hn
        exact lowerPart_apply_of_lt (-3) n z.2 hn
    have hi : z - a ∈ infinitySections (R := R) := by
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
  · exact
      sup_le affineSections_le_ker
        infinitySections_le_ker

/-- Canonical representatives of the two obstruction coefficients. -/
def obstructionRepresentative
    (b : Obstruction (R := R)) :
    Laurent (R := R) :=
  AddMonoidAlgebra.single (-2) (b 0) +
    AddMonoidAlgebra.single (-1) (b 1)

@[simp] theorem obstructionRepresentative_apply_negTwo
    (b : Obstruction (R := R)) :
    obstructionRepresentative b (-2) = b 0 := by
  simp only [obstructionRepresentative, AddMonoidAlgebra.coeff_add,
    ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  norm_num

@[simp] theorem obstructionRepresentative_apply_negOne
    (b : Obstruction (R := R)) :
    obstructionRepresentative b (-1) = b 1 := by
  simp only [obstructionRepresentative, AddMonoidAlgebra.coeff_add,
    ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  norm_num

theorem obstruction_surjective :
    Function.Surjective (obstruction (R := R)) := by
  intro b
  refine
    ⟨(0, obstructionRepresentative b), ?_⟩
  funext i
  fin_cases i <;> simp [obstruction]

theorem obstruction_range_eq_top :
    LinearMap.range (obstruction (R := R)) = ⊤ :=
  LinearMap.range_eq_top.mpr obstruction_surjective

/-- First cohomology of the additive two-chart Laurent complex. -/
abbrev StructureCechH1 : Type u :=
  Overlap (R := R) ⧸
    (affineSections (R := R) ⊔
      infinitySections (R := R))

/-- The Laurent Čech quotient is canonically the rank-two obstruction
module. -/
noncomputable def structureCechH1Equiv :
    StructureCechH1 (R := R) ≃ₗ[R]
      Obstruction (R := R) :=
  (Submodule.quotEquivOfEq
      (affineSections (R := R) ⊔
        infinitySections (R := R))
      (LinearMap.ker (obstruction (R := R)))
      ker_obstruction.symm).trans
    ((obstruction (R := R)).quotKerEquivOfSurjective
      obstruction_surjective)

section Field

variable {F : Type u} [Field F]

theorem structureCechH1_finrank :
    Module.finrank F (StructureCechH1 (R := F)) = 2 := by
  rw [(structureCechH1Equiv (R := F)).finrank_eq]
  simp

end Field

end

end MazurProof.N13CechLaurentCore


