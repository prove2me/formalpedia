-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CechLaurentSeriesCore_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13CechLaurentSeriesCore_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:29:59.902999+00:00
-- url     : https://prove2.me/theorems/4a57bf08-fb7d-432d-a718-3607870d20d7
-- title:
--   FLT.Assumptions.MazurProof.N13CechLaurentSeriesCore source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13CechLaurentSeriesCore

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CechLaurentSeriesCore
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.RingTheory.LaurentSeries
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false




/-!
# The formal Laurent-series Čech core

The proper two-chart calculation at infinity uses Laurent series, not only
Laurent polynomials: a function such as `1 / (1 + t)` is regular at
`t = 0`, but has an infinite power-series tail.

Write a formal overlap function in the basis `1,v` as `a(t) + b(t)v`.
The affine chart contributes scalar exponents at most zero and
`v`-exponents at most `-3`; the formal infinity chart contributes
nonnegative exponents.  Their additive Čech quotient is therefore still
represented exactly by

`b₋₂, b₋₁`.

Unlike the finite Laurent-polynomial model, this file includes every
power-series tail and hence gives the correct formal neighbourhood used by
the proper lifting argument.
-/

namespace MazurProof.N13CechLaurentSeriesCore

noncomputable section

open HahnSeries
open scoped PowerSeries LaurentSeries

universe u

variable {R : Type u} [CommRing R]

/-- Formal Laurent series in the infinity parameter. -/
abbrev Laurent : Type u :=
  LaurentSeries R

/-- Formal power series on the infinity chart. -/
abbrev Power : Type u :=
  PowerSeries R

/-- An overlap function in the basis `1,v`. -/
abbrev Overlap : Type u :=
  Laurent (R := R) × Laurent (R := R)

/-- The two missing Laurent coefficients. -/
abbrev Obstruction : Type u :=
  Fin 2 → R

/-- Keep the Laurent-series terms of exponent at most `c`. -/
def lowerPart (c : ℤ) :
    Laurent (R := R) →ₗ[R] Laurent (R := R) where
  toFun f := HahnSeries.truncLT (c + 1) f
  map_add' f g := by
    ext n
    by_cases hn : n < c + 1 <;>
      simp [HahnSeries.coeff_truncLT, hn]
  map_smul' a f := by
    ext n
    by_cases hn : n < c + 1 <;>
      simp [HahnSeries.coeff_truncLT, hn]

@[simp] theorem lowerPart_coeff_of_le
    (c n : ℤ) (f : Laurent (R := R)) (hn : n ≤ c) :
    (lowerPart c f).coeff n = f.coeff n := by
  apply HahnSeries.coeff_truncLT_of_lt
  omega

@[simp] theorem lowerPart_coeff_of_lt
    (c n : ℤ) (f : Laurent (R := R)) (hn : c < n) :
    (lowerPart c f).coeff n = 0 := by
  apply HahnSeries.coeff_truncLT_of_le
  omega

/-- Formal restrictions of affine-chart functions. -/
def affineSections : Submodule R (Overlap (R := R)) where
  carrier z :=
    (∀ n : ℤ, 0 < n → z.1.coeff n = 0) ∧
      (∀ n : ℤ, -3 < n → z.2.coeff n = 0)
  zero_mem' :=
    ⟨fun _ _ => by simp, fun _ _ => by simp⟩
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

/-- Formal power-series restrictions from the infinity chart. -/
def infinitySections : Submodule R (Overlap (R := R)) where
  carrier z :=
    (∀ n : ℤ, n < 0 → z.1.coeff n = 0) ∧
      (∀ n : ℤ, n < 0 → z.2.coeff n = 0)
  zero_mem' :=
    ⟨fun _ _ => by simp, fun _ _ => by simp⟩
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
  toFun z := ![z.2.coeff (-2), z.2.coeff (-1)]
  map_add' z w := by
    funext i
    fin_cases i <;> simp
  map_smul' c z := by
    funext i
    fin_cases i <;> simp

@[simp] theorem obstruction_apply_zero
    (z : Overlap (R := R)) :
    obstruction z 0 = z.2.coeff (-2) := rfl

@[simp] theorem obstruction_apply_one
    (z : Overlap (R := R)) :
    obstruction z 1 = z.2.coeff (-1) := rfl

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

/-- Vanishing of the two missing coefficients is sufficient for a formal
two-chart decomposition, including arbitrary nonnegative power-series
tails. -/
theorem ker_obstruction :
    LinearMap.ker (obstruction (R := R)) =
      affineSections (R := R) ⊔
        infinitySections (R := R) := by
  apply le_antisymm
  · intro z hz
    have hobs : obstruction z = 0 :=
      LinearMap.mem_ker.mp hz
    have hm2 : z.2.coeff (-2) = 0 := by
      simpa using congrFun hobs 0
    have hm1 : z.2.coeff (-1) = 0 := by
      simpa using congrFun hobs 1
    let a : Overlap (R := R) :=
      (lowerPart 0 z.1, lowerPart (-3) z.2)
    have ha : a ∈ affineSections (R := R) := by
      constructor
      · intro n hn
        exact lowerPart_coeff_of_lt 0 n z.1 hn
      · intro n hn
        exact lowerPart_coeff_of_lt (-3) n z.2 hn
    have hi : z - a ∈ infinitySections (R := R) := by
      constructor
      · intro n hn
        change z.1.coeff n - (lowerPart 0 z.1).coeff n = 0
        rw [lowerPart_coeff_of_le 0 n z.1 hn.le, sub_self]
      · intro n hn
        by_cases hn3 : n ≤ -3
        · change z.2.coeff n - (lowerPart (-3) z.2).coeff n = 0
          rw [lowerPart_coeff_of_le (-3) n z.2 hn3, sub_self]
        · have hcases : n = -2 ∨ n = -1 := by omega
          rcases hcases with rfl | rfl
          · change
              z.2.coeff (-2) -
                (lowerPart (-3) z.2).coeff (-2) = 0
            rw [lowerPart_coeff_of_lt (-3) (-2) z.2 (by norm_num),
              hm2, sub_zero]
          · change
              z.2.coeff (-1) -
                (lowerPart (-3) z.2).coeff (-1) = 0
            rw [lowerPart_coeff_of_lt (-3) (-1) z.2 (by norm_num),
              hm1, sub_zero]
    have hsum : a + (z - a) = z := by
      abel
    rw [← hsum]
    exact Submodule.add_mem_sup ha hi
  · exact
      sup_le affineSections_le_ker
        infinitySections_le_ker

/-- Canonical formal Laurent representatives of the obstruction
coefficients. -/
def obstructionRepresentative
    (b : Obstruction (R := R)) :
    Laurent (R := R) :=
  HahnSeries.single (-2) (b 0) +
    HahnSeries.single (-1) (b 1)

@[simp] theorem obstructionRepresentative_coeff_negTwo
    (b : Obstruction (R := R)) :
    (obstructionRepresentative b).coeff (-2) = b 0 := by
  simp [obstructionRepresentative]

@[simp] theorem obstructionRepresentative_coeff_negOne
    (b : Obstruction (R := R)) :
    (obstructionRepresentative b).coeff (-1) = b 1 := by
  simp [obstructionRepresentative]

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

/-- Coercion of a formal power series to a Laurent series, as a linear
map. -/
def includePower :
    Power (R := R) →ₗ[R] Laurent (R := R) where
  toFun f := (f : Laurent (R := R))
  map_add' f g := PowerSeries.coe_add f g
  map_smul' c f := PowerSeries.coe_smul c f

theorem includePower_coeff_of_neg
    (f : Power (R := R)) (n : ℤ) (hn : n < 0) :
    (includePower f).coeff n = 0 := by
  simp [includePower, PowerSeries.coeff_coe, hn]

/-- A Laurent series with no negative coefficients is the coercion of its
power-series coefficient sequence. -/
def powerOfNonnegative
    (f : Laurent (R := R)) :
    Power (R := R) :=
  PowerSeries.mk fun n => f.coeff n

theorem includePower_powerOfNonnegative
    (f : Laurent (R := R))
    (hf : ∀ n : ℤ, n < 0 → f.coeff n = 0) :
    includePower (powerOfNonnegative f) = f := by
  ext n
  cases n with
  | ofNat n =>
      simp [includePower, powerOfNonnegative]
  | negSucc n =>
      rw [includePower_coeff_of_neg _ _ (by omega)]
      exact (hf _ (by omega)).symm

/-- Coefficientwise inclusion of a pair of formal power series. -/
def includePowerPair :
    (Power (R := R) × Power (R := R)) →ₗ[R]
      Overlap (R := R) where
  toFun f := (includePower f.1, includePower f.2)
  map_add' f g := by
    ext <;> simp
  map_smul' c f := by
    ext <;> simp

/-- The coefficient condition defining the formal infinity chart is
exactly the image of two power-series modules. -/
theorem infinitySections_eq_range :
    infinitySections (R := R) =
      LinearMap.range (includePowerPair (R := R)) := by
  apply le_antisymm
  · intro z hz
    refine
      ⟨(powerOfNonnegative z.1,
          powerOfNonnegative z.2), ?_⟩
    apply Prod.ext
    · exact includePower_powerOfNonnegative z.1 hz.1
    · exact includePower_powerOfNonnegative z.2 hz.2
  · rintro z ⟨f, rfl⟩
    constructor
    · intro n hn
      exact includePower_coeff_of_neg f.1 n hn
    · intro n hn
      exact includePower_coeff_of_neg f.2 n hn

/-- First cohomology of the formal two-chart additive complex. -/
abbrev StructureCechH1 : Type u :=
  Overlap (R := R) ⧸
    (affineSections (R := R) ⊔
      infinitySections (R := R))

/-- The formal Laurent-series Čech quotient is canonically the rank-two
obstruction module. -/
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

end MazurProof.N13CechLaurentSeriesCore


