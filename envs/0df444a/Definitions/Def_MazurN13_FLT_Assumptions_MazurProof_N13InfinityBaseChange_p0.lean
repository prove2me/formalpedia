-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityBaseChange_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13InfinityBaseChange_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:26:46.59301+00:00
-- url     : https://prove2.me/theorems/c25dca59-55be-4359-b824-387e14a91330
-- title:
--   FLT.Assumptions.MazurProof.N13InfinityBaseChange source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13InfinityBaseChange

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13InfinityBaseChange
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13BranchNorm_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SmallMumfordRigidity_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordOrientedBaseChange_p0
import Mathlib.NumberTheory.Padics.PadicIntegers

set_option autoImplicit false




/-!
# Base change at the positive infinity of the N13 sextic

Coefficient extension commutes with the chosen positive Laurent branch of
the N13 function field.  The only apparent issue is the formal square root
used to define that branch.  We avoid coefficient calculations: after base
change the two candidate square roots have the same square and constant
coefficient `1`, so the factorization of a difference of squares excludes
the negative root.

For an injective coefficient map, coefficientwise extension of Laurent
series also preserves the support, hence its integer order.  Together these
facts give compatibility of the oriented infinity order and the induced
base-change map on concrete Picard groups.
-/

open Polynomial
open scoped LaurentSeries

namespace MazurProof.N13InfinityBaseChange

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u v

variable {K : Type u} {K' : Type v}
variable [Field K] [Field K'] [CharZero K] [CharZero K']

/-- Coefficientwise extension of Laurent series as a bundled ring map. -/
def laurentMap (ι : K →+* K') :
    LaurentSeries K →+* LaurentSeries K' where
  toFun z := z.map ι
  map_zero' := HahnSeries.map_zero ι.toZeroHom
  map_one' := HahnSeries.map_one ι.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add ι.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul ι.toNonUnitalRingHom

omit [CharZero K] [CharZero K'] in
@[simp] theorem laurentMap_coeff
    (ι : K →+* K') (z : LaurentSeries K) (n : ℤ) :
    (laurentMap ι z).coeff n = ι (z.coeff n) := rfl

omit [CharZero K] [CharZero K'] in
theorem laurentMap_injective
    (ι : K →+* K') (hι : Function.Injective ι) :
    Function.Injective (laurentMap ι) := by
  intro z w h
  apply HahnSeries.coeff_injective
  funext n
  apply hι
  simpa only [laurentMap_coeff] using
    congrArg (fun q : LaurentSeries K' => q.coeff n) h

omit [CharZero K] [CharZero K'] in
theorem laurentMap_order
    (ι : K →+* K') (hι : Function.Injective ι)
    (z : LaurentSeries K) :
    (laurentMap ι z).order = z.order := by
  by_cases hz : z = 0
  · simp [hz]
  have hmz : laurentMap ι z ≠ 0 := by
    simpa using (laurentMap_injective ι hι).ne hz
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    rw [laurentMap_coeff]
    simpa using
      hι.ne (HahnSeries.coeff_order_eq_zero.not.mpr hz)
  · apply HahnSeries.order_le_of_coeff_ne_zero
    intro hzero
    have :
        (laurentMap ι z).coeff (laurentMap ι z).order = 0 := by
      rw [laurentMap_coeff, hzero, map_zero]
    exact (HahnSeries.coeff_order_eq_zero.not.mpr hmz) this

omit [CharZero K] [CharZero K'] in
@[simp] theorem laurentMap_parameter
    (ι : K →+* K') :
    laurentMap ι (N13Infinity.parameter K) =
      N13Infinity.parameter K' := by
  change
    ((HahnSeries.single (1 : ℤ) (1 : K)).map ι :
      LaurentSeries K') =
        HahnSeries.single (1 : ℤ) (1 : K')
  calc
    ((HahnSeries.single (1 : ℤ) (1 : K)).map ι :
        LaurentSeries K') =
        HahnSeries.single (1 : ℤ) (ι 1) :=
      HahnSeries.map_single (a := (1 : ℤ)) (r := (1 : K))
        ι.toZeroHom
    _ = HahnSeries.single (1 : ℤ) (1 : K') := by rw [map_one]

omit [CharZero K] [CharZero K'] in
@[simp] theorem laurentMap_algebraMap
    (ι : K →+* K') (a : K) :
    laurentMap ι (algebraMap K (LaurentSeries K) a) =
      algebraMap K' (LaurentSeries K') (ι a) := by
  rw [HahnSeries.algebraMap_apply',
    HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply,
    PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_C]
  exact HahnSeries.map_single (a := (0 : ℤ)) (r := a)
    ι.toZeroHom

/-- The positive square root is natural under coefficient extension.

The proof uses its defining square and constant coefficient, rather than
expanding the binomial series coefficient by coefficient. -/
theorem laurentMap_wSeries
    (ι : K →+* K') :
    laurentMap ι (N13Infinity.wSeries K) =
      N13Infinity.wSeries K' := by
  let a : LaurentSeries K' :=
    laurentMap ι (N13Infinity.wSeries K)
  let b : LaurentSeries K' :=
    N13Infinity.wSeries K'
  have hab_sq : a ^ 2 = b ^ 2 := by
    dsimp only [a, b]
    rw [← map_pow, N13Infinity.wSeries_sq,
      N13Infinity.wSeries_sq]
    simp only [map_add, map_mul, map_pow, map_one, map_ofNat,
      laurentMap_parameter]
  have hab_add_ne : a + b ≠ 0 := by
    intro hab
    have hcoeff := congrArg
      (fun z : LaurentSeries K' => z.coeff (0 : ℤ)) hab
    have ha_coeff :
        a.coeff (0 : ℤ) = 1 := by
      dsimp only [a]
      rw [laurentMap_coeff]
      unfold N13Infinity.wSeries
      rw [show (0 : ℤ) = (0 : ℕ) by rfl,
        HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_zero_eq_constantCoeff]
      rw [N13Infinity.sqrtReverseF_constantCoeff]
      exact map_one ι
    have hb_coeff :
        b.coeff (0 : ℤ) = 1 := by
      dsimp only [b]
      unfold N13Infinity.wSeries
      rw [show (0 : ℤ) = (0 : ℕ) by rfl,
        HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_zero_eq_constantCoeff]
      exact N13Infinity.sqrtReverseF_constantCoeff K'
    rw [HahnSeries.coeff_add, ha_coeff, hb_coeff,
      HahnSeries.coeff_zero] at hcoeff
    norm_num at hcoeff
  have hfactor : (a - b) * (a + b) = 0 := by
    calc
      (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hab_sq
  rcases mul_eq_zero.mp hfactor with hdiff | hsum
  · exact sub_eq_zero.mp hdiff
  · exact (hab_add_ne hsum).elim

@[simp] theorem laurentMap_ySeries
    (ι : K →+* K') :
    laurentMap ι (N13Infinity.ySeries K) =
      N13Infinity.ySeries K' := by
  simp [N13Infinity.ySeries, N13InfinityBaseChange.laurentMap_wSeries]

omit [CharZero K] [CharZero K'] in
@[simp] theorem map_n13_f
    (ι : K →+* K') :
    (N13Mumford.f K).map ι = N13Mumford.f K' := by
  simp [N13Mumford.f]

omit [CharZero K] [CharZero K'] in
private theorem eval_at_infinity_map
    (ι : K →+* K') (p : K[X]) :
    laurentMap ι
        (p.eval₂ (algebraMap K (LaurentSeries K))
          ((N13Infinity.parameter K)⁻¹)) =
      (p.map ι).eval₂ (algebraMap K' (LaurentSeries K'))
        ((N13Infinity.parameter K')⁻¹) := by
  have hcoeff :
      (laurentMap ι).comp
          (algebraMap K (LaurentSeries K)) =
        (algebraMap K' (LaurentSeries K')).comp ι := by
    apply RingHom.ext
    intro a
    exact laurentMap_algebraMap ι a
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map,
    hcoeff, map_inv₀, laurentMap_parameter]

/-- The affine positive-branch embedding commutes with N13 coefficient
extension. -/
theorem coordinateToLaurent_coordinateMap
    (ι : K →+* K') (z : N13Mumford.CoordinateRing K) :
    laurentMap ι (N13Infinity.coordinateToLaurent K z) =
      N13Infinity.coordinateToLaurent K'
        (SexticMumford.OrientedBaseChange.coordinateMap
          ι (map_n13_f ι) z) := by
  rw [← SexticMumford.recompose (N13Mumford.model K) z]
  simp only [map_add, map_mul,
    SexticMumford.OrientedBaseChange.coordinateMap_xClass,
    SexticMumford.OrientedBaseChange.coordinateMap_yClass,
    N13Infinity.coordinateToLaurent_xClass,
    N13BranchNorm.coordinateToLaurent_yClass]
  simp_rw [eval_at_infinity_map]
  rw [laurentMap_ySeries]

/-- The function-field positive-branch embedding commutes with coefficient
extension. -/
theorem functionFieldToLaurent_functionMap
    (ι : K →+* K') (hι : Function.Injective ι)
    (z : N13Mumford.FunctionField K) :
    laurentMap ι (N13Infinity.functionFieldToLaurent K z) =
      N13Infinity.functionFieldToLaurent K'
        (SexticMumford.OrientedBaseChange.functionMap
          ι hι (map_n13_f ι) z) := by
  let lhs : N13Mumford.FunctionField K →+* LaurentSeries K' :=
    (laurentMap ι).comp
      (N13Infinity.functionFieldToLaurent K)
  let rhs : N13Mumford.FunctionField K →+* LaurentSeries K' :=
    (N13Infinity.functionFieldToLaurent K').comp
      (SexticMumford.OrientedBaseChange.functionMap
        ι hι (map_n13_f ι))
  have hhom : lhs = rhs := by
    apply IsFractionRing.ringHom_ext
      (A := N13Mumford.CoordinateRing K)
    intro w
    dsimp only [lhs, rhs, RingHom.comp_apply]
    rw [N13Infinity.functionFieldToLaurent_algebraMap,
      SexticMumford.OrientedBaseChange.functionMap_algebraMap,
      N13Infinity.functionFieldToLaurent_algebraMap,
      coordinateToLaurent_coordinateMap]
  change lhs z = rhs z
  rw [hhom]

/-- Every injective characteristic-zero coefficient extension preserves the
chosen positive infinity order on the N13 sextic. -/
theorem infinityCompatible
    (ι : K →+* K') (hι : Function.Injective ι) :
    SexticMumford.OrientedBaseChange.InfinityCompatible
      ι hι (map_n13_f ι)
      (N13Infinity.positiveInfinityOrder K)
      (N13Infinity.positiveInfinityOrder K') := by
  intro α
  change Multiplicative.ofAdd
      ((N13Infinity.functionFieldToLaurent K'
        (SexticMumford.OrientedBaseChange.functionMap
          ι hι (map_n13_f ι) (α : N13Mumford.FunctionField K))).order) =
    Multiplicative.ofAdd
      ((N13Infinity.functionFieldToLaurent K
        (α : N13Mumford.FunctionField K)).order)
  rw [← functionFieldToLaurent_functionMap ι hι,
    laurentMap_order ι hι]

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev Q₂ : Type := ℚ_[2]

def ratToQ₂ : ℚ →+* Q₂ := algebraMap ℚ Q₂

theorem ratToQ₂_injective : Function.Injective ratToQ₂ :=
  (ratToQ₂).injective

/-- The concrete oriented Picard base-change map from the rational N13
function field to its two-adic coefficient extension. -/
def picMapRatToQ₂ :
    SexticMumford.ConcretePic
        (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ) →+
      SexticMumford.ConcretePic
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂) :=
  SexticMumford.OrientedBaseChange.picMap
    ratToQ₂ ratToQ₂_injective (map_n13_f ratToQ₂)
    (N13Infinity.positiveInfinityOrder ℚ)
    (N13Infinity.positiveInfinityOrder Q₂)
    (infinityCompatible ratToQ₂ ratToQ₂_injective)

@[simp] theorem picMapRatToQ₂_classOf
    (D : N13Mumford.Mumford ℚ) :
    picMapRatToQ₂
        (SexticMumford.classOf
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) D) =
      SexticMumford.classOf
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (D.mapCoeffs ratToQ₂ ratToQ₂_injective
          (map_n13_f ratToQ₂)) := by
  exact SexticMumford.OrientedBaseChange.picMap_classOf
    ratToQ₂ ratToQ₂_injective (map_n13_f ratToQ₂)
    (N13Infinity.positiveInfinityOrder ℚ)
    (N13Infinity.positiveInfinityOrder Q₂)
    (infinityCompatible ratToQ₂ ratToQ₂_injective) D

/-- Canonical balanced representatives commute with rational-to-two-adic
base change. -/
@[simp] theorem normalize_picMapRatToQ₂
    (c :
      SexticMumford.ConcretePic
        (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ)) :
    SexticMumford.normalize
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (picMapRatToQ₂ c) =
      (SexticMumford.normalize
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) c).mapCoeffs
        ratToQ₂ ratToQ₂_injective
        (map_n13_f ratToQ₂) := by
  apply SexticMumford.normalize_eq_of_class
  calc
    SexticMumford.classOf
          (N13Mumford.model Q₂)
          (N13Infinity.positiveInfinityOrder Q₂)
          ((SexticMumford.normalize
              (N13Mumford.model ℚ)
              (N13Infinity.positiveInfinityOrder ℚ) c).mapCoeffs
            ratToQ₂ ratToQ₂_injective
            (map_n13_f ratToQ₂)) =
        picMapRatToQ₂
          (SexticMumford.classOf
            (N13Mumford.model ℚ)
            (N13Infinity.positiveInfinityOrder ℚ)
            (SexticMumford.normalize
              (N13Mumford.model ℚ)
              (N13Infinity.positiveInfinityOrder ℚ) c)) := by
      rw [picMapRatToQ₂_classOf]
    _ = picMapRatToQ₂ c := by
      rw [SexticMumford.classOf_normalize]

/-- Rational oriented Picard classes remain distinct after extension to
`ℚ₂`.  The proof uses unique balanced normal forms, not a Picard-scheme
separatedness theorem. -/
theorem picMapRatToQ₂_injective :
    Function.Injective picMapRatToQ₂ := by
  intro c d hcd
  have hnormal :
      ((SexticMumford.normalize
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) c).mapCoeffs
            ratToQ₂ ratToQ₂_injective
            (map_n13_f ratToQ₂) :
          N13Mumford.Mumford Q₂) =
        ((SexticMumford.normalize
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) d).mapCoeffs
            ratToQ₂ ratToQ₂_injective
            (map_n13_f ratToQ₂) :
          N13Mumford.Mumford Q₂) := by
    rw [← normalize_picMapRatToQ₂,
      ← normalize_picMapRatToQ₂, hcd]
  have hsource :
      SexticMumford.normalize
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) c =
        SexticMumford.normalize
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ) d :=
    SexticMumford.Mumford.mapCoeffs_injective
      ratToQ₂ ratToQ₂_injective
      (map_n13_f ratToQ₂) hnormal
  calc
    c = SexticMumford.classOf
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ)
          (SexticMumford.normalize
            (N13Mumford.model ℚ)
            (N13Infinity.positiveInfinityOrder ℚ) c) :=
      (SexticMumford.classOf_normalize
        (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ) c).symm
    _ = SexticMumford.classOf
          (N13Mumford.model ℚ)
          (N13Infinity.positiveInfinityOrder ℚ)
          (SexticMumford.normalize
            (N13Mumford.model ℚ)
            (N13Infinity.positiveInfinityOrder ℚ) d) := by
      rw [hsource]
    _ = d :=
      SexticMumford.classOf_normalize
        (N13Mumford.model ℚ)
        (N13Infinity.positiveInfinityOrder ℚ) d

end

end MazurProof.N13InfinityBaseChange


