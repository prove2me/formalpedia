-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialAffineSaturation_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialAffineSaturation_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T21:04:57.42841+00:00
-- url     : https://prove2.me/theorems/dc9b0fb5-b4af-43be-81c0-b82894d770ee
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialAffineSaturation source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialAffineSaturation

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialAffineSaturation
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityGraphSaturation_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoChartSpecialRestriction_p0

set_option autoImplicit false




/-!
# Saturated affine ideals on the special N13 overlap

The special affine and infinity charts meet on the principal open where
`x` is invertible.  If `x` is already a unit modulo an affine ideal, then
localizing at `x` loses no information: the original ideal is the contraction
of its extension to the overlap.

This gives a useful uniqueness principle for special divisors.  Two compatible
chart pairs with the same infinity ideal and `x`-saturated affine ideals have
the same affine ideal, so the infinity calculation alone determines the whole
pair.
-/

namespace MazurProof.N13SpecialAffineSaturation

noncomputable section

/-- The special affine coordinate ring. -/
abbrev AffineCurve :=
  N13SpecialCurveOverlap.AffineCurve

/-- The special infinity coordinate ring. -/
abbrev InfinityCurve :=
  N13SpecialCurveOverlap.CoordinateRing

/-- The special affine-to-infinity overlap ring. -/
abbrev InfinityOverlap :=
  N13SpecialCurveOverlap.InfinityOverlap

/-- The affine coordinate is a unit in the quotient by `I`.  This is the
ideal-theoretic form of saying that the closed subscheme cut out by `I`
does not acquire support on the omitted divisor `x=0`. -/
def XUnitMod (I : Ideal AffineCurve) : Prop :=
  ∃ q : AffineCurve,
    1 - q * N13SpecialCurveOverlap.xClass ∈ I

/-- The unit ideal trivially makes the affine coordinate invertible in the
quotient. -/
theorem top_xUnitMod :
    XUnitMod (⊤ : Ideal AffineCurve) := by
  exact ⟨0, by simp⟩

/-- If the affine coordinate is invertible modulo each of two ideals, it is
also invertible modulo their product.  The inverse witness is obtained by
multiplying the two Bézout relations. -/
theorem mul_xUnitMod
    {I J : Ideal AffineCurve}
    (hI : XUnitMod I)
    (hJ : XUnitMod J) :
    XUnitMod (I * J) := by
  obtain ⟨q, hq⟩ := hI
  obtain ⟨r, hr⟩ := hJ
  refine
    ⟨q + r - q * r * N13SpecialCurveOverlap.xClass, ?_⟩
  have hprod := Ideal.mul_mem_mul hq hr
  convert hprod using 1
  ring

/-- Multiplication by `x` can be cancelled modulo an ideal in which `x`
is already a unit. -/
theorem mem_of_x_mul_mem
    {I : Ideal AffineCurve}
    (hx : XUnitMod I)
    {z : AffineCurve}
    (hz : N13SpecialCurveOverlap.xClass * z ∈ I) :
    z ∈ I := by
  obtain ⟨q, hq⟩ := hx
  have h₁ := Ideal.mul_mem_left I z hq
  have h₂ := Ideal.mul_mem_left I q hz
  have hsum := Ideal.add_mem I h₁ h₂
  convert hsum using 1
  all_goals ring

/-- Every power of `x` can be cancelled modulo an ideal in which `x`
is already a unit. -/
theorem mem_of_x_pow_mul_mem
    {I : Ideal AffineCurve}
    (hx : XUnitMod I)
    (n : ℕ)
    {z : AffineCurve}
    (hz : N13SpecialCurveOverlap.xClass ^ n * z ∈ I) :
    z ∈ I := by
  induction n with
  | zero =>
      simpa using hz
  | succ n ih =>
      apply ih
      apply mem_of_x_mul_mem hx
      convert hz using 1
      all_goals simp only [pow_succ]
      all_goals ring

/-- Localizing a special affine ideal at `x` and contracting it back returns
the original ideal whenever `x` is a unit modulo that ideal. -/
theorem comap_map_affineOverlap_eq_of_xUnitMod
    {I : Ideal AffineCurve}
    (hx : XUnitMod I) :
    Ideal.comap
        (algebraMap AffineCurve
          N13SpecialCurveOverlap.AffineOverlap)
        (Ideal.map
          (algebraMap AffineCurve
            N13SpecialCurveOverlap.AffineOverlap) I) =
      I := by
  apply le_antisymm
  · intro z hz
    change
      algebraMap AffineCurve
          N13SpecialCurveOverlap.AffineOverlap z ∈
        Ideal.map
          (algebraMap AffineCurve
            N13SpecialCurveOverlap.AffineOverlap) I at hz
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
      (Submonoid.powers N13SpecialCurveOverlap.xClass)] at hz
    obtain ⟨m, hm, hmz⟩ := hz
    obtain ⟨n, rfl⟩ := hm
    exact mem_of_x_pow_mul_mem hx n hmz
  · exact Ideal.le_comap_map

/-- The direct special affine-to-infinity map factors through localization
at `x` followed by the explicit overlap equivalence. -/
private theorem affineToInfinityOverlap_eq_comp :
    N13SpecialCurveOverlap.affineToInfinityOverlap =
      N13SpecialCurveOverlap.overlapEquiv.toRingHom.comp
        (algebraMap AffineCurve
          N13SpecialCurveOverlap.AffineOverlap) := by
  apply DFunLike.ext _ _
  intro z
  change
    N13SpecialCurveOverlap.affineToInfinityOverlap z =
      N13SpecialCurveOverlap.affineOverlapToInfinityOverlap
        (algebraMap AffineCurve
          N13SpecialCurveOverlap.AffineOverlap z)
  exact
    (N13SpecialCurveOverlap.affineOverlapToInfinityOverlap_algebraMap
      z).symm

/-- Restricting to the actual special overlap loses no information from an
affine ideal in which `x` is already invertible. -/
theorem affineOverlapContracted_of_xUnitMod
    {I : Ideal AffineCurve}
    (hx : XUnitMod I) :
    Ideal.comap
        N13SpecialCurveOverlap.affineToInfinityOverlap
        (Ideal.map
          N13SpecialCurveOverlap.affineToInfinityOverlap I) =
      I := by
  let loc :
      AffineCurve →+* N13SpecialCurveOverlap.AffineOverlap :=
    algebraMap AffineCurve
      N13SpecialCurveOverlap.AffineOverlap
  let e :
      N13SpecialCurveOverlap.AffineOverlap →+* InfinityOverlap :=
    N13SpecialCurveOverlap.overlapEquiv.toRingHom
  have he :
      Ideal.comap e (Ideal.map e (Ideal.map loc I)) =
        Ideal.map loc I := by
    rw [Ideal.comap_map_of_surjective e
      N13SpecialCurveOverlap.overlapEquiv.surjective]
    have hker : RingHom.ker e = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot e).mp
        N13SpecialCurveOverlap.overlapEquiv.injective
    rw [← RingHom.ker_eq_comap_bot, hker, sup_bot_eq]
  rw [affineToInfinityOverlap_eq_comp,
    ← Ideal.map_map, ← Ideal.comap_comap, he]
  exact comap_map_affineOverlap_eq_of_xUnitMod hx

/-- Reduction preserves the property that `x` is a unit modulo an affine
ideal: reduce an explicit inverse relation coefficientwise. -/
theorem map_reduceCoordinate_xUnitMod
    {I : Ideal N13OrdinaryCurveOverlap.AffineCurve}
    (hx : N13IntegralInfinityGraphSaturation.XUnitMod I) :
    XUnitMod
      (Ideal.map
        N13GeneralizedMumfordReduction.reduceCoordinate I) := by
  obtain ⟨q, hq⟩ := hx
  refine
    ⟨N13GeneralizedMumfordReduction.reduceCoordinate q, ?_⟩
  have hmap :=
    Ideal.mem_map_of_mem
      N13GeneralizedMumfordReduction.reduceCoordinate hq
  simpa [XUnitMod,
    N13IntegralInfinityGraphSaturation.XUnitMod,
    N13OrdinaryCurveOverlap.xClass,
    N13SpecialCurveOverlap.xClass] using hmap

/-- Compatible special chart pairs with the same infinity ideal and
`x`-saturated affine ideals are equal.  Their overlap extensions agree by
compatibility, and saturation contracts that common extension back to the
two original affine ideals. -/
theorem chartPair_eq_of_infinityIdeal_eq
    (L M : N13TwoChartSpecialRestriction.ChartPair)
    (hL : XUnitMod L.affineIdeal)
    (hM : XUnitMod M.affineIdeal)
    (hinfinity : L.infinityIdeal = M.infinityIdeal) :
    L = M := by
  apply N13TwoChartSpecialRestriction.ChartPair.ext
  · have hoverlap :
        Ideal.map
            N13SpecialCurveOverlap.affineToInfinityOverlap
            L.affineIdeal =
          Ideal.map
            N13SpecialCurveOverlap.affineToInfinityOverlap
            M.affineIdeal := by
      rw [L.overlap_eq, M.overlap_eq, hinfinity]
    rw [← affineOverlapContracted_of_xUnitMod hL,
      ← affineOverlapContracted_of_xUnitMod hM, hoverlap]
  · exact hinfinity

end

end MazurProof.N13SpecialAffineSaturation


