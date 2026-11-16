-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteInverseSearchInterface
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteInverseSearchInterface
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:50:22.116342+00:00
-- url     : https://prove2.me/theorems/188f3bc4-0089-49c7-aa6e-d981cb96a0be
-- title:
--   Computable analysis · FiniteInverseSearchInterface · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteInverseSearchInterface.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteBisectionIteration

set_option autoImplicit true

/-!
# Reusable finite inverse-search interface

An inverse is represented by a finite target bracket.  A monotone rational
map, an input interval, and endpoint inequalities determine a bisection
computation whose output interval contains the requested target preimage.
-/

namespace ComputableAnalysis

structure FiniteInverseSearchCertificate where
  map : Rat → Rat
  target : Rat
  initialInterval : QInterval
  stage : Nat
  ordered : initialInterval.lo ≤ initialInterval.hi
  lower_bracket : map initialInterval.lo ≤ target
  upper_bracket : target ≤ map initialInterval.hi

def FiniteInverseSearchCertificate.output
    (certificate : FiniteInverseSearchCertificate) : QInterval :=
  monotoneTargetBisectionIterate certificate.map certificate.target
    certificate.stage certificate.initialInterval

theorem FiniteInverseSearchCertificate.output_bracket
    (certificate : FiniteInverseSearchCertificate) :
    certificate.map certificate.output.lo ≤ certificate.target /\
      certificate.target ≤ certificate.map certificate.output.hi := by
  exact monotoneBisectionIterate_preserves_target_bracket
    certificate.target certificate.ordered certificate.lower_bracket
    certificate.upper_bracket certificate.stage

theorem FiniteInverseSearchCertificate.output_width
    (certificate : FiniteInverseSearchCertificate) :
    certificate.output.width =
      certificate.initialInterval.width /
        (2 ^ certificate.stage : Rat) := by
  exact monotoneTargetBisectionIterate_width certificate.target certificate.stage

theorem FiniteInverseSearchCertificate.output_midpoint_witness
    (certificate : FiniteInverseSearchCertificate) :
    certificate.map certificate.output.lo ≤ certificate.target /\
      certificate.target ≤ certificate.map certificate.output.hi /\
      certificate.output.lo ≤ certificate.output.midpoint /\
      certificate.output.midpoint ≤ certificate.output.hi := by
  have hbracket := certificate.output_bracket
  have hordered := monotoneTargetBisectionIterate_ordered
    (f := certificate.map) (I := certificate.initialInterval)
    certificate.target certificate.ordered certificate.stage
  have hmid := QInterval.midpoint_mem hordered
  exact ⟨hbracket.1, hbracket.2, hmid.1, hmid.2⟩

theorem FiniteInverseSearchCertificate.stage_bracket
    (certificate : FiniteInverseSearchCertificate) (n : Nat) :
    certificate.map
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).lo <= certificate.target /\
      certificate.target <= certificate.map
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).hi := by
  exact monotoneBisectionIterate_preserves_target_bracket
    certificate.target certificate.ordered certificate.lower_bracket
    certificate.upper_bracket n

theorem FiniteInverseSearchCertificate.stage_width
    (certificate : FiniteInverseSearchCertificate) (n : Nat) :
    (monotoneTargetBisectionIterate certificate.map certificate.target n
      certificate.initialInterval).width =
        certificate.initialInterval.width / (2 ^ n : Rat) := by
  exact monotoneTargetBisectionIterate_width certificate.target n

/-! The classical intermediate-value step becomes an explicit error budget when
the map is monotone and Lipschitz on the initial interval.  The bisection
midpoint is then a rational representative whose target residual is bounded
by the Lipschitz constant times the current interval width. -/
theorem FiniteInverseSearchCertificate.midpoint_residual_le_lipschitz_width
    (certificate : FiniteInverseSearchCertificate) (L : Rat)
    (hL : 0 <= L)
    (hmono : ∀ ⦃x y : Rat⦄, x <= y -> certificate.map x <= certificate.map y)
    (hlip : ∀ x y : Rat,
      certificate.initialInterval.lo <= x ->
      x <= certificate.initialInterval.hi ->
      certificate.initialInterval.lo <= y ->
      y <= certificate.initialInterval.hi ->
      qabs (certificate.map x - certificate.map y) <=
        L * qabs (x - y)) :
    qabs (certificate.map certificate.output.midpoint - certificate.target) <=
      L * certificate.output.width := by
  let I := certificate.output
  have hI : I.lo <= I.hi := by
    dsimp [I]
    exact monotoneTargetBisectionIterate_ordered
      certificate.target certificate.ordered certificate.stage
  have hsub := monotoneTargetBisectionIterate_subinterval
    (f := certificate.map) certificate.target certificate.ordered certificate.stage
  have hmid := QInterval.midpoint_mem hI
  have hbracket := certificate.output_bracket
  have hmap_lo_mid : certificate.map I.lo <= certificate.map I.midpoint := by
    apply hmono
    exact hmid.1
  have hmap_mid_hi : certificate.map I.midpoint <= certificate.map I.hi := by
    apply hmono
    exact hmid.2
  have hcommon := qabs_sub_le_of_common_bounds
    hmap_lo_mid hmap_mid_hi hbracket.1 hbracket.2
  have hIlo_initial : certificate.initialInterval.lo <= I.lo := hsub.1
  have hIhi_initial : I.hi <= certificate.initialInterval.hi := hsub.2
  have hIhi_lower : certificate.initialInterval.lo <= I.hi :=
    Rat.le_trans hIlo_initial hI
  have hIlo_upper : I.lo <= certificate.initialInterval.hi :=
    Rat.le_trans hI hIhi_initial
  have himage_lip := hlip I.hi I.lo
    hIhi_lower hIhi_initial hIlo_initial hIlo_upper
  have hhi_lo : 0 <= I.hi - I.lo := by grind
  have hqabs_width : qabs (I.hi - I.lo) = I.width := by
    rw [qabs_eq_self_of_nonneg hhi_lo]
    rfl
  have himage : certificate.map I.hi - certificate.map I.lo <=
      L * I.width := by
    have hmap_order : certificate.map I.lo <= certificate.map I.hi :=
      hmono (hI)
    have himage_abs := himage_lip
    rw [qabs_eq_self_of_nonneg (by grind :
      0 <= certificate.map I.hi - certificate.map I.lo),
      hqabs_width] at himage_abs
    exact himage_abs
  dsimp [I] at hcommon himage ⊢
  exact Rat.le_trans hcommon himage

/-! The finite inverse search can also be run at every stage, producing the
nested interval algorithm used by `RealCompute`.  The only extra hypothesis is
the harmless normalization that the initial interval has width at most one;
the bisection width law then supplies the explicit precision modulus. -/
def FiniteInverseSearchCertificate.toRealCompute
    (certificate : FiniteInverseSearchCertificate) : RealCompute where
  compute := fun n =>
    monotoneTargetBisectionIterate certificate.map certificate.target n
      certificate.initialInterval

theorem FiniteInverseSearchCertificate.toRealCompute_valid
    (certificate : FiniteInverseSearchCertificate)
    (hwidth : certificate.initialInterval.width <= 1) :
    certificate.toRealCompute.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change 0 <=
      (monotoneTargetBisectionIterate certificate.map certificate.target n
        certificate.initialInterval).hi -
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).lo
    have hordered := monotoneTargetBisectionIterate_ordered
      (f := certificate.map) certificate.target certificate.ordered n
    grind
  · intro n m hnm
    change
      (monotoneTargetBisectionIterate certificate.map certificate.target n
        certificate.initialInterval).lo <=
          (monotoneTargetBisectionIterate certificate.map certificate.target m
            certificate.initialInterval).lo /\
        (monotoneTargetBisectionIterate certificate.map certificate.target m
          certificate.initialInterval).lo <=
          (monotoneTargetBisectionIterate certificate.map certificate.target m
            certificate.initialInterval).hi /\
        (monotoneTargetBisectionIterate certificate.map certificate.target m
          certificate.initialInterval).hi <=
          (monotoneTargetBisectionIterate certificate.map certificate.target n
            certificate.initialInterval).hi
    have hlater := monotoneTargetBisectionIterate_later_subinterval
      (f := certificate.map) certificate.target certificate.ordered hnm
    have hm := monotoneTargetBisectionIterate_ordered
      (f := certificate.map) certificate.target certificate.ordered m
    exact ⟨hlater.1, hm, hlater.2⟩
  · intro eps
    refine ⟨eps.val.den, ?_⟩
    intro n hn
    have hreach := monotoneTargetBisectionIterate_reaches_of_positive_tolerance
      (f := certificate.map) (I := certificate.initialInterval)
      certificate.target hwidth eps
    have hsub := monotoneTargetBisectionIterate_later_subinterval
      (f := certificate.map) certificate.target certificate.ordered hn
    change
      (monotoneTargetBisectionIterate certificate.map certificate.target n
        certificate.initialInterval).width <= eps.val
    have hwidth_mono :
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).width <=
          (monotoneTargetBisectionIterate certificate.map certificate.target
            eps.val.den certificate.initialInterval).width := by
      change
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).hi -
            (monotoneTargetBisectionIterate certificate.map certificate.target n
              certificate.initialInterval).lo <=
          (monotoneTargetBisectionIterate certificate.map certificate.target
            eps.val.den certificate.initialInterval).hi -
            (monotoneTargetBisectionIterate certificate.map certificate.target
              eps.val.den certificate.initialInterval).lo
      grind [hsub.1, hsub.2]
    exact Rat.le_trans hwidth_mono hreach

/-! The same finite certificate also generates the full stage-indexed
interval computation.  This is the reusable bridge from a rational bisection
trace to the project's `RealCompute`: no completed real or choice of a limiting
point is introduced. -/
def FiniteInverseSearchCertificate.toRealComputeFamily
    (certificate : FiniteInverseSearchCertificate) : RealCompute where
  compute := fun n =>
    monotoneTargetBisectionIterate certificate.map certificate.target n
      certificate.initialInterval

theorem FiniteInverseSearchCertificate.toRealComputeFamily_valid
    (certificate : FiniteInverseSearchCertificate)
    (hwidth : certificate.initialInterval.width <= 1) :
    certificate.toRealComputeFamily.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change 0 <=
      (monotoneTargetBisectionIterate certificate.map certificate.target n
        certificate.initialInterval).hi -
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).lo
    have hordered := monotoneTargetBisectionIterate_ordered
      (f := certificate.map) certificate.target certificate.ordered n
    grind
  · intro n m hnm
    have hlater := monotoneTargetBisectionIterate_later_subinterval
      (f := certificate.map) certificate.target certificate.ordered hnm
    have hm := monotoneTargetBisectionIterate_ordered
      (f := certificate.map) certificate.target certificate.ordered m
    exact ⟨hlater.1, hm, hlater.2⟩
  · intro eps
    refine ⟨eps.val.den, ?_⟩
    intro n hn
    have hreach := monotoneTargetBisectionIterate_reaches_of_positive_tolerance
      (f := certificate.map) (I := certificate.initialInterval)
      certificate.target hwidth eps
    have hsub := monotoneTargetBisectionIterate_later_subinterval
      (f := certificate.map) certificate.target certificate.ordered hn
    change
      (monotoneTargetBisectionIterate certificate.map certificate.target n
        certificate.initialInterval).width <= eps.val
    have hwidth_mono :
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).width <=
        (monotoneTargetBisectionIterate certificate.map certificate.target
          eps.val.den certificate.initialInterval).width := by
      change
        (monotoneTargetBisectionIterate certificate.map certificate.target n
          certificate.initialInterval).hi -
            (monotoneTargetBisectionIterate certificate.map certificate.target n
              certificate.initialInterval).lo <=
          (monotoneTargetBisectionIterate certificate.map certificate.target
            eps.val.den certificate.initialInterval).hi -
            (monotoneTargetBisectionIterate certificate.map certificate.target
              eps.val.den certificate.initialInterval).lo
      grind [hsub.1, hsub.2]
    exact Rat.le_trans hwidth_mono hreach

def finiteInverseSearchCertificate
    (map : Rat → Rat) (target : Rat) (initialInterval : QInterval)
    (stage : Nat) (ordered : initialInterval.lo ≤ initialInterval.hi)
    (lower_bracket : map initialInterval.lo ≤ target)
    (upper_bracket : target ≤ map initialInterval.hi) :
    FiniteInverseSearchCertificate where
  map := map
  target := target
  initialInterval := initialInterval
  stage := stage
  ordered := ordered
  lower_bracket := lower_bracket
  upper_bracket := upper_bracket

end ComputableAnalysis


