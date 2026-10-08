-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LocalDlogRegimes_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13LocalDlogRegimes_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:20:02.803151+00:00
-- url     : https://prove2.me/theorems/f6168005-952c-4943-be31-d207bb7d578a
-- title:
--   FLT.Assumptions.MazurProof.N13LocalDlogRegimes source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13LocalDlogRegimes

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13LocalDlogRegimes
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LocalDlogTwo_p0
import Mathlib.NumberTheory.Padics.RingHoms

set_option autoImplicit false




/-!
# The two local first-jet regimes for N13 at two

This file connects the finite first-jet calculation in
`N13LocalDlogTwo` to the two valuation regimes for a `2`-adic affine
coordinate.

For an integral coordinate, reduction gives

`x - θ ↦ x̄ - α`,

a constant unit of the dual-number ring.  For a nonintegral coordinate,
putting `t = x⁻¹` and removing the rational scalar `x` gives

`1 - t θ ↦ 1`,

because positive `2`-adic valuation forces `t̄ = 0`.  Both jets therefore
have zero first ramified logarithm.  No local square-class enumeration is
used.

Proof boundary: this file proves the two coordinate-jet calculations and
their `ℚ₂` residue adapters.  It does not yet construct the map from the
actual completed sextic order modulo its prime square, nor identify a
Mumford/Jacobian Kummer value with one of these coordinate jets.  That
fixed local-order compatibility is isolated in
`scratch/N13_Q2_ADAPTER.md`.
-/

open scoped CharTwo

namespace MazurProof.N13LocalDlogRegimes

open N13LocalDlogTwo
open TrivSqZeroExt

noncomputable section

/-! ## Exact dual-number semantics -/

/-- Embed an `𝔽₂` residue as a constant element of the N13 dual-number
quotient over `𝔽₈`. -/
def scalarDual (a : ZMod 2) : DualNumber F8 :=
  inl (algebraMap (ZMod 2) F8 a)

/-- The residue of the cubic generator in the first-jet quotient. -/
def thetaDual : DualNumber F8 :=
  inl alpha

/-- The image of the Gaussian unit `i` under `i ↦ 1 + ε`. -/
def gaussianIDual : DualNumber F8 :=
  (1, 1)

set_option backward.isDefEq.respectTransparency.types false in
theorem gaussianIDual_sq :
    gaussianIDual ^ 2 = -1 := by
  rw [pow_two]
  apply TrivSqZeroExt.ext
  · simp [gaussianIDual, TrivSqZeroExt.fst_mul]
  · simp [gaussianIDual, TrivSqZeroExt.snd_mul]

/-- The Gaussian cubic relation remains valid in the first-jet quotient.
This verifies directly that `i ↦ 1+ε` and `θ ↦ α` are compatible with
the local presentation, rather than merely assigning two unrelated
dual numbers. -/
theorem gaussian_cubic_jet_relation :
    thetaDual ^ 3 + 2 * thetaDual ^ 2 - thetaDual - 1 -
        gaussianIDual * (2 * thetaDual * (thetaDual + 1)) = 0 := by
  have htwo : (2 : DualNumber F8) = 0 := by
    ext
    · change (2 : F8) = 0
      exact charTwo
    · exact TrivSqZeroExt.snd_natCast (R := F8) (M := F8) 2
  rw [htwo]
  simp only [zero_mul, add_zero, mul_zero, sub_zero]
  ext
  · change alpha ^ 3 - alpha - 1 = 0
    simpa only [sub_eq_add_neg, CharTwo.neg_eq] using alpha_relation
  · simp [thetaDual]

/-- The raw first jet of `x - θ` in the integral regime. -/
def integralRawJet (xbar : ZMod 2) : DualNumber F8 :=
  scalarDual xbar - thetaDual

theorem integral_residue_ne_alpha (xbar : ZMod 2) :
    algebraMap (ZMod 2) F8 xbar - alpha ≠ 0 := by
  rcases eq_or_ne xbar 0 with rfl | hx
  · simpa only [map_zero, zero_sub, neg_ne_zero] using alpha_ne_zero
  · have hxval : xbar.val = 1 := by
      have hpos : 0 < xbar.val := ZMod.val_pos.mpr hx
      have hlt := xbar.val_lt
      omega
    have hxone : xbar = 1 :=
      (ZMod.val_eq_one (by omega) xbar).mp hxval
    rw [hxone, map_one]
    exact sub_ne_zero.mpr alpha_ne_one.symm

/-- The integral raw jet is a unit. -/
def integralJet (xbar : ZMod 2) : JetUnit :=
  RamifiedDlog.unitOf
    (algebraMap (ZMod 2) F8 xbar - alpha) 0
    (integral_residue_ne_alpha xbar)

@[simp] theorem integralJet_val (xbar : ZMod 2) :
    (integralJet xbar : DualNumber F8) = integralRawJet xbar := by
  ext <;> simp [integralJet, integralRawJet, scalarDual, thetaDual]

/-- Every modeled integral coordinate jet has zero ramified logarithm. -/
theorem dlog_integralJet (xbar : ZMod 2) :
    RamifiedDlog.dlog (integralJet xbar) = 0 := by
  simp [integralJet]

/-- The raw normalized jet in the nonintegral regime. -/
def normalizedRawJet (tbar : ZMod 2) : DualNumber F8 :=
  1 - scalarDual tbar * thetaDual

theorem normalized_residue_ne_zero
    (tbar : ZMod 2) (ht : tbar = 0) :
    1 - algebraMap (ZMod 2) F8 tbar * alpha ≠ 0 := by
  subst tbar
  simp

/-- Package the normalized nonintegral jet as a unit once its inverse
coordinate has zero residue. -/
def normalizedJet (tbar : ZMod 2) (ht : tbar = 0) : JetUnit :=
  RamifiedDlog.unitOf
    (1 - algebraMap (ZMod 2) F8 tbar * alpha) 0
    (normalized_residue_ne_zero tbar ht)

@[simp] theorem normalizedJet_val
    (tbar : ZMod 2) (ht : tbar = 0) :
    (normalizedJet tbar ht : DualNumber F8) =
      normalizedRawJet tbar := by
  ext <;> simp [normalizedJet, normalizedRawJet, scalarDual, thetaDual]

theorem normalizedRawJet_eq_one
    (tbar : ZMod 2) (ht : tbar = 0) :
    normalizedRawJet tbar = 1 := by
  subst tbar
  simp [normalizedRawJet, scalarDual]

/-- After removing the rational scalar, every modeled nonintegral
coordinate jet has zero ramified logarithm. -/
theorem dlog_normalizedJet
    (tbar : ZMod 2) (ht : tbar = 0) :
    RamifiedDlog.dlog (normalizedJet tbar ht) = 0 := by
  simp [normalizedJet]

/-! ## `ℚ₂` and `ℤ₂` adapters -/

abbrev Q2 : Type := ℚ_[2]
abbrev Z2 : Type := ℤ_[2]

/-- Reduction of a `2`-adic integer into constant dual numbers. -/
def padicScalarDualHom : Z2 →+* DualNumber F8 :=
  (algebraMap F8 (DualNumber F8)).comp
    ((algebraMap (ZMod 2) F8).comp PadicInt.toZMod)

/-- The residue used by the integral first-jet regime. -/
def integralResidue (x : Z2) : ZMod 2 :=
  PadicInt.toZMod x

theorem integralRawJet_eq_map_sub_theta (x : Z2) :
    integralRawJet (integralResidue x) =
      padicScalarDualHom x - thetaDual := by
  ext <;>
    simp [integralRawJet, integralResidue, padicScalarDualHom,
      scalarDual, thetaDual, TrivSqZeroExt.algebraMap_eq_inl']

/-- The first jet attached to a `2`-adic integer. -/
def integralPadicJet (x : Z2) : JetUnit :=
  integralJet (integralResidue x)

theorem dlog_integralPadicJet (x : Z2) :
    RamifiedDlog.dlog (integralPadicJet x) = 0 :=
  dlog_integralJet _

/-- Regard an integral `2`-adic number as a `2`-adic integer. -/
def integralPart (x : Q2) (hx : ‖x‖ ≤ 1) : Z2 :=
  ⟨x, hx⟩

/-- The integral-regime first jet attached directly to a `2`-adic
coordinate. -/
def integralQ2Jet (x : Q2) (hx : ‖x‖ ≤ 1) : JetUnit :=
  integralPadicJet (integralPart x hx)

theorem dlog_integralQ2Jet (x : Q2) (hx : ‖x‖ ≤ 1) :
    RamifiedDlog.dlog (integralQ2Jet x hx) = 0 :=
  dlog_integralPadicJet _

/-- The integral first jet, stated in the valuation language used by the
local two-case split. -/
def integralQ2JetOfValuation
    (x : Q2) (hx : 0 ≤ x.valuation) : JetUnit :=
  integralQ2Jet x ((Padic.norm_le_one_iff_val_nonneg x).2 hx)

theorem dlog_integralQ2JetOfValuation
    (x : Q2) (hx : 0 ≤ x.valuation) :
    RamifiedDlog.dlog (integralQ2JetOfValuation x hx) = 0 :=
  dlog_integralQ2Jet _ _

/-- If `x` is nonintegral, its inverse is a `2`-adic integer. -/
def inverseIntegralPart (x : Q2) (hx : x.valuation < 0) : Z2 :=
  ⟨x⁻¹, (Padic.norm_le_one_iff_val_nonneg x⁻¹).2 (by
    rw [Padic.valuation_inv]
    omega)⟩

theorem inverseIntegralPart_ne_zero
    (x : Q2) (hx : x.valuation < 0) :
    inverseIntegralPart x hx ≠ 0 := by
  apply PadicInt.coe_ne_zero.mp
  simp only [inverseIntegralPart, Subtype.coe_mk]
  intro h
  have hx0 : x = 0 := inv_eq_zero.mp h
  rw [hx0, Padic.valuation_zero] at hx
  omega

theorem inverseIntegralPart_valuation_pos
    (x : Q2) (hx : x.valuation < 0) :
    0 < (inverseIntegralPart x hx).valuation := by
  have hval :
      ((inverseIntegralPart x hx).valuation : ℤ) = -x.valuation := by
    rw [← PadicInt.valuation_coe]
    exact Padic.valuation_inv x
  omega

theorem nonintegral_coordinate_ne_zero
    (x : Q2) (hx : x.valuation < 0) :
    x ≠ 0 := by
  intro hx0
  rw [hx0, Padic.valuation_zero] at hx
  omega

/-- The algebraic factorization behind the nonintegral normalization.
The first factor is a rational scalar, hence is invisible in the fake
square-class target. -/
theorem scalar_sub_factorization
    {K : Type*} [Field K] [Algebra Q2 K]
    (x : Q2) (theta : K) (hx : x ≠ 0) :
    algebraMap Q2 K x - theta =
      algebraMap Q2 K x *
        (1 - algebraMap Q2 K x⁻¹ * theta) := by
  have hxK : algebraMap Q2 K x ≠ 0 := by
    rw [← map_zero (algebraMap Q2 K)]
    exact (algebraMap Q2 K).injective.ne hx
  rw [map_inv₀, mul_sub, mul_one, ← mul_assoc,
    mul_inv_cancel₀ hxK, one_mul]

/-- Positive valuation of `x⁻¹` forces zero residue modulo `2`. -/
theorem inverseIntegralPart_residue_eq_zero
    (x : Q2) (hx : x.valuation < 0) :
    PadicInt.toZMod (inverseIntegralPart x hx) = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
  have hmem :=
    (PadicInt.mem_span_pow_iff_le_valuation
      (p := 2) (inverseIntegralPart x hx)
      (inverseIntegralPart_ne_zero x hx) 1).2 (by
        have hv := inverseIntegralPart_valuation_pos x hx
        omega)
  simpa only [pow_one, Ideal.mem_span_singleton] using hmem

theorem normalizedRawJet_eq_map_inverse
    (x : Q2) (hx : x.valuation < 0) :
    normalizedRawJet
        (PadicInt.toZMod (inverseIntegralPart x hx)) =
      1 - padicScalarDualHom (inverseIntegralPart x hx) * thetaDual := by
  ext <;>
    simp [normalizedRawJet, padicScalarDualHom, scalarDual, thetaDual,
      TrivSqZeroExt.algebraMap_eq_inl']

/-- The normalized first jet attached to a nonintegral `2`-adic
coordinate. -/
def nonintegralQ2Jet (x : Q2) (hx : x.valuation < 0) : JetUnit :=
  normalizedJet
    (PadicInt.toZMod (inverseIntegralPart x hx))
    (inverseIntegralPart_residue_eq_zero x hx)

@[simp] theorem nonintegralQ2Jet_val
    (x : Q2) (hx : x.valuation < 0) :
    (nonintegralQ2Jet x hx : DualNumber F8) = 1 := by
  rw [nonintegralQ2Jet, normalizedJet_val,
    normalizedRawJet_eq_one _ (inverseIntegralPart_residue_eq_zero x hx)]

theorem dlog_nonintegralQ2Jet
    (x : Q2) (hx : x.valuation < 0) :
    RamifiedDlog.dlog (nonintegralQ2Jet x hx) = 0 :=
  dlog_normalizedJet _ _

end

end MazurProof.N13LocalDlogRegimes


