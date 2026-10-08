-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TraceGluing_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TraceGluing_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:31:51.095985+00:00
-- url     : https://prove2.me/theorems/71b6e581-a80f-4db9-bc48-810299936aa4
-- title:
--   FLT.Assumptions.MazurProof.N13TraceGluing source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TraceGluing

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TraceGluing
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.FractionalIdeal.Inverse

set_option autoImplicit false




/-!
# Generic trace gluing for fractional ideals

Let `Q = M M⁻¹`.  A power of a scalar in `Q`, together with an element of
`Q` congruent to one modulo that scalar, forces `1 ∈ Q` by the finite
geometric-series identity.  Since multiplier products are always contained
in the unit fractional ideal, this proves that `M` is invertible.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13TraceGluing

noncomputable section

variable {A K : Type*}
variable [CommRing A] [IsDomain A]
variable [Field K] [Algebra A K] [IsFractionRing A K]

/-- A generic-power certificate and a congruence-one trace certificate
force a fractional ideal to be a unit. -/
theorem isUnit_of_genericPower_and_modUniformizerTrace
    (M : FractionalIdeal A⁰ K)
    {f : A}
    (hpow :
      ∃ n : ℕ,
        algebraMap A K (f ^ n) ∈ M * M⁻¹)
    (hmod :
      ∃ a : A,
        algebraMap A K (1 - f * a) ∈ M * M⁻¹) :
    IsUnit M := by
  obtain ⟨n, hn⟩ := hpow
  obtain ⟨a, ha⟩ := hmod
  let Q : FractionalIdeal A⁰ K := M * M⁻¹
  change algebraMap A K (f ^ n) ∈ Q at hn
  change algebraMap A K (1 - f * a) ∈ Q at ha
  let z : A := f * a
  let s : A := ∑ i ∈ Finset.range n, z ^ i
  have hzpow : algebraMap A K (z ^ n) ∈ Q := by
    have h := Q.val.smul_mem (a ^ n) hn
    simpa [z, Algebra.smul_def, mul_pow, mul_comm] using h
  have hgeom : s * (1 - z) = 1 - z ^ n := by
    dsimp [s]
    rw [mul_comm]
    simpa using (Commute.one_right z).mul_neg_geom_sum₂ n
  have htail : algebraMap A K (1 - z ^ n) ∈ Q := by
    have ha' : algebraMap A K (1 - z) ∈ Q := by
      simpa [z] using ha
    have hscaled := Q.val.smul_mem s ha'
    have hmapped :
        algebraMap A K (s * (1 - z)) ∈ Q.val := by
      simpa only [Algebra.smul_def, map_mul] using hscaled
    rw [hgeom] at hmapped
    exact FractionalIdeal.mem_coe.mp hmapped
  have hone : (1 : K) ∈ Q := by
    have h := Q.val.add_mem htail hzpow
    simpa using h
  have hQ_le_one :
      Q ≤ (1 : FractionalIdeal A⁰ K) := by
    change M * M⁻¹ ≤ (1 : FractionalIdeal A⁰ K)
    simpa only [FractionalIdeal.inv_eq] using
      (FractionalIdeal.mul_one_div_le_one (I := M))
  have hQ : Q = 1 :=
    le_antisymm hQ_le_one
      ((FractionalIdeal.one_le).mpr hone)
  apply (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp
  simpa [Q] using hQ

end

end MazurProof.N13TraceGluing


