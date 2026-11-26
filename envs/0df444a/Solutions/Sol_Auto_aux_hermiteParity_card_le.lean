-- Prove2me | solution 1 for Auto.aux_hermiteParity_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:54:11.409827+00:00
-- url     : https://prove2.me/submissions/47c22c0d-de59-4f08-9d74-0774becbf340

module
public import Definitions.Def_LeanNct_Auto_WienerSpace
public import Definitions.Def_LeanNct_Auto_Preliminaries_Notation
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.LHopital
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
public import Definitions.Def_LeanNct_Auto_Preliminaries_Gaussians

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter
open scoped FourierTransform Real RealInnerProductSpace Topology
noncomputable section
namespace Auto
theorem _root_.solution (m : ℕ) :
    ((Finset.range (m + 1)).filter (fun d => Even (m + d))).card ≤ m / 2 + 1 := by
  let S := (Finset.range (m + 1)).filter (fun d => Even (m + d))
  change S.card ≤ m / 2 + 1
  rw [← Finset.card_range (m / 2 + 1)]
  refine Finset.card_le_card_of_injOn (fun d => (m - d) / 2) ?_ ?_
  case refine_1 =>
    intro d hd
    have hd' := (Finset.mem_filter.mp hd).1
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.sub_le m d)))
  case refine_2 =>
    intro a ha b hb hab
    change (m - a) / 2 = (m - b) / 2 at hab
    have ha_le : a ≤ m := by
      exact Nat.le_of_lt_succ
        (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)
    have hb_le : b ≤ m := by
      exact Nat.le_of_lt_succ
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
    have hea : Even (m + a) := (Finset.mem_filter.mp ha).2
    have heb : Even (m + b) := (Finset.mem_filter.mp hb).2
    have hsa : Even (m - a) := by
      exact (Nat.even_sub ha_le).mpr ((Nat.even_add).mp hea)
    have hsb : Even (m - b) := by
      exact (Nat.even_sub hb_le).mpr ((Nat.even_add).mp heb)
    have hta : 2 * ((m - a) / 2) = m - a :=
      Nat.two_mul_div_two_of_even hsa
    have htb : 2 * ((m - b) / 2) = m - b :=
      Nat.two_mul_div_two_of_even hsb
    have hsub : m - a = m - b := by
      calc
        m - a = 2 * ((m - a) / 2) := hta.symm
        _ = 2 * ((m - b) / 2) := by rw [hab]
        _ = m - b := htb
    omega
end Auto
