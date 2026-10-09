-- Prove2me | Definitions.Def_ConnesGreen_integral_certificate_kernel
-- name    : ConnesGreen_integral_certificate_kernel
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-08T21:42:39.131059+00:00
-- url     : https://prove2.me/theorems/907458b7-8d9e-47ef-b7ba-3f9a4aada9c9
-- title:
--   Explicit Green/source integral kernels for original finite Gram certificates
-- statement:
--   For the unchanged actual zeta-zero subtype and original Dirichlet Green columns, define the source kernel J(t,ρ,σ) as the interval integral of conjugate(actualGreenSource ρ) times greenColumn t σ. The signed pair kernel combines its four reflected entries with the exact square-root multiplicities and factor 1/4. Tagged positive F and selected negative S columns give a finite matrix H of these kernels. The integral certificate is δH + H E H, where E is diagonal with positive tags +1 and negative tags −1. The error is δH because the original columns need not be orthonormal. These are exact auxiliary formulas, with no new carrier, zero set, inverse, or positivity premise.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/FiniteIntegralGram.lean at d81aa3cc2a387fa9f51ee06fee978b868cbc6b85

import Definitions.Def_ConnesGreen_finite_certificate_gram
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative MeasureTheory Matrix
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
namespace ConnesGreen
/-- Exact original Green/source integral, without physical-carrier projections. -/
def canonicalSourceGramKernel (t : ℝ) (ρ σ : CriticalZeros) : ℂ :=
  ∫ x in -t..t, star (actualGreenSource ρ x) * greenColumn t σ x

/-- Original multiplicity and /2 pair normalization, for real pair signs. -/
def canonicalPairGramKernel (t ε η : ℝ) (ρ σ : CriticalZeros) : ℂ :=
  ((Real.sqrt (zeroMult ρ.1 : ℝ) : ℂ) *
    (Real.sqrt (zeroMult σ.1 : ℝ) : ℂ) / 4) *
    (canonicalSourceGramKernel t ρ σ +
      (η : ℂ) * canonicalSourceGramKernel t ρ (reflectedZero σ) +
      (ε : ℂ) * canonicalSourceGramKernel t (reflectedZero ρ) σ +
      (ε : ℂ) * (η : ℂ) * canonicalSourceGramKernel t (reflectedZero ρ) (reflectedZero σ))

/-- The actual column Gram matrix expressed entirely by the original integrals. -/
def canonicalFiniteColumnKernel (t : ℝ) (S F : Finset CriticalZeros) :
    Matrix ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S})
      ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) ℂ :=
  let sign := Sum.elim (fun _ : {ρ : CriticalZeros // ρ ∈ F} => (1 : ℝ))
    (fun _ : {ρ : CriticalZeros // ρ ∈ S} => (-1 : ℝ))
  let zero := Sum.elim (fun ρ : {ρ : CriticalZeros // ρ ∈ F} => ρ.1)
    (fun ρ : {ρ : CriticalZeros // ρ ∈ S} => ρ.1)
  fun i j => canonicalPairGramKernel t (sign i) (sign j) (zero i) (zero j)

/-- A finite polynomial in the explicit integral Gram kernel, with original
positive/negative tags and the SAME error allowance. No inverse is used. -/
def canonicalFiniteIntegralCertificate (t : ℝ) (S F : Finset CriticalZeros) (δ : ℝ) :
    Matrix ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S})
      ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) ℂ :=
  let H := canonicalFiniteColumnKernel t S F
  let sign := Sum.elim (fun _ : {ρ : CriticalZeros // ρ ∈ F} => (1 : ℂ))
    (fun _ : {ρ : CriticalZeros // ρ ∈ S} => (-1 : ℂ))
  (δ : ℂ) • H + H * Matrix.diagonal sign * H


end ConnesGreen


