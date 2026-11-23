-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HasFDerivAtEvX
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HasFDerivAtEvX
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:09:28.679808+00:00
-- url     : https://prove2.me/theorems/92c81abc-c5f6-4739-a332-4632b7470a1f
-- title:
--   Has FDeriv At Ev X
-- statement:
--   Definitions and structural lemmas for Has FDeriv At Ev X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/PolynomialDerivatives/HasFDerivAtEvX.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
namespace PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
def crd (k : Fin m × Fin n × Bool) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  if k.2.2 then (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.1))
  else (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k.2.1).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) k.1)
def dP (P : PX m n) (x : Fin m → Fin n → ℂ) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ := ∑ k, evX (pderiv k P) x • crd k
end PositivityTheory.Rg.Sw.LC.NullS


