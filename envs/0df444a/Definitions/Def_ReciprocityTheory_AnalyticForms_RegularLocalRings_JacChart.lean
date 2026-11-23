-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:28:03.430866+00:00
-- url     : https://prove2.me/theorems/1bfaf137-a625-4ed6-a190-627e67158da3
-- title:
--   Jac Chart
-- statement:
--   Definitions and structural lemmas for Jac Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/JacChart.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChartC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {n : ℕ}
def ptIdeal (p : Fin n → ℂ) : Ideal (MvPolynomial (Fin n) ℂ) :=
  RingHom.ker (MvPolynomial.eval p : MvPolynomial (Fin n) ℂ →+* ℂ)
instance ptIdeal_isPrime (p : Fin n → ℂ) : (ptIdeal p).IsPrime :=
  RingHom.ker_isPrime _
abbrev locPt (p : Fin n → ℂ) : Type :=
  Localization.AtPrime (ptIdeal p)
abbrev locRing (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Type :=
  locPt p ⧸ Ideal.map (algebraMap (MvPolynomial (Fin n) ℂ) (locPt p)) K
def grad (p : Fin n → ℂ) (h : MvPolynomial (Fin n) ℂ) : Fin n → ℂ :=
  fun j => eval p (pderiv j h)
def jacSpan (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (grad p '' (K : Set (MvPolynomial (Fin n) ℂ)))
end
end ReciprocityTheory.AnForm.R


