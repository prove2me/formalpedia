-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibre
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFibre
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:07.653798+00:00
-- url     : https://prove2.me/theorems/f5c8f6b0-d9af-499f-85e3-8b8551d8ee3d
-- title:
--   Statements Cone Fibre
-- statement:
--   Definitions and structural lemmas for Statements Cone Fibre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsConeFibre.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory
noncomputable section
variable {m n : ℕ}
def coneSet (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (EuclideanSpace ℂ (Fin n)) :=
  {y | ∀ q ∈ J, eval (h.pointOf y) q = 0}
def linProj (π : Fin m → Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin m) :=
  WithLp.toLp 2 fun i => ∑ j, π i j * y j
def fibreCount (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) : ℕ∞ :=
  {y | y ∈ coneSet h J ∧ linProj π y = w}.encard
def ConeFibreDegree.Statement : Prop :=
  ∀ (n e δ : ℕ) (h : HermNorm n) (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : MvPolynomial (Fin (e + 1) × Fin n) ℂ),
    IsProjPrime W → IsChowForm W (e + 1) f → IsMultiHomog δ f →
      ∀ᵐ π : Fin (e + 1) → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin (e + 1)),
        fibreCount h W π w = δ
end
end GroundTheory.Heights₂.Heights


