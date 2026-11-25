-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrictTwist
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T06:23:30.309797+00:00
-- url     : https://prove2.me/theorems/8204a530-d09d-4267-8ac1-a8c1ffde20a4
-- title:
--   PRestrict Twist
-- statement:
--   Definitions and structural lemmas for PRestrict Twist, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PRestrictTwist.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
namespace RestrictTwist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {K' : Type w} [Field K'] [Algebra S K']
def IsFrac (x : Fin (N + 1) → Ω) (c : ℤ) (I : Finset (Fin (N + 1))) (z : Ω)
    (t : Poly S N × Poly S N × ℕ × ℕ) : Prop :=
  t.2.1 ∈ monos I ∧ t.1.IsHomogeneous t.2.2.2 ∧ t.2.1.IsHomogeneous t.2.2.1 ∧
    (t.2.2.2 : ℤ) = t.2.2.1 + c ∧ z = aeval x t.1 / aeval x t.2.1
variable (S) in

def twistRes (x : Fin (N + 1) → Ω) (y : Fin (N + 1) → K') (c : ℤ) (z : Ω) : K' := by
  classical
  exact if h : ∃ (I : Chart y) (t : Poly S N × Poly S N × ℕ × ℕ), IsFrac x c I.1 z t then
    aeval y (Classical.choose (Classical.choose_spec h)).1 /
      aeval y (Classical.choose (Classical.choose_spec h)).2.1
  else 0
variable {x : Fin (N + 1) → Ω} {y : Fin (N + 1) → K'} {hxy : ∀ i, y i ≠ 0 → x i ≠ 0}
variable (S x y) in

def red (I : Finset (Fin (N + 1))) (a : Ω) : K' := by
  classical
  exact if h : ∃ t : Poly S N × Poly S N × ℕ, t.2.1 ∈ monos I ∧ t.1.IsHomogeneous t.2.2 ∧
      t.2.1.IsHomogeneous t.2.2 ∧ a = aeval x t.1 / aeval x t.2.1 then
    aeval y (Classical.choose h).1 / aeval y (Classical.choose h).2.1 else 0
def prodRes (r₁ r₂ : Ω → K') (l : List (Ω × Ω)) (z : Ω) : K' :=
  (l.map fun p => r₁ p.1 * r₂ (p.2 * z)).sum
end RestrictTwist
end
end GroundTheory.Heights₂.Heights.Kleiman


