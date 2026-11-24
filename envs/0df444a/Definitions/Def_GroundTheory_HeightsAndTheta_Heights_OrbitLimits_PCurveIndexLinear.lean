-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveIndexLinear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:01.68475+00:00
-- url     : https://prove2.me/theorems/0403d9d5-09bb-458b-a585-88a64a8a53e7
-- title:
--   PCurve Index Linear
-- statement:
--   Definitions and structural lemmas for PCurve Index Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveIndexLinear.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveIndexLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace CurveIndexLinearAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
def cu (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) : Ω :=
  ∏ k, y ⟨k, c k⟩ ^ a k
def secIdeal (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) : AddSubgroup Ω :=
  (chartLat y a 1).map (AddMonoidHom.mulLeft (cu y c a)⁻¹)
def gen (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (c' : ∀ k, ι k) : Ω :=
  cu y c' a / cu y c a
def locRing {y : (Σ k, ι k) → Ω} (m : Ideal (curveRing y)) (hm : m.IsPrime) (S : Subring Ω)
    (hS : ∀ b : curveRing y, (b : Ω) ∈ S) : Subring Ω where
  carrier := {r | ∃ b : curveRing y, b ∉ m ∧ (b : Ω) * r ∈ S}
  mul_mem' := by
    rintro r s ⟨b, hb, hbr⟩ ⟨b', hb', hbs⟩
    refine ⟨b * b', fun h => (hm.mem_or_mem h).elim hb hb', ?_⟩
    have := S.mul_mem hbr hbs
    convert this using 1
    push_cast
    ring
  one_mem' := ⟨1, fun h => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  add_mem' := by
    rintro r s ⟨b, hb, hbr⟩ ⟨b', hb', hbs⟩
    refine ⟨b * b', fun h => (hm.mem_or_mem h).elim hb hb', ?_⟩
    have := S.add_mem (S.mul_mem (hS b') hbr) (S.mul_mem (hS b) hbs)
    convert this using 1
    push_cast
    ring
  zero_mem' := ⟨1, fun h => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  neg_mem' := by
    rintro r ⟨b, hb, hbr⟩
    exact ⟨b, hb, by rw [mul_neg]; exact S.neg_mem hbr⟩
end CurveIndexLinearAlt
end
end GroundTheory.Heights₂.Heights.Targets


