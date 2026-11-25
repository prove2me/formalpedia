-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitChart
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:18:23.412231+00:00
-- url     : https://prove2.me/theorems/82ad5aaf-8cb0-4fac-a0b4-8eb5c440df88
-- title:
--   Twist Split Chart
-- statement:
--   Definitions and structural lemmas for Twist Split Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/TwistSplitChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistSplitObj
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
open MvPolynomial Pointwise
noncomputable section
universe u w
section Chart
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)
def twLocPart (M₀ : FinGradedSub (S := S) (x := x) Ω) (b c : ℤ) (I : Finset (Fin (N + 1))) :
    Submodule S Ω :=
  Submodule.span S {y | ∃ (z : Ω) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I ∧ s.IsHomogeneous e ∧
    z ∈ twPart η M₀ a b ∧ a - e = c ∧ y = (aeval x s)⁻¹ * z}
theorem twLocPart_chart_mul (M₀ : FinGradedSub (S := S) (x := x) Ω) {b c : ℤ} (K : Chart x)
    (a : chartRing S x K) {y : Ω} (hy : y ∈ twLocPart η M₀ b c K.1) : (a : Ω) * y ∈ twLocPart η M₀ b c K.1 := by
  obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
  rw [ha]
  refine Submodule.span_induction (p := fun y _ => aeval x f / aeval x s * y ∈ twLocPart η M₀ b c K.1)
    ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z, s₁, a₁, e₁, hs₁, hse₁, hz, hae, rfl⟩
    refine Submodule.subset_span ⟨aeval x f * z, s * s₁, a₁ + e, e + e₁, mul_mem hs hs₁, hse.mul hse₁,
      twPart_form_mul η M₀ hf hz, by push_cast; omega, ?_⟩
    rw [map_mul, mul_inv, div_eq_mul_inv]
    ring
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
  · intro c' u _ hu; rw [mul_smul_comm]; exact Submodule.smul_mem _ c' hu
def twLocPartA (M₀ : FinGradedSub (S := S) (x := x) Ω) (b c : ℤ) (K : Chart x) :
    Submodule (chartRing S x K) Ω where
  carrier := twLocPart η M₀ b c K.1
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  smul_mem' a y hy := by rw [chartRing_smul_def]; exact twLocPart_chart_mul η M₀ K a hy
variable {G B : SubSystem S x Ω}
variable (M₀ : FinGradedSub (S := S) (x := x) Ω)
end Chart
end
end GroundTheory.Heights₂.Heights.Kleiman


