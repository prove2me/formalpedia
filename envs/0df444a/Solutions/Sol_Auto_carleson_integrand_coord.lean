-- Prove2me | solution 1 for Auto.carleson_integrand_coord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:48:05.550479+00:00
-- url     : https://prove2.me/submissions/aff27c6d-4f33-4a38-9977-b412e1b06409

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution (a ν : ℝ → ℝ) (g : ℝ → ℂ) (σ ε : ℝ) (q : (ℝ × ℝ) × ℝ) :
    (let r := carlesonCoord q
     if ε < |r.1.1 + r.1.2 + r.2| then
       carlesonF₀ a ν σ r.1 * carlesonF₁ g (r.1.2, r.2) * carlesonF₂ a ν σ (r.2, r.1.1) /
         ((r.1.1 + r.1.2 + r.2 : ℝ) : ℂ) else 0) =
      carlesonH a ν g σ ε q.1 * (carlesonW q.1.2 q.2 : ℂ) := by
  obtain ⟨⟨x, t⟩, u⟩ := q
  change (if ε < |x + (u - x / 2) + (t - u - x / 2)| then
      carlesonF₀ a ν σ (x, u - x / 2) * carlesonF₁ g (u - x / 2, t - u - x / 2) *
        carlesonF₂ a ν σ (t - u - x / 2, x) / ((x + (u - x / 2) + (t - u - x / 2) : ℝ) : ℂ)
      else 0) = _
  rw [show x + (u - x / 2) + (t - u - x / 2) = t by ring]
  simp only [carlesonF₀, carlesonF₁, carlesonF₂, carlesonH, carlesonW]
  split_ifs
  · rw [show u - x / 2 + x / 2 = u by ring, show -(u - x / 2) - (t - u - x / 2) = x - t by ring,
      show u - x / 2 - (t - u - x / 2) = 2 * u - t by ring,
      show t - u - x / 2 + x / 2 = t - u by ring]
    have he : Complex.exp ((σ * ν x * (x + (u - x / 2)) : ℝ) * Complex.I) *
        Complex.exp ((σ * ν x * (t - u - x / 2) : ℝ) * Complex.I) =
        Complex.exp ((σ * ν x * t : ℝ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← he]
    push_cast
    ring
  · simp
end Auto
