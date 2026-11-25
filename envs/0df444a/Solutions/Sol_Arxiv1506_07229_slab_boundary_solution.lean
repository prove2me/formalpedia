-- Prove2me | solution 1 for Arxiv1506_07229.slab_boundary_solution
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:47:19.612905+00:00
-- url     : https://prove2.me/submissions/c0e911ae-0601-4e1c-9059-97559490c81a

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate

namespace Arxiv1506_07229

theorem slab_boundary_solution (eps : ℂ) (a q : ℝ) (ha : 0 < a) (hq : 0 < q) (he : eps ≠ 0)
    (hD : 1 + (Real.exp (a * q) : ℂ) + eps * ((Real.exp (a * q) : ℂ) - 1) ≠ 0) :
    slabBC eps a q (slabA1 eps a q) (slabA2 eps a q) (slabA2 eps a q) (slabA1 eps a q) ∧
      (eps * ((Real.exp (a * q) : ℂ) + 1) + ((Real.exp (a * q) : ℂ) - 1) ≠ 0 →
        ∀ A1 A2 B2 B3 : ℂ, slabBC eps a q A1 A2 B2 B3 →
          A1 = slabA1 eps a q ∧ A2 = slabA2 eps a q ∧ B2 = slabA2 eps a q ∧ B3 = slabA1 eps a q) := by
  have e1 : (Real.exp (-(q * a / 2)) : ℂ) = (Real.exp (q * a / 2) : ℂ)⁻¹ := by
    rw [Real.exp_neg]; push_cast; rfl
  have e2 : (Real.exp (a * q) : ℂ) = (Real.exp (q * a / 2) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, sq, ← Real.exp_add]; congr 2; ring
  have e3 : Real.exp (a * q / 2) = Real.exp (q * a / 2) := by ring_nf
  have hE0 : (Real.exp (q * a / 2) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  unfold slabBC slabA1 slabA2
  rw [e3, e1, e2]
  rw [e2] at hD
  generalize (Real.exp (q * a / 2) : ℂ) = E at hE0 hD ⊢
  have hsol : (1 + (eps * (1 - E ^ 2) * ((eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1))))
        * E⁻¹ = 1 / eps + (eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1)) * E⁻¹ +
          (eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1)) * E) ∧
      (1 + (eps * (1 - E ^ 2) * ((eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1)))) * E⁻¹ =
        1 / eps + (eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1)) * E +
          (eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1)) * E⁻¹) ∧
      (-(eps * (1 - E ^ 2) * ((eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1))) * E⁻¹) =
        eps * (-((eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1)) * E⁻¹) +
          (eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1)) * E)) ∧
      (eps * (1 - E ^ 2) * ((eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1))) * E⁻¹ =
        eps * (-((eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1)) * E) +
          (eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1)) * E⁻¹)) := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (field_simp; ring)
  refine ⟨hsol, ?_⟩
  intro hD2 A1 A2 B2 B3 ⟨h1, h2, h3, h4⟩
  obtain ⟨s1, s2, s3, s4⟩ := hsol
  set A2v := (eps - 1) / eps * E / (1 + E ^ 2 + eps * (E ^ 2 - 1))
  set A1v := eps * (1 - E ^ 2) * A2v
  set u := E⁻¹ with hu
  have huE : u * E = 1 := inv_mul_cancel₀ hE0
  -- differences satisfy the homogeneous system
  set x := A2 - A2v
  set y := B2 - A2v
  have g1 : (A1 - A1v) * u = x * u + y * E := by linear_combination h1 - s1
  have g2 : (B3 - A1v) * u = x * E + y * u := by linear_combination h2 - s2
  have g3 : -((A1 - A1v) * u) = eps * (-(x * u) + y * E) := by linear_combination h3 - s3
  have g4 : (B3 - A1v) * u = eps * (-(x * E) + y * u) := by linear_combination h4 - s4
  have k1 : x * u * (eps - 1) - y * E * (eps + 1) = 0 := by linear_combination g1 + g3
  have k2 : x * E * (1 + eps) + y * u * (1 - eps) = 0 := by linear_combination g4 - g2
  have hdet : (1 + E ^ 2 + eps * (E ^ 2 - 1)) * (eps * (E ^ 2 + 1) + (E ^ 2 - 1)) ≠ 0 :=
    mul_ne_zero hD hD2
  have hx : x = 0 := by
    have : x * ((1 + E ^ 2 + eps * (E ^ 2 - 1)) * (eps * (E ^ 2 + 1) + (E ^ 2 - 1))) = 0 := by
      linear_combination E ^ 2 * u * (1 - eps) * k1 + E ^ 3 * (eps + 1) * k2 +
        x * (eps - 1) ^ 2 * (u * E + 1) * huE
    exact (mul_eq_zero.mp this).resolve_right hdet
  have hy : y = 0 := by
    have : y * ((1 + E ^ 2 + eps * (E ^ 2 - 1)) * (eps * (E ^ 2 + 1) + (E ^ 2 - 1))) = 0 := by
      linear_combination -(E ^ 2) * (E * (1 + eps) * k1 - u * (eps - 1) * k2) +
        y * (eps - 1) ^ 2 * (u * E + 1) * huE
    exact (mul_eq_zero.mp this).resolve_right hdet
  have hA2 : A2 = A2v := sub_eq_zero.mp hx
  have hB2 : B2 = A2v := sub_eq_zero.mp hy
  refine ⟨?_, hA2, hB2, ?_⟩
  · linear_combination E * g1 - (A1 - A1v) * huE + E * u * hx + E ^ 2 * hy
  · linear_combination E * g2 - (B3 - A1v) * huE + E ^ 2 * hx + E * u * hy

end Arxiv1506_07229
open Arxiv1506_07229 in
theorem solution (eps : ℂ) (a q : ℝ) (ha : 0 < a) (hq : 0 < q) (he : eps ≠ 0)
    (hD : 1 + (Real.exp (a * q) : ℂ) + eps * ((Real.exp (a * q) : ℂ) - 1) ≠ 0) :
    slabBC eps a q (slabA1 eps a q) (slabA2 eps a q) (slabA2 eps a q) (slabA1 eps a q) ∧
      (eps * ((Real.exp (a * q) : ℂ) + 1) + ((Real.exp (a * q) : ℂ) - 1) ≠ 0 →
        ∀ A1 A2 B2 B3 : ℂ, slabBC eps a q A1 A2 B2 B3 →
          A1 = slabA1 eps a q ∧ A2 = slabA2 eps a q ∧ B2 = slabA2 eps a q ∧ B3 = slabA1 eps a q) :=
  slab_boundary_solution eps a q ha hq he hD
