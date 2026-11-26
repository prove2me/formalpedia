-- Prove2me | solution 1 for Arxivcond_mat_0004049.pDiff_tails
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T13:58:40.563843+00:00
-- url     : https://prove2.me/submissions/cb99c097-4937-4a31-ab62-06edddbdd4e0

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Filter Topology

namespace Arxivcond_mat_0004049

/-- `h u = (Q u² + (1/φ̄ - u)²)⁻¹`; for `u = φ⁻¹` this is `φ² / (Q + (φ/φ̄ - 1)²)`. -/
private lemma tails_aux (Q phibar : ℝ) (hQ : 0 < Q) (hphibar : 0 < phibar) (l : Filter ℝ)
    (hl : Tendsto (fun φ : ℝ => φ⁻¹) l (𝓝 0)) (hne : ∀ᶠ φ in l, φ ≠ 0) :
    Tendsto (fun φ => |φ| ^ 3 * pDiff Q phibar φ) l (𝓝 (Q * phibar ^ 2 / 2)) := by
  set h : ℝ → ℝ := fun u => (Q * u ^ 2 + (1 / phibar - u) ^ 2)⁻¹ with hh
  have hcont : ContinuousAt h 0 := by
    refine ContinuousAt.inv₀ (by fun_prop) ?_
    simp; positivity
  have h0 : h 0 = phibar ^ 2 := by simp [hh]
  have hlim : Tendsto (fun φ : ℝ => Q / (2 * phibar) * h φ⁻¹ ^ ((3 : ℝ) / 2)) l
      (𝓝 (Q / (2 * phibar) * (phibar ^ 2) ^ ((3 : ℝ) / 2))) := by
    refine Tendsto.const_mul _ ?_
    refine Tendsto.rpow_const ?_ (Or.inl (by positivity))
    rw [← h0]
    exact hcont.tendsto.comp hl
  have hval : Q / (2 * phibar) * (phibar ^ 2) ^ ((3 : ℝ) / 2) = Q * phibar ^ 2 / 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hphibar.le]
    norm_num
    field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hne] with φ hφ
  have hD : 0 < Q + (φ / phibar - 1) ^ 2 := by positivity
  have hhφ : h φ⁻¹ = φ ^ 2 / (Q + (φ / phibar - 1) ^ 2) := by
    simp only [hh]
    field_simp
  rw [hhφ, Real.div_rpow (sq_nonneg φ) hD.le, pDiff]
  rw [show φ ^ 2 = |φ| ^ 2 by rw [sq_abs], ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg φ)]
  rw [show (-(3 : ℝ) / 2) = -((3 : ℝ) / 2) by ring, Real.rpow_neg hD.le]
  norm_num
  field_simp

private theorem pDiff_tails_aux (Q phibar : ℝ) (hQ : 0 < Q) (hphibar : 0 < phibar) :
    Tendsto (fun φ => |φ| ^ 3 * pDiff Q phibar φ) atTop (𝓝 (Q * phibar ^ 2 / 2)) ∧
      Tendsto (fun φ => |φ| ^ 3 * pDiff Q phibar φ) atBot (𝓝 (Q * phibar ^ 2 / 2)) :=
  ⟨tails_aux Q phibar hQ hphibar atTop tendsto_inv_atTop_zero
      (eventually_ne_atTop 0),
    tails_aux Q phibar hQ hphibar atBot tendsto_inv_atBot_zero
      (eventually_ne_atBot 0)⟩

end Arxivcond_mat_0004049

open Arxivcond_mat_0004049 in
theorem solution (Q phibar : ℝ) (hQ : 0 < Q) (hphibar : 0 < phibar) :
    Tendsto (fun φ => |φ| ^ 3 * pDiff Q phibar φ) atTop (𝓝 (Q * phibar ^ 2 / 2)) ∧
      Tendsto (fun φ => |φ| ^ 3 * pDiff Q phibar φ) atBot (𝓝 (Q * phibar ^ 2 / 2)) :=
  pDiff_tails_aux Q phibar hQ hphibar
