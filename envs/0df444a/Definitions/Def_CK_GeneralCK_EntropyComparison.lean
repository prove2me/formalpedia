-- Prove2me | Definitions.Def_CK_GeneralCK_EntropyComparison
-- name    : CK_GeneralCK_EntropyComparison
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:22:38.13445+00:00
-- url     : https://prove2.me/theorems/5b4fa8bc-57be-49ed-897c-26478cb0eabf
-- title:
--   Courtade–Kumar proof module `GeneralCK.EntropyComparison` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.EntropyComparison` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.EntropyComparison` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.EntropyComparison (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyComparison.lean)

import Definitions.Def_CK_GeneralCK_ProfileBasics
import Definitions.Def_CK_GeneralCK_EtaMonotone
import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_GeneralCK_entropy_comparison

namespace GeneralCK.Comparison
open Set

/-- A continuous scalar curve cannot become positive if its right derivative is
nonpositive wherever the curve is positive. -/
theorem nonpos_of_deriv_nonpos_when_pos {g g' : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hc : ContinuousOn g (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt g (g' t) (Ici t) t)
    (h0 : g 0 ≤ 0)
    (hbound : ∀ t ∈ Ico 0 T, 0 < g t → g' t ≤ 0) : g T ≤ 0 := by
  by_contra hn
  have hp : 0 < g T := lt_of_not_ge hn
  let e := g T / (2 * (T + 1))
  have he : 0 < e := div_pos hp (by positivity)
  have hB : ∀ t : ℝ, HasDerivAt (fun s => e * (s + 1)) e t := by
    intro t
    simpa using ((hasDerivAt_id t).add_const 1).const_mul e
  have hb := image_le_of_deriv_right_lt_deriv_boundary hc hd
    (B := fun t => e * (t + 1)) (B' := fun _ => e)
    (by simpa using h0.trans he.le) hB (by
      intro t ht htB
      have hg : 0 < g t := by rw [htB]; exact mul_pos he (by linarith [ht.1])
      exact (hbound t ht hg).trans_lt he)
    (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)
  have heq : e * (T + 1) = g T / 2 := by
    dsimp [e]
    field_simp
  rw [heq] at hb
  linarith

/-- Comparison with an antitone scalar field. No differentiability of the field
itself, nor differentiation of an inverse function, is required. -/
theorem antitone_ode_comparison {field u v u' v' : ℝ → ℝ} {s : Set ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hf : AntitoneOn field s)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hdu : ∀ t ∈ Ico 0 T, HasDerivWithinAt u (u' t) (Ici t) t)
    (hdv : ∀ t ∈ Ico 0 T, HasDerivWithinAt v (v' t) (Ici t) t)
    (hus : ∀ t ∈ Ico 0 T, u t ∈ s) (hvs : ∀ t ∈ Ico 0 T, v t ∈ s)
    (hu' : ∀ t ∈ Ico 0 T, u' t ≤ field (u t))
    (hv' : ∀ t ∈ Ico 0 T, field (v t) ≤ v' t)
    (h0 : u 0 ≤ v 0) : u T ≤ v T := by
  have h := nonpos_of_deriv_nonpos_when_pos hT (hu.sub hv)
    (fun t ht => (hdu t ht).sub (hdv t ht)) (sub_nonpos.mpr h0) (by
      intro t ht hpos
      change 0 < u t - v t at hpos
      have hf' := hf (hvs t ht) (hus t ht) (by linarith)
      have h₁ := hu' t ht
      have h₂ := hv' t ht
      linarith)
  exact sub_nonpos.mp h





theorem noiseParameter_mem {eps t : ℝ} (he : 0 < eps) (he' : eps < 1 / 2)
    (ht : 0 ≤ t) : noiseParameter eps t ∈ Ioo 0 (1 / 2) := by
  have hp := Real.exp_pos (-2 * t)
  have hle : Real.exp (-2 * t) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hm : 0 < 1 - 2 * eps := by linarith
  have hmul : Real.exp (-2 * t) * (1 - 2 * eps) ≤ 1 - 2 * eps :=
    mul_le_of_le_one_left hm.le hle
  have hmulpos := mul_pos hp hm
  dsimp [noiseParameter]
  constructor <;> linarith

@[simp] theorem noiseParameter_zero (eps : ℝ) : noiseParameter eps 0 = eps := by
  simp [noiseParameter]

theorem hasDerivAt_noiseParameter (eps t : ℝ) :
    HasDerivAt (noiseParameter eps) (1 - 2 * noiseParameter eps t) t := by
  have hd := (((hasDerivAt_id t).const_mul (-2)).exp.mul_const (1 - 2 * eps)).const_sub 1
  convert! hd.div_const 2 using 1
  simp only [noiseParameter, id_eq]
  ring

theorem hasDerivAt_H {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    HasDerivAt H (J p) p := by
  have hl : Real.log ((1 - p) / p) = Real.log (1 - p) - Real.log p :=
    Real.log_div (by linarith) (ne_of_gt hp)
  simpa [H, J, hl] using!
    (Real.hasDerivAt_binEntropy (ne_of_gt hp) (by linarith)).div_const (Real.log 2)

theorem eta_H {p : ℝ} (hp : 0 < p) (hp' : p < 1 / 2) :
    eta (H p) = (1 - 2 * p) * J p := by
  have hlt : H p < 1 := by
    rw [← H_half]
    exact H_strictMonoOn ⟨hp.le, hp'.le⟩ ⟨by norm_num, le_rfl⟩ hp'
  simp [eta, ne_of_lt hlt, entropyInverse_H_lower hp.le hp'.le]

theorem hasDerivAt_entropy_trajectory {eps t : ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) :
    HasDerivAt (fun s => H (noiseParameter eps s))
      (eta (H (noiseParameter eps t))) t := by
  have hp := noiseParameter_mem he he' ht
  rw [eta_H hp.1 hp.2]
  convert! (hasDerivAt_H hp.1 (by linarith [hp.2])).comp t
    (hasDerivAt_noiseParameter eps t) using 1
  ring

/-- The explicit entropy trajectory is a lower bound for every supersolution
of the scalar entropy-production inequality. -/
theorem entropy_lower_bound {eps T : ℝ} {delta delta' : ℝ → ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (hT : 0 ≤ T)
    (hc : ContinuousOn delta (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt delta (delta' t) (Ici t) t)
    (hrange : ∀ t ∈ Ico 0 T, delta t ∈ Ioc 0 1)
    (hprod : ∀ t ∈ Ico 0 T, eta (delta t) ≤ delta' t)
    (h0 : H eps ≤ delta 0) : H (noiseParameter eps T) ≤ delta T := by
  apply antitone_ode_comparison hT eta_antitoneOn
    (u := fun t => H (noiseParameter eps t))
    (u' := fun t => eta (H (noiseParameter eps t)))
    (v' := delta')
  · exact H_continuous.comp_continuousOn (fun t _ =>
      (hasDerivAt_noiseParameter eps t).continuousAt.continuousWithinAt)
  · exact hc
  · intro t ht
    exact (hasDerivAt_entropy_trajectory he he' ht.1).hasDerivWithinAt
  · exact hd
  · intro t ht
    have hp := noiseParameter_mem he he' ht.1
    exact ⟨H_pos hp.1 (by linarith [hp.2]), H_le_one _⟩
  · exact hrange
  · intro _ _
    exact le_rfl
  · exact hprod
  · simpa using h0

end GeneralCK.Comparison


