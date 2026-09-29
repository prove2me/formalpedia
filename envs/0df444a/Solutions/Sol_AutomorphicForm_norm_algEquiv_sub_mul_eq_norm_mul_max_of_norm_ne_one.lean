-- Prove2me | solution 1 for AutomorphicForm.norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/21725ea8-0d1d-55ca-9f2a-1db2df11d420

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

namespace Ws31
namespace S3b

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)

scoped instance isScalarTower_int : IsScalarTower (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem isIntegral_of_mem {y : Lw} (hy : y ∈ w.1.adicCompletionIntegers L) :
    IsIntegral (v.adicCompletionIntegers K) y := by
  haveI : Algebra.IsIntegral (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.of_finite _ _
  have h : IsIntegral (v.adicCompletionIntegers K) (⟨y, hy⟩ : w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.isIntegral _
  exact h.map (IsScalarTower.toAlgHom (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L))

theorem mem_of_isIntegral {y : Lw} (hy : IsIntegral (v.adicCompletionIntegers K) y) :
    y ∈ w.1.adicCompletionIntegers L := by
  have h2 : IsIntegral (w.1.adicCompletionIntegers L) y := hy.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.1.adicCompletionIntegers L)
    (K := w.1.adicCompletion L)).1 h2
  rw [← hz]
  exact z.2

variable (θ : (w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L))

theorem theta_mem {y : Lw} (hy : y ∈ w.1.adicCompletionIntegers L) : θ y ∈ w.1.adicCompletionIntegers L := by
  apply mem_of_isIntegral K L v w
  exact (isIntegral_of_mem K L v w hy).map (θ.restrictScalars (v.adicCompletionIntegers K)).toAlgHom

theorem ramificationIdx_ne_zero' :
    Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal ≠ 0 := by
  intro he
  have h := HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w 0
  rw [he, pow_zero, map_zero, map_zero] at h
  exact zero_ne_one h

theorem norm_theta_le (y : Lw) : ‖θ y‖ ≤ ‖y‖ := by
  by_cases hy : y = 0
  · rw [hy, map_zero]
  set e : ℕ := Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal with he_def
  have he : e ≠ 0 := ramificationIdx_ne_zero' K L v w

  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v
    ((Valued.v y : WithZero (Multiplicative ℤ))⁻¹)
  have hvx : (Valued.v (algebraMap Kv Lw x) : WithZero (Multiplicative ℤ)) = Valued.v ((y ^ e)⁻¹) := by
    change Valued.v (w.adicCompletionSemialgHom K L x) = _
    rw [HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w x, hx, map_inv₀, map_pow, inv_pow]
  have hnx : ‖algebraMap Kv Lw x‖ = ‖(y ^ e)⁻¹‖ :=
    le_antisymm ((Valued.toNormedField.norm_le_iff).2 hvx.le) ((Valued.toNormedField.norm_le_iff).2 hvx.ge)
  have hye : ‖y ^ e‖ ≠ 0 := by rw [norm_pow]; exact pow_ne_zero _ (norm_ne_zero_iff.2 hy)

  have hz : y ^ e * algebraMap Kv Lw x ∈ w.1.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff, norm_mul, hnx,
      norm_inv, mul_inv_cancel₀ hye]
  have hθz := theta_mem K L v w θ hz
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff, map_mul,
    AlgEquiv.commutes, map_pow, norm_mul, hnx, norm_inv, norm_pow, norm_pow, ← div_eq_mul_inv,
    ← div_pow, pow_le_one_iff_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)) he,
    div_le_one (norm_pos_iff.2 hy)] at hθz
  exact hθz

theorem norm_theta (y : Lw) : ‖θ y‖ = ‖y‖ := by
  refine le_antisymm (norm_theta_le K L v w θ y) ?_
  have := norm_theta_le K L v w θ.symm (θ y)
  rwa [AlgEquiv.symm_apply_apply] at this

end Ws31.S3b
p2m_reactivate "P2MW.S_AutomorphicForm_norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one.Ws31 P2MW.S_AutomorphicForm_norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one.Ws31.S3b"
p2m_reactivate "P2MW.S_AutomorphicForm_norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one.Ws31"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (c : w.1.adicCompletion L) (hc : ‖c‖ ≠ 1) (y : w.1.adicCompletion L) :
    ‖θ y - c * y‖ = ‖y‖ * max 1 ‖c‖ := by
  have hθ := Ws31.S3b.norm_theta K L v w θ y
  by_cases hy : y = 0
  · subst hy; simp
  have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hne : ‖θ y‖ ≠ ‖-(c * y)‖ := by
    rw [norm_neg, norm_mul, hθ]
    intro h
    exact hc (mul_right_cancel₀ hy0.ne' (by rw [one_mul]; exact h)).symm
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_neg, norm_mul, hθ]
  rcases lt_or_gt_of_ne hc with h1 | h1
  · rw [max_eq_left h1.le, mul_one, max_eq_left]
    exact mul_le_of_le_one_left hy0.le h1.le
  · rw [max_eq_right h1.le, max_eq_right, mul_comm]
    exact le_mul_of_one_le_left hy0.le h1.le

end S_AutomorphicForm_norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one
end P2MW
export P2MW.S_AutomorphicForm_norm_algEquiv_sub_mul_eq_norm_mul_max_of_norm_ne_one (solution)
