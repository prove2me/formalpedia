-- Prove2me | solution 1 for AlgebraicCurve.Place.ramificationIndexAlong_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ae3610fc-c696-54bb-9ea2-b822be0f8810

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_smul

noncomputable section

open AlgebraicCurve

namespace FibreSolG

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring := Iff.rfl

theorem mem_smul_iff (σ : F' ≃ₐ[K] F') (w : Place K F') (x : F') :
    x ∈ (σ • w).toValuationSubring ↔ σ.symm x ∈ w.toValuationSubring := by
  rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem deg_restrictAlong_mul_inertiaDegAlong (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    (w.restrictAlong φ hφ).deg * w.inertiaDegAlong φ hφ = w.deg := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.deg_restrict_mul_inertiaDeg

variable (α β : F →ₐ[K] F') (hα : α.toRingHom.IsIntegral) (hβ : β.toRingHom.IsIntegral)
  (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x))
include h

theorem sq_symm (x : F) : σ.symm (α x) = β (τ.symm x) := by
  apply σ.injective
  rw [AlgEquiv.apply_symm_apply, ← h, AlgEquiv.apply_symm_apply]

theorem smul_restrictAlong (W : Place K F') :
    (σ • W).restrictAlong α hα = τ • (W.restrictAlong β hβ) := by
  ext f
  rw [mem_restrictAlong_iff, mem_smul_iff, sq_symm α β σ τ h,
    show f ∈ (τ • W.restrictAlong β hβ).toValuationSubring ↔ τ.symm f ∈ (W.restrictAlong β hβ).toValuationSubring from by
      rw [Place.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]; rfl,
    mem_restrictAlong_iff]

theorem ramificationIndexAlong_smul (W : Place K F') :
    (σ • W).ramificationIndexAlong α = W.ramificationIndexAlong β := by
  show sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ (σ • W).ord (α f) = n}
    = sInf {n : ℕ | 0 < n ∧ ∃ f : F, f ≠ 0 ∧ W.ord (β f) = n}
  congr 1
  ext n
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨f, hf, hn⟩
    refine ⟨τ.symm f, by simpa using hf, ?_⟩
    rw [← hn, ← sq_symm α β σ τ h f, ← Place.ord_smul σ W (σ.symm (α f)), AlgEquiv.apply_symm_apply]
  · rintro ⟨g, hg, hn⟩
    refine ⟨τ g, by simpa using hg, ?_⟩
    rw [← hn, h g, Place.ord_smul]

theorem inertiaDegAlong_smul (W : Place K F') (hdeg : (W.restrictAlong β hβ).deg = 1) :
    (σ • W).inertiaDegAlong α hα = W.inertiaDegAlong β hβ := by
  have h1 := deg_restrictAlong_mul_inertiaDegAlong (K := K) α hα (σ • W)
  have h2 := deg_restrictAlong_mul_inertiaDegAlong (K := K) β hβ W
  rw [smul_restrictAlong α β hα hβ σ τ h, Place.deg_smul, hdeg, one_mul, Place.deg_smul] at h1
  rw [hdeg, one_mul] at h2
  rw [h1, h2]

end Generic

end FibreSolG

end

open AlgebraicCurve in
theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (α β : F →ₐ[K] F') (σ : F' ≃ₐ[K] F') (τ : F ≃ₐ[K] F) (h : ∀ x, α (τ x) = σ (β x)) (W : Place K F') : (σ • W).ramificationIndexAlong α = W.ramificationIndexAlong β :=
  FibreSolG.ramificationIndexAlong_smul α β σ τ h W

end S_AlgebraicCurve_Place_ramificationIndexAlong_smul
end P2MW
export P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_smul (solution)
