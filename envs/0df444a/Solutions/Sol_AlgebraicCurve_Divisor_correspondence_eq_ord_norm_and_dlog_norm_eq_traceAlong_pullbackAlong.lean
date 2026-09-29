-- Prove2me | solution 1 for AlgebraicCurve.Divisor.correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/afdf12b2-6469-5059-be11-950f6492920c

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_Differentials
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_AlgebraicCurve_traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm
import Theorems.Thm_AlgebraicCurve_traceDiff_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong

set_option autoImplicit false

noncomputable section

open KaehlerDifferential TensorProduct

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along FundamentalIdentityAlong FiniteAlong NormFormulaAlong Divisor.pullbackAlong Divisor.pushforwardAlong Divisor.correspondence Divisor.correspondence_apply Pic0.degZeroCorrespondence Pic0.correspondence Pic0.correspondence_mk Place.ord_restrictAlong Divisor.pullbackAlong_apply SeparableAlong Place Divisor Divisor.degZero HasPrincipalDivisors Pic Pic0 Pic0.mk Pic0.mk_surjective Pic0.torsion Pic0.mem_torsion Differential.pullbackAlong Differential.pullbackAlong_D Differential.pullbackAlong_smul Differential.traceAlong Differential.traceAlong_smul_pullbackAlong Differential.correspondence Differential.correspondence_apply traceDiff traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm traceDiff_apply"
p2m_open "AlgebraicCurve"

namespace DlogCorrespondence

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mul_pullbackAlong_eq_ord [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) {n : ℤ} {D : Divisor K F} {f : F}
    (hD : ∀ v : Place K F, n * D v = v.ord f) (w : Place K F') :
    n * Divisor.pullbackAlong φ hφ D w = w.ord (φ f) := by
  rw [Divisor.pullbackAlong_apply, mul_left_comm, hD, Place.ord_restrictAlong φ hφ]

theorem mul_pushforwardAlong_eq_ord (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) {n : ℤ} {E : Divisor K F'} {g : F'}
    (hg : g ≠ 0) (hE : ∀ w : Place K F', n * E w = w.ord g) (v : Place K F) :
    n * Divisor.pushforwardAlong ψ hψ E v =
      v.ord (letI := algebraAlong ψ; Algebra.norm F g) := by
  letI := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI := isIntegral_along ψ hψ
  haveI : Module.Finite F F' := hfin
  have hE' : ∀ w : Place K F', (n • E) w = w.ord g := fun w => by
    rw [Finsupp.smul_apply, smul_eq_mul, hE w]
  have h := hN g hg (n • E) hE' v
  rw [map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h
  exact h

theorem norm_along_ne_zero (ψ : F →ₐ[K] F') (hfin : FiniteAlong K ψ) {g : F'} (hg : g ≠ 0) :
    (letI := algebraAlong ψ; Algebra.norm F g) ≠ 0 := by
  letI := algebraAlong ψ
  haveI : Module.Finite F F' := hfin
  exact Algebra.norm_ne_zero_iff.mpr hg

theorem mul_correspondence_eq_ord [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) {n : ℤ} {D : Divisor K F} {f : F}
    (hf : f ≠ 0) (hD : ∀ v : Place K F, n * D v = v.ord f) (v : Place K F) :
    n * Divisor.correspondence φ ψ hφ hψ D v =
      v.ord (letI := algebraAlong ψ; Algebra.norm F (φ f)) := by
  rw [Divisor.correspondence_apply]
  exact mul_pushforwardAlong_eq_ord ψ hψ hfin hN ((map_ne_zero φ).mpr hf)
    (mul_pullbackAlong_eq_ord φ hφ hD) v

theorem pullbackAlong_dlog (φ : F →ₐ[K] F') (f : F) :
    Differential.pullbackAlong φ (f⁻¹ • D K F f) = (φ f)⁻¹ • D K F' (φ f) := by
  rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_D, map_inv₀]

theorem traceAlong_apply_eq_traceDiff (ψ : F →ₐ[K] F') (hsep : SeparableAlong K ψ)
    (ω' : Ω[F'⁄K]) :
    Differential.traceAlong ψ ω' =
      (letI := algebraAlong ψ; haveI := isScalarTower_along ψ; traceDiff K F F' ω') := by
  letI := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI : Algebra.IsSeparable F F' := hsep
  haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  obtain ⟨t, rfl⟩ := (tensorKaehlerEquivOfFormallyEtale K F F').surjective ω'
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul u ω =>
      have htm : tensorKaehlerEquivOfFormallyEtale K F F' (u ⊗ₜ ω) =
          u • Differential.pullbackAlong ψ ω := by
        rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
        rfl
      rw [htm, Differential.traceAlong_smul_pullbackAlong ψ hsep]
      exact (AlgebraicCurve.traceDiff_apply K F F' u ω).symm

theorem traceAlong_dlog (ψ : F →ₐ[K] F') (hsep : SeparableAlong K ψ) (g : F') :
    Differential.traceAlong ψ (g⁻¹ • D K F' g) =
      (letI := algebraAlong ψ; Algebra.norm F g)⁻¹ •
        D K F (letI := algebraAlong ψ; Algebra.norm F g) := by
  letI := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI : Algebra.IsSeparable F F' := hsep
  rw [traceAlong_apply_eq_traceDiff ψ hsep]
  exact AlgebraicCurve.traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm K F F' g

theorem traceAlong_pullbackAlong_dlog (φ ψ : F →ₐ[K] F') (hsep : SeparableAlong K ψ) (f : F) :
    Differential.traceAlong ψ (Differential.pullbackAlong φ (f⁻¹ • D K F f)) =
      (letI := algebraAlong ψ; Algebra.norm F (φ f))⁻¹ •
        D K F (letI := algebraAlong ψ; Algebra.norm F (φ f)) := by
  rw [pullbackAlong_dlog, traceAlong_dlog ψ hsep]

theorem differentialCorrespondence_dlog (φ ψ : F →ₐ[K] F') (hsep : SeparableAlong K ψ) (f : F) :
    Differential.correspondence ψ φ (f⁻¹ • D K F f) =
      (letI := algebraAlong ψ; Algebra.norm F (φ f))⁻¹ •
        D K F (letI := algebraAlong ψ; Algebra.norm F (φ f)) := by
  rw [Differential.correspondence_apply, traceAlong_pullbackAlong_dlog φ ψ hsep]

theorem correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
    [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) (hsep : SeparableAlong K ψ)
    (n : ℤ) (D : Divisor K F) (f : F) (hf : f ≠ 0)
    (hD : ∀ v : Place K F, n * D v = v.ord f) :
    ∃ g : F, g = (letI := algebraAlong ψ; Algebra.norm F (φ f)) ∧ g ≠ 0 ∧
      (∀ v : Place K F, n * Divisor.correspondence φ ψ hφ hψ D v = v.ord g) ∧
      g⁻¹ • KaehlerDifferential.D K F g =
        Differential.traceAlong ψ
          (Differential.pullbackAlong φ (f⁻¹ • KaehlerDifferential.D K F f)) :=
  ⟨(letI := algebraAlong ψ; Algebra.norm F (φ f)), rfl,
    norm_along_ne_zero ψ hfin ((map_ne_zero φ).mpr hf),
    mul_correspondence_eq_ord φ ψ hφ hψ hfin hN hf hD,
    (traceAlong_pullbackAlong_dlog φ ψ hsep f).symm⟩

theorem exists_rep_of_mem_torsion {p : ℕ} {x : Pic0 K F} (hx : x ∈ Pic0.torsion K F p) :
    ∃ (D : Divisor.degZero (K := K) (F := F)) (f : F), Pic0.mk D = x ∧ f ≠ 0 ∧
      ∀ v : Place K F, (p : ℤ) * (D : Divisor K F) v = v.ord f := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.mem_torsion] at hx
  have hmk : (Pic0.mk ((p : ℤ) • D) : Pic0 K F) = 0 := by
    rw [Pic0.mk, QuotientAddGroup.mk_zsmul]; exact hx
  rw [Pic0.mk, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hmk
  obtain ⟨f, hf, hDf⟩ := hmk
  refine ⟨D, f, rfl, hf, fun v => ?_⟩
  rw [← hDf v]
  rfl

theorem dlogMap_correspondence [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) (hsep : SeparableAlong K ψ) (p : ℕ)
    (δ : Pic0 K F → Ω[F⁄K])
    (hδ : ∀ (x : Pic0 K F) (E : Divisor.degZero (K := K) (F := F)) (g : F), Pic0.mk E = x →
      g ≠ 0 → (∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) → δ x = g⁻¹ • D K F g)
    {x : Pic0 K F} (hx : x ∈ Pic0.torsion K F p) :
    δ (Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) =
      Differential.traceAlong ψ (Differential.pullbackAlong φ (δ x)) := by
  obtain ⟨D, f, rfl, hf, hD⟩ := exists_rep_of_mem_torsion hx
  obtain ⟨g, -, hg0, hg, hdlog⟩ :=
    correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong φ ψ hφ hψ hfin hN hsep
      (p : ℤ) (D : Divisor K F) f hf hD
  rw [hδ (Pic0.mk D) D f rfl hf hD, ← hdlog, Pic0.correspondence_mk]
  exact hδ _ (Pic0.degZeroCorrespondence φ ψ hφ hψ hFI D) g rfl hg0 hg

theorem dlogMap_correspondence' [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) (hsep : SeparableAlong K ψ) (p : ℕ)
    (δ : Pic0 K F → Ω[F⁄K])
    (hδ : ∀ (x : Pic0 K F) (E : Divisor.degZero (K := K) (F := F)) (g : F), Pic0.mk E = x →
      g ≠ 0 → (∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) → δ x = g⁻¹ • D K F g)
    {x : Pic0 K F} (hx : x ∈ Pic0.torsion K F p) :
    δ (Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) = Differential.correspondence ψ φ (δ x) := by
  rw [Differential.correspondence_apply]
  exact dlogMap_correspondence φ ψ hφ hψ hFI hfin hN hsep p δ hδ hx

theorem correspondence_mem_torsion [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) (p : ℕ) {x : Pic0 K F} (hx : x ∈ Pic0.torsion K F p) :
    Pic0.correspondence φ ψ hφ hψ hFI hfin hN x ∈ Pic0.torsion K F p := by
  rw [Pic0.mem_torsion] at hx ⊢
  rw [← map_zsmul, hx, map_zero]

theorem dlogMap_torsion_correspondence [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) (hsep : SeparableAlong K ψ) (p : ℕ)
    (δ : Pic0.torsion K F p → Ω[F⁄K])
    (hδ : ∀ (x : Pic0.torsion K F p) (E : Divisor.degZero (K := K) (F := F)) (g : F),
      Pic0.mk E = (x : Pic0 K F) → g ≠ 0 →
      (∀ v : Place K F, (p : ℤ) * (E : Divisor K F) v = v.ord g) → δ x = g⁻¹ • D K F g)
    (x y : Pic0.torsion K F p)
    (hxy : (y : Pic0 K F) = Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) :
    δ y = Differential.traceAlong ψ (Differential.pullbackAlong φ (δ x)) := by
  obtain ⟨D, f, hDx, hf, hD⟩ := exists_rep_of_mem_torsion x.2
  obtain ⟨g, -, hg0, hg, hdlog⟩ :=
    correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong φ ψ hφ hψ hfin hN hsep
      (p : ℤ) (D : Divisor K F) f hf hD
  rw [hδ x D f hDx hf hD, ← hdlog]
  refine hδ y (Pic0.degZeroCorrespondence φ ψ hφ hψ hFI D) g ?_ hg0 hg
  rw [hxy, ← hDx, Pic0.correspondence_mk]

end DlogCorrespondence

end AlgebraicCurve

end

theorem solution
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfin : AlgebraicCurve.FiniteAlong K ψ) (hN : AlgebraicCurve.NormFormulaAlong K ψ hfin)
    (hsep : AlgebraicCurve.SeparableAlong K ψ)
    (n : ℤ) (D : AlgebraicCurve.Divisor K F) (f : F) (hf : f ≠ 0)
    (hD : ∀ v : AlgebraicCurve.Place K F, n * D v = v.ord f) :
    ∃ g : F, g = (letI := AlgebraicCurve.algebraAlong ψ; Algebra.norm F (φ f)) ∧ g ≠ 0 ∧
      (∀ v : AlgebraicCurve.Place K F,
        n * AlgebraicCurve.Divisor.correspondence φ ψ hφ hψ D v = v.ord g) ∧
      g⁻¹ • KaehlerDifferential.D K F g =
        AlgebraicCurve.Differential.traceAlong ψ
          (AlgebraicCurve.Differential.pullbackAlong φ (f⁻¹ • KaehlerDifferential.D K F f)) :=
  AlgebraicCurve.DlogCorrespondence.correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
    φ ψ hφ hψ hfin hN hsep n D f hf hD

end S_AlgebraicCurve_Divisor_correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_correspondence_eq_ord_norm_and_dlog_norm_eq_traceAlong_pullbackAlong (solution)
