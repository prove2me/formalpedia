-- Prove2me | solution 1 for AlgebraicCurve.Divisor.pushforwardAlong_liesOver_of_liesOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/2e2850ec-f904-59d5-81ad-ebec8e3b6e31

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_liesOver_of_liesOver

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_liesOver_of_liesOver.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along Divisor.pushforwardAlong Divisor.pushforward Divisor.pushforward_apply Place Place.ext Divisor HasPrincipalDivisors IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed Place.exists_comap_algebraMap_eq_of_constantFieldExtension"
namespace HBCAux
p2m_open "AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem mem_restrictAlong_iff (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (f : F) :
    f ∈ (w.restrictAlong φ hφ).toValuationSubring ↔ φ f ∈ w.toValuationSubring :=
  Iff.rfl

theorem inertiaDegAlong_eq_one [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h

theorem pushforwardAlong_apply [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K F'] [DecidableEq (Place K F)]
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (D : Divisor K F') (v : Place K F) :
    Divisor.pushforwardAlong φ hφ D v = ∑ w ∈ D.support, if w.restrictAlong φ hφ = v then D w else 0 := by
  have h1 : ∀ w : Place K F', (w.inertiaDegAlong φ hφ : ℤ) = 1 := fun w => by
    rw [inertiaDegAlong_eq_one φ hφ w, Nat.cast_one]
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  show Divisor.pushforward F D v = _
  rw [Divisor.pushforward_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1w : (w.inertiaDeg F : ℤ) = 1 := h1 w
  by_cases hw : w.restrict F = v
  · rw [if_pos hw, if_pos (show w.restrictAlong φ hφ = v from hw), h1w, mul_one]
  · rw [if_neg hw, if_neg (show ¬ w.restrictAlong φ hφ = v from hw)]

end AlgebraicCurve.HBCAux

theorem solution
    (K F F' E FE F'E : Type*) [Field K] [Field F] [Field F'] [Field E] [Field FE] [Field F'E]
    [Algebra K F] [Algebra K F'] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E] [IsScalarTower K E F'E] [IsScalarTower K F' F'E]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K x ∧ FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE : ∃ x : FE, Transcendental E x ∧ FiniteDimensional ↥(IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hfgE' : ∃ x : F'E, Transcendental E x ∧ FiniteDimensional ↥(IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K F'] [AlgebraicCurve.IsCurveOver E FE] [AlgebraicCurve.IsCurveOver E F'E]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    [AlgebraicCurve.HasPrincipalDivisors K F'] [AlgebraicCurve.HasPrincipalDivisors E F'E]
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (φE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral)
    (hcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (D : AlgebraicCurve.Divisor K F') (DE : AlgebraicCurve.Divisor E F'E)
    (hover : ∀ (w' : AlgebraicCurve.Place E F'E) (w : AlgebraicCurve.Place K F'),
      w'.toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring → DE w' = D w)
    (hoff : ∀ w' : AlgebraicCurve.Place E F'E,
      (∀ w : AlgebraicCurve.Place K F', w'.toValuationSubring.comap (algebraMap F' F'E) ≠ w.toValuationSubring) → DE w' = 0) :
    (∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
        v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring →
        AlgebraicCurve.Divisor.pushforwardAlong φE hφE DE v' = AlgebraicCurve.Divisor.pushforwardAlong φ hφ D v) ∧
    (∀ v' : AlgebraicCurve.Place E FE,
        (∀ v : AlgebraicCurve.Place K F, v'.toValuationSubring.comap (algebraMap F FE) ≠ v.toValuationSubring) →
        AlgebraicCurve.Divisor.pushforwardAlong φE hφE DE v' = 0) := by
  classical

  have hsq : ∀ (w' : AlgebraicCurve.Place E F'E) (w : AlgebraicCurve.Place K F'),
      w'.toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring →
      (w'.restrictAlong φE hφE).toValuationSubring.comap (algebraMap F FE)
        = (w.restrictAlong φ hφ).toValuationSubring := by
    intro w' w hw
    ext f
    constructor
    · intro hf
      have h1 : φE (algebraMap F FE f) ∈ w'.toValuationSubring :=
        (HBCAux.mem_restrictAlong_iff φE hφE w' _).mp (ValuationSubring.mem_comap.mp hf)
      rw [hcomm] at h1
      have h2 : φ f ∈ w.toValuationSubring := by
        rw [← hw]
        exact ValuationSubring.mem_comap.mpr h1
      exact (HBCAux.mem_restrictAlong_iff φ hφ w f).mpr h2
    · intro hf
      have h2 : φ f ∈ w.toValuationSubring := (HBCAux.mem_restrictAlong_iff φ hφ w f).mp hf
      rw [← hw] at h2
      have h1 : algebraMap F' F'E (φ f) ∈ w'.toValuationSubring :=
        ValuationSubring.mem_comap.mp h2
      rw [← hcomm] at h1
      exact ValuationSubring.mem_comap.mpr ((HBCAux.mem_restrictAlong_iff φE hφE w' _).mpr h1)

  have hunder : ∀ w' : AlgebraicCurve.Place E F'E, DE w' ≠ 0 →
      ∃ w : AlgebraicCurve.Place K F', w'.toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring := by
    intro w' hne
    by_contra h
    push Not at h
    exact hne (hoff w' h)
  refine ⟨?_, ?_⟩
  ·
    intro v' v hv
    rw [HBCAux.pushforwardAlong_apply, HBCAux.pushforwardAlong_apply, ← Finset.sum_filter, ← Finset.sum_filter]

    have hPv := AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F E FE hfg hfgE hgen v
    have huniq_v : ∀ Q' : AlgebraicCurve.Place E FE,
        Q'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring → Q' = v' := fun Q' hQ' =>
      (hPv.choose_spec.2.2 Q' hQ').trans (hPv.choose_spec.2.2 v' hv).symm

    have hPw := fun w : AlgebraicCurve.Place K F' =>
      AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F' E F'E hfg' hfgE' hgen' w
    let lift : AlgebraicCurve.Place K F' → AlgebraicCurve.Place E F'E := fun w => (hPw w).choose
    have hlift : ∀ w, (lift w).toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring :=
      fun w => (hPw w).choose_spec.1
    have hlift_uniq : ∀ (w : AlgebraicCurve.Place K F') (Q' : AlgebraicCurve.Place E F'E),
        Q'.toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring → Q' = lift w :=
      fun w Q' hQ' => (hPw w).choose_spec.2.2 Q' hQ'
    symm
    refine Finset.sum_bij (fun w _ => lift w) ?_ ?_ ?_ ?_
    ·
      intro w hw
      rw [Finset.mem_filter] at hw ⊢
      have hval : DE (lift w) = D w := hover _ _ (hlift w)
      refine ⟨Finsupp.mem_support_iff.mpr (by rw [hval]; exact Finsupp.mem_support_iff.mp hw.1), ?_⟩
      apply huniq_v
      rw [hsq _ _ (hlift w), hw.2]
    ·
      intro w₁ hw₁ w₂ hw₂ h
      have h' : lift w₁ = lift w₂ := h
      apply AlgebraicCurve.Place.ext
      rw [← hlift w₁, ← hlift w₂, h']
    ·
      intro w' hw'
      rw [Finset.mem_filter] at hw'
      have hne : DE w' ≠ 0 := Finsupp.mem_support_iff.mp hw'.1
      have hw := hunder w' hne
      let w : AlgebraicCurve.Place K F' := hw.choose
      have hww' : w'.toValuationSubring.comap (algebraMap F' F'E) = w.toValuationSubring := hw.choose_spec
      refine ⟨w, ?_, (hlift_uniq w w' hww').symm⟩
      rw [Finset.mem_filter]
      refine ⟨Finsupp.mem_support_iff.mpr (by rw [← hover _ _ hww']; exact hne), ?_⟩
      apply AlgebraicCurve.Place.ext
      rw [← hsq _ _ hww', hw'.2, hv]
    ·
      intro w hw
      exact (hover _ _ (hlift w)).symm
  ·
    intro v' hv'
    rw [HBCAux.pushforwardAlong_apply]
    refine Finset.sum_eq_zero fun w' _ => ?_
    by_cases h : w'.restrictAlong φE hφE = v'
    · rw [if_pos h]
      by_contra hne
      have hw := hunder w' hne
      apply hv' (hw.choose.restrictAlong φ hφ)
      rw [← h]
      exact hsq _ _ hw.choose_spec
    · rw [if_neg h]

end S_AlgebraicCurve_Divisor_pushforwardAlong_liesOver_of_liesOver
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_pushforwardAlong_liesOver_of_liesOver (solution)
