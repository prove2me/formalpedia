-- Prove2me | solution 1 for AlgebraicCurve.Pic0.conorm_correspondence_eq_correspondence_conorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f16f5101-69fd-5635-ba77-45800c3c85d4

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_liesOver_of_liesOver
import Theorems.Thm_AlgebraicCurve_Divisor_pushforwardAlong_liesOver_of_liesOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_conorm_correspondence_eq_correspondence_conorm

set_option autoImplicit false

open AlgebraicCurve

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
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (φE ψE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
    (hcommφ : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hcommψ : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))

    (hFI : AlgebraicCurve.FundamentalIdentityAlong K φ hφ) (hfin : AlgebraicCurve.FiniteAlong K ψ)
    (hN : AlgebraicCurve.NormFormulaAlong K ψ hfin)
    (hFIE : AlgebraicCurve.FundamentalIdentityAlong E φE hφE) (hfinE : AlgebraicCurve.FiniteAlong E ψE)
    (hNE : AlgebraicCurve.NormFormulaAlong E ψE hfinE)

    (ι : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 E FE)
    (hpin : ∀ (D : AlgebraicCurve.Divisor.degZero (K := K) (F := F)) (D' : AlgebraicCurve.Divisor.degZero (K := E) (F := FE)),
      (∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
        v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring →
          (D' : AlgebraicCurve.Divisor E FE) v' = (D : AlgebraicCurve.Divisor K F) v) →
      (∀ v' : AlgebraicCurve.Place E FE,
        (∀ v : AlgebraicCurve.Place K F, v'.toValuationSubring.comap (algebraMap F FE) ≠ v.toValuationSubring) →
          (D' : AlgebraicCurve.Divisor E FE) v' = 0) →
      ι (AlgebraicCurve.Pic0.mk D) = AlgebraicCurve.Pic0.mk D')
    (hex : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F), ∃ D' : AlgebraicCurve.Divisor.degZero (K := E) (F := FE),
      (∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
        v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring →
          (D' : AlgebraicCurve.Divisor E FE) v' = (D : AlgebraicCurve.Divisor K F) v) ∧
      (∀ v' : AlgebraicCurve.Place E FE,
        (∀ v : AlgebraicCurve.Place K F, v'.toValuationSubring.comap (algebraMap F FE) ≠ v.toValuationSubring) →
          (D' : AlgebraicCurve.Divisor E FE) v' = 0)) :
    ∀ x : AlgebraicCurve.Pic0 K F,
      ι (AlgebraicCurve.Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) =
        AlgebraicCurve.Pic0.correspondence φE ψE hφE hψE hFIE hfinE hNE (ι x) := by
  intro x
  obtain ⟨D, rfl⟩ := AlgebraicCurve.Pic0.mk_surjective x
  obtain ⟨DE, hover, hoff⟩ := hex D

  obtain ⟨hoverP, hoffP⟩ :=
    AlgebraicCurve.Divisor.pullbackAlong_liesOver_of_liesOver K F F' E FE F'E hfg hfg' hfgE hfgE' hgen hgen'
      φ hφ φE hφE hcommφ (D : AlgebraicCurve.Divisor K F) (DE : AlgebraicCurve.Divisor E FE) hover hoff

  obtain ⟨hover', hoff'⟩ :=
    AlgebraicCurve.Divisor.pushforwardAlong_liesOver_of_liesOver K F F' E FE F'E hfg hfg' hfgE hfgE' hgen hgen'
      ψ hψ ψE hψE hcommψ (AlgebraicCurve.Divisor.pullbackAlong φ hφ (D : AlgebraicCurve.Divisor K F))
      (AlgebraicCurve.Divisor.pullbackAlong φE hφE (DE : AlgebraicCurve.Divisor E FE)) hoverP hoffP
  rw [hpin D DE hover hoff, AlgebraicCurve.Pic0.correspondence_mk, AlgebraicCurve.Pic0.correspondence_mk]
  refine hpin _ _ (fun v' v hv => ?_) (fun v' hv => ?_)
  · rw [AlgebraicCurve.Pic0.coe_degZeroCorrespondence, AlgebraicCurve.Pic0.coe_degZeroCorrespondence,
      AlgebraicCurve.Divisor.correspondence_apply, AlgebraicCurve.Divisor.correspondence_apply]
    exact hover' v' v hv
  · rw [AlgebraicCurve.Pic0.coe_degZeroCorrespondence, AlgebraicCurve.Divisor.correspondence_apply]
    exact hoff' v' hv

#print axioms solution

end S_AlgebraicCurve_Pic0_conorm_correspondence_eq_correspondence_conorm
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_conorm_correspondence_eq_correspondence_conorm (solution)
