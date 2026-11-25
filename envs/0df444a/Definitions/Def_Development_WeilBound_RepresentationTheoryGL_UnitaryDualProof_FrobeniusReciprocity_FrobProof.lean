-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_FrobProof
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_FrobProof
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:32:33.559747+00:00
-- url     : https://prove2.me/theorems/6261d27e-f8ca-4328-a171-28a3cb725c5b
-- title:
--   Frob Proof
-- statement:
--   Definitions and structural lemmas for Frob Proof, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/FrobeniusReciprocity/FrobProof.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_TrivSymmApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousSectionQuotientStatement
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_FrobeniusReciprocity_HaarDistr
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzBruhatCharacterIntegralOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHaarRightInvariantStatement
import Theorems.Thm_GlobalTheory_T_unimodular_haar_right_invariant
import Theorems.Thm_PositivityTheory_PfBern_Frob_eq_fap
import Theorems.Thm_PositivityTheory_PfBern_Frob_fap_smul
import Theorems.Thm_PositivityTheory_PfBern_Frob_intB_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_mem_eqv
import Theorems.Thm_PositivityTheory_PfBern_Frob_rtr_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_triv_apply
import Theorems.Thm_PositivityTheory_PfBern_Frob_triv_symm_apply
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_eq_const_mul_integral_char
import Theorems.Thm_PositivityTheory_RgUd_T2_HaarDistr_mulLC_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.PfBern.Frob.intB_apply
attribute [local simp] PositivityTheory.PfBern.Frob.rtr_apply
attribute [local simp] PositivityTheory.PfBern.Frob.triv_apply
attribute [local simp] PositivityTheory.PfBern.Frob.triv_symm_apply
attribute [local simp] PositivityTheory.RgUd.T2.HaarDistr.mulLC_apply


set_option autoImplicit false
noncomputable section
open Set MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil
namespace PositivityTheory.PfBern.Frob
section Main
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [LocallyCompactSpace H]
  {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X] [MulAction G X] [ContinuousSMul G X]
  {p : X → G ⧸ H} (hp : ∀ (g : G) (x : X), p (g • x) = g • p x) (σ : Sec H)
  (hpc : Continuous p) (μH : Measure H) [μH.IsHaarMeasure] [LocallyCompactSpace (Fib p)]
  (μG : Measure G) [μG.IsHaarMeasure] (χ : G →* ℂˣ)
theorem fibSmul_fibSmul (a b : H) (z : Fib p) :
    fibSmul hp a (fibSmul hp b z) = fibSmul hp (a * b) z :=
  Subtype.ext (by simp [smul_smul])
theorem int_chi_right [μG.IsMulRightInvariant] (α : SB G) (h0 : G) :
    ∫ g, (α : G → ℂ) (g * h0⁻¹) * (χ g : ℂ) ∂μG =
      (χ h0 : ℂ) * ∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG := by
  calc ∫ g, (α : G → ℂ) (g * h0⁻¹) * (χ g : ℂ) ∂μG
      = ∫ g, (α : G → ℂ) (g * h0 * h0⁻¹) * (χ (g * h0) : ℂ) ∂μG :=
        (integral_mul_right_eq_self (fun g => (α : G → ℂ) (g * h0⁻¹) * (χ g : ℂ)) h0).symm
    _ = ∫ g, ((α : G → ℂ) g * (χ g : ℂ)) * (χ h0 : ℂ) ∂μG := by
        congr 1; funext g
        simp only [mul_inv_cancel_right, map_mul, Units.val_mul]
        ring
    _ = _ := by rw [integral_mul_const, mul_comm]
theorem transl_fap (g0 : G) (α : SB G) (φ : SB (Fib p)) :
    transl g0 (fap hp σ hpc μH α φ) = fap hp σ hpc μH (transl g0 α) φ := by
  apply eq_fap
  intro g z
  rw [transl_apply, smul_smul, fap_smul]
  simp only [transl_apply, smul_eq_mul, mul_assoc]
theorem fap_translF (uH : IsUnimod H) (h0 : H) (α : SB G) (φ : SB (Fib p)) :
    fap hp σ hpc μH α (translF hp h0 φ) =
      fap hp σ hpc μH (pullHomeo (Homeomorph.mulRight ((h0 : G)⁻¹)) α) φ := by
  haveI : SecondCountableTopology H := inferInstanceAs (SecondCountableTopology (H : Set G))
  haveI := GlobalTheory.T.unimodular_haar_right_invariant H uH μH
  apply eq_fap
  intro g z
  rw [fap_smul]
  refine Eq.trans ?_ (integral_mul_right_eq_self (μ := μH) _ h0)
  congr 1
  funext h
  simp [translF_apply, pullHomeo_apply, Homeomorph.coe_mulRight, fibSmul_fibSmul, mul_assoc]
theorem eval_fap (hχ : Continuous fun g => (χ g : ℂ)) (ξ : eqv X χ) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) (α : SB G) (φ : SB (Fib p)) :
    (ξ : Distr X) (fap hp σ hpc μH α φ) =
      (∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG) * (ξ : Distr X) (fap hp σ hpc μH α0 φ) := by
  obtain ⟨c, hc⟩ := PositivityTheory.RgUd.T2.HaarDistr.eq_const_mul_integral_char G μG χ hχ ((ξ : Distr X) ∘ₗ (avg hp σ hpc μH ∘ₗ tensL φ))
    (fun g α => by
      show (ξ : Distr X) (fap hp σ hpc μH (transl g α) φ) =
        (χ g : ℂ) * (ξ : Distr X) (fap hp σ hpc μH α φ)
      rw [← transl_fap]
      exact (mem_eqv.1 ξ.2) g _)
  have h1 : (ξ : Distr X) (fap hp σ hpc μH α φ) = c * ∫ g, (α : G → ℂ) g * (χ g : ℂ) ∂μG := hc α
  have h2 : (ξ : Distr X) (fap hp σ hpc μH α0 φ) =
      c * ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG := hc α0
  rw [h1, h2, hα0, mul_one, mul_comm]
def FrMap (uG : IsUnimod G) (uH : IsUnimod H) (hχ : Continuous fun g => (χ g : ℂ)) (α0 : SB G)
    (hα0 : ∫ g, (α0 : G → ℂ) g * (χ g : ℂ) ∂μG = 1) :
    eqv X χ →ₗ[ℂ] eqvF hp (χ.comp H.subtype) where
  toFun ξ := ⟨(ξ : Distr X) ∘ₗ (avg hp σ hpc μH ∘ₗ tensR α0), fun h0 φ => by
    haveI := GlobalTheory.T.unimodular_haar_right_invariant G uG μG
    show (ξ : Distr X) (fap hp σ hpc μH α0 (translF hp h0 φ)) =
      (χ (h0 : G) : ℂ) * (ξ : Distr X) (fap hp σ hpc μH α0 φ)
    rw [fap_translF hp σ hpc μH uH, eval_fap hp σ hpc μH μG χ hχ ξ α0 hα0]
    congr 1
    have := int_chi_right μG χ α0 (h0 : G)
    rw [hα0, mul_one] at this
    exact this⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def intG (hχ : Continuous fun g => (χ g : ℂ)) : SB (G × Fib p) →ₗ[ℂ] SB (Fib p) :=
  intB μG (fun g => (χ g : ℂ)) hχ ∘ₗ pullHomeo (Homeomorph.prodComm (Fib p) G)
end Main
end PositivityTheory.PfBern.Frob


