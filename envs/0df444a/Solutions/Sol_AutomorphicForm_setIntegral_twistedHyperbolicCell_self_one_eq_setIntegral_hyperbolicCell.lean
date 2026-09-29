-- Prove2me | solution 1 for AutomorphicForm.setIntegral_twistedHyperbolicCell_self_one_eq_setIntegral_hyperbolicCell
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2a1b7b7b-81cb-53c1-8237-bda8e62bd64d

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_twistedHyperbolicCell_self_one_eq_setIntegral_hyperbolicCell

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace BridgeKKHyp

open AutomorphicForm LT.TwistedNorm Polynomial

variable (K : Type) [Field K] [NumberField K]

theorem sigmaAdelicAct_one (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) K K) (g : AdelicGL2 (𝓞 K) K) :
    sigmaAdelicAct K K D 1 g = g := by
  unfold AutomorphicForm.sigmaAdelicAct
  rw [map_one]
  ext i j
  rfl

theorem isCentralType_conj_iff (P : GL (Fin 2) K) (M : Matrix (Fin 2) (Fin 2) K) :
    IsCentralType ((P : Matrix (Fin 2) (Fin 2) K) * M * ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) ↔
      IsCentralType M := by
  have hPP : ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * (P : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPP' : (P : Matrix (Fin 2) (Fin 2) K) * ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have : M = ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        ((P : Matrix (Fin 2) (Fin 2) K) * M * ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
        (P : Matrix (Fin 2) (Fin 2) K) := by
      rw [← mul_assoc, ← mul_assoc, hPP, one_mul, mul_assoc, hPP, mul_one]
    rw [this, hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP']

theorem isHyperbolicType_conj_iff (P : GL (Fin 2) K) (M : Matrix (Fin 2) (Fin 2) K) :
    IsHyperbolicType ((P : Matrix (Fin 2) (Fin 2) K) * M * ((P⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) ↔
      IsHyperbolicType M := by
  unfold AutomorphicForm.IsHyperbolicType
  rw [Matrix.coe_units_inv, Matrix.charpoly_units_conj P M]

theorem mem_hyperbolicCell_of_isConj {γ δ : GL (Fin 2) K} (h : IsConj γ δ) (hγ : γ ∈ hyperbolicCell K) :
    δ ∈ hyperbolicCell K := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [mem_hyperbolicCell_iff] at hγ ⊢
  rw [← hc, Units.val_mul, Units.val_mul]
  exact (isHyperbolicType_conj_iff K c (γ : Matrix (Fin 2) (Fin 2) K)).mpr hγ

theorem isNormRep_one_iff (γ δ : GL (Fin 2) K) :
    IsNormRep (1 : K ≃ₐ[K] K) γ δ ↔ ∃ P : GL (Fin 2) K, P⁻¹ * δ * P = γ := by
  unfold LT.TwistedNorm.IsNormRep
  have h1 : sigmaNormPow (Matrix.GeneralLinearGroup.map ((1 : K ≃ₐ[K] K) : K →+* K)) (Module.finrank K K) δ = δ := by
    rw [Module.finrank_self]
    simp [LT.TwistedNorm.sigmaNormPow, LT.TwistedNorm.sigmaPartialNorm]
  have h2 : Matrix.GeneralLinearGroup.map (algebraMap K K) γ = γ := by
    ext i j; rfl
  rw [h1, h2]

theorem normClass_setOf_eq (hgen : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K)) :
    {δ : GL (Fin 2) K | ∃ γ : GL (Fin 2) K, γ ∈ hyperbolicCell K ∧
        normClassMap hgen (SigmaConjClasses.mk (1 : K ≃ₐ[K] K) δ) = ConjClasses.mk γ} = hyperbolicCell K := by
  ext δ
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨γ, hγ, hmap⟩
    rw [normClassMap_mk] at hmap
    have hconj : IsConj (normRep hgen δ) γ := ConjClasses.mk_eq_mk_iff_isConj.mp hmap
    obtain ⟨P, hP⟩ := (isNormRep_one_iff K _ δ).mp (isNormRep_normRep hgen δ)

    obtain ⟨d, hd⟩ := isConj_iff.mp hconj
    have hδ : IsConj γ δ := by
      refine isConj_iff.mpr ⟨P * d⁻¹, ?_⟩
      rw [← hd, ← hP]
      group
    exact mem_hyperbolicCell_of_isConj K hδ hγ
  · intro hδ
    refine ⟨δ, hδ, normClassMap_mk_eq_of_isNormRep hgen ((isNormRep_one_iff K δ δ).mpr ⟨1, by simp⟩)⟩

theorem borel_setOf_eq :
    {γ : GL (Fin 2) K | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
        Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1} =
    {γ : GL (Fin 2) K | (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
        (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1} := by
  ext γ
  simp only [Set.mem_setOf_eq, Algebra.norm_self, MonoidHom.id_apply]

end BridgeKKHyp

open AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (Φ₁ Φ₂ : Set (AdelicGL2 (𝓞 K) K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) K K)
    (hgen : ∀ τ : K ≃ₐ[K] K, τ ∈ Subgroup.zpowers (1 : K ≃ₐ[K] K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    ∀ R : ℝ,
      ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
        (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ {δ : GL (Fin 2) K | ∃ γ : GL (Fin 2) K,
              γ ∈ AutomorphicForm.hyperbolicCell K ∧
              LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk (1 : K ≃ₐ[K] K) δ) = ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K δ *
                AutomorphicForm.sigmaAdelicAct K K D 1 (AutomorphicForm.centralScalar (𝓞 K) K z * x))) -
          Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
          (@AutomorphicForm.constantTerm _
            (productionPinsOf K Φ₁ (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
              (fun w => heckeGen (𝓞 K) K w) (adelicBox K)).nS _ _
            (productionPinsOf K Φ₁ (fun M => levelOne (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
              (fun w => heckeGen (𝓞 K) K w) (adelicBox K)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) K |
              (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1) ≠ 1},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K δ * AutomorphicForm.sigmaAdelicAct K K D 1 y)))
          (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
        (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              (AutomorphicForm.adelicKernelHyperbolicPart K φ x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf K Φ₂ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                  (productionPinsOf K Φ₂ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                    (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                    φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  intro R
  have hact : ∀ g, AutomorphicForm.sigmaAdelicAct K K D 1 g = g := BridgeKKHyp.sigmaAdelicAct_one K D
  simp only [hact, BridgeKKHyp.normClass_setOf_eq K hgen, BridgeKKHyp.borel_setOf_eq K,
    AutomorphicForm.adelicKernelHyperbolicPart, productionPinsOf]
  rfl

end S_AutomorphicForm_setIntegral_twistedHyperbolicCell_self_one_eq_setIntegral_hyperbolicCell
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_twistedHyperbolicCell_self_one_eq_setIntegral_hyperbolicCell (solution)
