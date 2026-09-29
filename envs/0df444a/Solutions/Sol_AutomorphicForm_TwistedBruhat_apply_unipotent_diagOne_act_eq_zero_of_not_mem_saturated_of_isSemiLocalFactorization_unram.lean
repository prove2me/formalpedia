-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.apply_unipotent_diagOne_act_eq_zero_of_not_mem_saturated_of_isSemiLocalFactorization_unram
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b3f0896d-60c0-519b-ba8c-fd9cf7eeab3f

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
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Theorems.Thm_AutomorphicForm_baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact
import Theorems.Thm_AutomorphicForm_semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
import Theorems.Thm_AutomorphicForm_mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet
import Theorems.Thm_AutomorphicForm_TransversalMeasure_mem_saturatedUnits_of_forall_ne_valued_semiLocalUnitComponent_congr_mul_inv_eq_one_unram
import Theorems.Thm_TwistedUnipotentTerm_isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_TwistedBruhat_apply_unipotent_diagOne_act_eq_zero_of_not_mem_saturated_of_isSemiLocalFactorization_unram

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace G4SB

section Generic

variable {A : Type*} [CommRing A] {R : Set A}

theorem inv_mem_integralUnitsSet {g : GL (Fin 2) A} (hg : g ∈ AutomorphicForm.integralUnitsSet R) :
    g⁻¹ ∈ AutomorphicForm.integralUnitsSet R :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem mul_mem_integralUnitsSet (hadd : ∀ a ∈ R, ∀ b ∈ R, a + b ∈ R) (hmul : ∀ a ∈ R, ∀ b ∈ R, a * b ∈ R)
    {g h : GL (Fin 2) A} (hg : g ∈ AutomorphicForm.integralUnitsSet R)
    (hh : h ∈ AutomorphicForm.integralUnitsSet R) : g * h ∈ AutomorphicForm.integralUnitsSet R := by
  rw [AutomorphicForm.mem_integralUnitsSet] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact hadd _ (hmul _ (hg.1 i 0) _ (hh.1 0 j)) _ (hmul _ (hg.1 i 1) _ (hh.1 1 j))
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact hadd _ (hmul _ (hh.2 i 0) _ (hg.2 0 j)) _ (hmul _ (hh.2 i 1) _ (hg.2 1 j))

theorem map_mem_integralUnitsSet {B : Type*} [CommRing B] {R' : Set B} (f : A →+* B)
    (hf : ∀ a ∈ R, f a ∈ R') {g : GL (Fin 2) A} (hg : g ∈ AutomorphicForm.integralUnitsSet R) :
    Matrix.GeneralLinearGroup.map f g ∈ AutomorphicForm.integralUnitsSet R' := by
  rw [AutomorphicForm.mem_integralUnitsSet] at hg ⊢
  refine ⟨fun i j => hf _ (hg.1 i j), fun i j => ?_⟩
  rw [← map_inv]
  exact hf _ (hg.2 i j)

theorem upper_entries (x : A) (a c : Aˣ) :
    ((AutomorphicForm.unipotentGL2 x * NumberField.AdelicLevel.diagOne a *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 ∧
    ((AutomorphicForm.unipotentGL2 x * NumberField.AdelicLevel.diagOne a *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1 = c ∧
    ((AutomorphicForm.unipotentGL2 x * NumberField.AdelicLevel.diagOne a *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0 = a * c := by
  have hd : (NumberField.AdelicLevel.diagOne a : Matrix (Fin 2) (Fin 2) A) = !![(a : A), 0; 0, 1] := by
    ext i j
    rw [NumberField.AdelicLevel.diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp
  have hs : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      !![(c : A), 0; 0, (c : A)] := by
    ext i j
    show Matrix.diagonal (fun _ => (c : A)) i j = _
    fin_cases i <;> fin_cases j <;> simp
  rw [Units.val_mul, Units.val_mul, AutomorphicForm.unipotentGL2_coe, hd, hs]
  refine ⟨?_, ?_, ?_⟩ <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end Generic

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem add_mem_semiLocalIntegers {x y : L ⊗[K] v.adicCompletion K}
    (hx : x ∈ AutomorphicForm.semiLocalIntegers K L v) (hy : y ∈ AutomorphicForm.semiLocalIntegers K L v) :
    x + y ∈ AutomorphicForm.semiLocalIntegers K L v := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a + b, map_add _ _ _⟩

theorem mul_mem_semiLocalIntegers {x y : L ⊗[K] v.adicCompletion K}
    (hx : x ∈ AutomorphicForm.semiLocalIntegers K L v) (hy : y ∈ AutomorphicForm.semiLocalIntegers K L v) :
    x * y ∈ AutomorphicForm.semiLocalIntegers K L v := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨b, rfl⟩ := hy; exact ⟨a * b, map_mul _ _ _⟩

theorem congr_mem_semiLocalIntegers (σ : L ≃ₐ[K] L) {y : L ⊗[K] v.adicCompletion K}
    (hy : y ∈ AutomorphicForm.semiLocalIntegers K L v) :
    (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)) y ∈
      AutomorphicForm.semiLocalIntegers K L v := by
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact AutomorphicForm.zero_mem_semiLocalIntegers K L v
  | add z₁ z₂ h₁ h₂ => rw [map_add, map_add]; exact add_mem_semiLocalIntegers K L v h₁ h₂
  | tmul b c =>
    rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
    refine ⟨(galRestrict (𝓞 K) K L (𝓞 L) σ b) ⊗ₜ c, ?_⟩
    rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, algebraMap_galRestrict_apply]
    rfl

noncomputable def coord (w : v.Extension (𝓞 L)) : L ⊗[K] v.adicCompletion K →+* w.1.adicCompletion L :=
  (Pi.evalRingHom (fun w' : v.Extension (𝓞 L) => w'.1.adicCompletion L) w).comp
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toRingEquiv.toRingHom

theorem coord_apply (w : v.Extension (𝓞 L)) (y : L ⊗[K] v.adicCompletion K) :
    coord K L v w y = HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y w := rfl

theorem semiLocalUnitComponent_val (w : v.Extension (𝓞 L)) (u : (L ⊗[K] v.adicCompletion K)ˣ) :
    ((TwistedUnipotentTerm.semiLocalUnitComponent K L v w u : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) =
      coord K L v w (u : L ⊗[K] v.adicCompletion K) := rfl

theorem valued_eq_one_of_mem_of_inv_mem (w : v.Extension (𝓞 L)) (a : (w.1.adicCompletion L)ˣ)
    (h1 : (a : w.1.adicCompletion L) ∈ w.1.adicCompletionIntegers L)
    (h2 : ((a⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) ∈ w.1.adicCompletionIntegers L) :
    Valued.v (a : w.1.adicCompletion L) = 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  refine le_antisymm h1 ?_
  have hne : Valued.v (a : w.1.adicCompletion L) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact a.ne_zero
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hne)] at h2
  exact h2

theorem mem_integralUnits_of_mem (a : (L ⊗[K] v.adicCompletion K)ˣ)
    (h1 : (a : L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v)
    (h2 : ((a⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) ∈ AutomorphicForm.semiLocalIntegers K L v) :
    a ∈ AutomorphicForm.TransversalMeasure.integralUnits K L v := by
  rw [AutomorphicForm.TransversalMeasure.integralUnits, Submonoid.mem_units_iff]
  obtain ⟨x, hx⟩ := h1; obtain ⟨y, hy⟩ := h2
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

theorem semiLocalComponent_sigmaAdelicAct_mem [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L) {k : AutomorphicForm.AdelicGL2 (𝓞 L) L} (hk : k ∈ AutomorphicForm.adelicMaximalCompact L) :
    AutomorphicForm.semiLocalComponent K L v
        (NumberField.AdelicLevel.glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ k)) ∈
      AutomorphicForm.semiLocalIntegralSet K L v := by
  have hS1 := (AutomorphicForm.semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
    K L D σ v).2.2
  have hS0 := (AutomorphicForm.baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact
    K L v).2.2
  have aux : ∀ {k' : AutomorphicForm.AdelicGL2 (𝓞 L) L}, k' ∈ AutomorphicForm.adelicMaximalCompact L → ∀ i j,
      ((AutomorphicForm.semiLocalComponent K L v
        (NumberField.AdelicLevel.glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ k')) :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈
        AutomorphicForm.semiLocalIntegers K L v := by
    intro k' hk' i j
    rw [hS1 k' i j]
    exact congr_mem_semiLocalIntegers K L v σ ((AutomorphicForm.mem_integralUnitsSet.mp (hS0 k' hk')).1 i j)
  refine AutomorphicForm.mem_integralUnitsSet.mpr ⟨aux hk, fun i j => ?_⟩
  rw [← map_inv, ← map_inv, ← map_inv]
  exact aux (inv_mem hk) i j

end SemiLocal

section Key

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem key (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal = 1)
    (t ζ : (AdeleRing (𝓞 L) L)ˣ) (x : AdeleRing (𝓞 L) L) (w₁ : v.Extension (𝓞 L))
    (hU : ∀ w' : v.Extension (𝓞 L), w' ≠ w₁ →
      Matrix.GeneralLinearGroup.map (coord K L v w')
        (AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L
          (AutomorphicForm.unipotentGL2 x *
            NumberField.AdelicLevel.diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
            AutomorphicForm.centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ)))) ∈
        AutomorphicForm.integralUnitsSet (w'.1.adicCompletionIntegers L : Set (w'.1.adicCompletion L))) :
    AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t ∈
      AutomorphicForm.TransversalMeasure.saturatedUnits K L v := by
  classical
  set u := AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t with hu

  have hS1b := (AutomorphicForm.semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
    K L D σ v).2.1
  have hσu : AutomorphicForm.TransversalMeasure.semiLocalIdele K L v (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t) =
      Units.mapEquiv (Algebra.TensorProduct.congr σ
        (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv u := by
    apply Units.ext
    rw [hS1b t, Units.coe_mapEquiv]
    rfl
  have ha0 : AutomorphicForm.TransversalMeasure.semiLocalIdele K L v
      (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) =
      Units.mapEquiv (Algebra.TensorProduct.congr σ
        (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv u * u⁻¹ := by
    rw [map_mul, map_inv, hσu]
  apply AutomorphicForm.TransversalMeasure.mem_saturatedUnits_of_forall_ne_valued_semiLocalUnitComponent_congr_mul_inv_eq_one_unram
    K L σ hgen v hv u w₁
  intro w' hw'
  rw [← ha0]

  set a₀ : (AdeleRing (𝓞 L) L)ˣ := M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹ with ha₀
  set c₀ : (AdeleRing (𝓞 L) L)ˣ := M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ with hc₀
  have hM := hU w' hw'

  obtain ⟨e10, e11, e00⟩ := upper_entries x a₀ c₀

  set ζ' := TwistedUnipotentTerm.semiLocalUnitComponent K L v w' (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v c₀)
    with hζ'
  set a' := TwistedUnipotentTerm.semiLocalUnitComponent K L v w' (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v a₀)
    with ha'
  have hentry : ∀ i j : Fin 2,
      ((Matrix.GeneralLinearGroup.map (coord K L v w')
        (AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L
          (AutomorphicForm.unipotentGL2 x * NumberField.AdelicLevel.diagOne a₀ *
            AutomorphicForm.centralScalar (𝓞 L) L c₀))) : GL (Fin 2) (w'.1.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w'.1.adicCompletion L)) i j =
        coord K L v w' (AutomorphicForm.semiLocalEval K L v
          (((AutomorphicForm.unipotentGL2 x * NumberField.AdelicLevel.diagOne a₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c₀ : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2) := fun i j => rfl
  have h10 : ((Matrix.GeneralLinearGroup.map (coord K L v w')
        (AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L
          (AutomorphicForm.unipotentGL2 x * NumberField.AdelicLevel.diagOne a₀ *
            AutomorphicForm.centralScalar (𝓞 L) L c₀))) : GL (Fin 2) (w'.1.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w'.1.adicCompletion L)) 1 0 = 0 := by
    rw [hentry, e10]
    show coord K L v w' (AutomorphicForm.semiLocalEval K L v 0) = 0
    rw [map_zero, map_zero]
  have h11 : ((Matrix.GeneralLinearGroup.map (coord K L v w')
        (AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L
          (AutomorphicForm.unipotentGL2 x * NumberField.AdelicLevel.diagOne a₀ *
            AutomorphicForm.centralScalar (𝓞 L) L c₀))) : GL (Fin 2) (w'.1.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w'.1.adicCompletion L)) 1 1 = ζ' := by
    rw [hentry, e11]
    rfl
  have h00 : ((Matrix.GeneralLinearGroup.map (coord K L v w')
        (AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L
          (AutomorphicForm.unipotentGL2 x * NumberField.AdelicLevel.diagOne a₀ *
            AutomorphicForm.centralScalar (𝓞 L) L c₀))) : GL (Fin 2) (w'.1.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w'.1.adicCompletion L)) 0 0 = a' * ζ' := by
    rw [hentry, e00]
    show coord K L v w' (AutomorphicForm.semiLocalEval K L v ((a₀ : AdeleRing (𝓞 L) L).2 * (c₀ : AdeleRing (𝓞 L) L).2)) = _
    rw [map_mul, map_mul]
    rfl
  obtain ⟨-, haR, haiR⟩ := AutomorphicForm.mem_and_inv_mem_of_upperTriangular_mem_integralUnitsSet
    (w'.1.adicCompletionIntegers L : Set (w'.1.adicCompletion L))
    (fun a ha b hb => mul_mem ha hb) _ ζ' a' h10 h11 h00 hM
  rw [ha'] at haR haiR
  exact valued_eq_one_of_mem_of_inv_mem K L v w' _ haR haiR

end Key

end G4SB

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL)
    (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
    (ns : HeightOneSpectrum (𝓞 K) → ℕ)
    (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L))
    (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L))
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hfac : IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v))

    (Sτ : Finset (HeightOneSpectrum (𝓞 K)))
    (hSτ : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ Sτ ↔ (v ∈ S ∧ v ∉ T) ∨
        ∃ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v ∧
          (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1) :
    ∀ t : (AdeleRing (𝓞 L) L)ˣ, t ∉ AutomorphicForm.TransversalMeasure.saturated K L Sτ →
      ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ) (w : AdeleRing (𝓞 L) L),
        φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0 := by
  intro t ht k ζ w
  classical
  obtain ⟨-, -, -, hprod, hvan, hsplit⟩ := hfac

  have ht' : ∃ v₀, v₀ ∉ Sτ ∧ AutomorphicForm.TransversalMeasure.semiLocalIdele K L v₀ t ∉
      AutomorphicForm.TransversalMeasure.saturatedUnits K L v₀ := by
    by_contra h
    push_neg at h
    exact ht (fun v hv => h v hv)
  obtain ⟨v₀, hv₀S, hv₀sat⟩ := ht'
  have hnot := (not_congr (hSτ v₀)).mp hv₀S
  push_neg at hnot
  obtain ⟨hA, hB⟩ := hnot

  set g : AdelicGL2 (𝓞 L) L := (k : AdelicGL2 (𝓞 L) L)⁻¹ *
      unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
      diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
      centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
      AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L) with hg
  set W : AdelicGL2 (𝓞 L) L :=
      unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
      diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
      centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) with hW
  have hgW : g = (k : AdelicGL2 (𝓞 L) L)⁻¹ * W * AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L) := by
    rw [hg, hW]; simp only [mul_assoc]
  clear_value W
  rw [hsplit g]

  have hcompW : ∀ v : HeightOneSpectrum (𝓞 K),
      semiLocalComponent K L v (glFin (𝓞 L) L W) =
        semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
          semiLocalComponent K L v (glFin (𝓞 L) L g) *
          (semiLocalComponent K L v (glFin (𝓞 L) L
            (AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))))⁻¹ := by
    intro v
    rw [hgW]
    simp only [map_mul, map_inv]
    group
  by_cases hint : ∀ v ∉ S ∪ T, semiLocalComponent K L v (glFin (𝓞 L) L g) ∈ semiLocalIntegralSet K L v
  swap
  · push_neg at hint
    rw [hvan _ hint, mul_zero]

  have hS0 := AutomorphicForm.baseChangeAlgEquiv_semiLocalComponent_localEmbed_and_mem_semiLocalIntegers_iff_and_semiLocalComponent_mem_of_mem_adelicMaximalCompact
    K L v₀
  have hk_int : semiLocalComponent K L v₀ (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) ∈ semiLocalIntegralSet K L v₀ :=
    hS0.2.2 _ k.2
  have hσk_int := G4SB.semiLocalComponent_sigmaAdelicAct_mem K L v₀ D σ k.2
  have hRadd := fun a (ha : a ∈ semiLocalIntegers K L v₀) b (hb : b ∈ semiLocalIntegers K L v₀) =>
    G4SB.add_mem_semiLocalIntegers K L v₀ ha hb
  have hRmul := fun a (ha : a ∈ semiLocalIntegers K L v₀) b (hb : b ∈ semiLocalIntegers K L v₀) =>
    G4SB.mul_mem_semiLocalIntegers K L v₀ ha hb

  have hcoord_int : ∀ (w' : v₀.Extension (𝓞 L)) {m : GL (Fin 2) (L ⊗[K] v₀.adicCompletion K)},
      m ∈ semiLocalIntegralSet K L v₀ →
        Matrix.GeneralLinearGroup.map (G4SB.coord K L v₀ w') m ∈
          AutomorphicForm.integralUnitsSet (w'.1.adicCompletionIntegers L : Set (w'.1.adicCompletion L)) :=
    fun w' m hm => G4SB.map_mem_integralUnitsSet (G4SB.coord K L v₀ w')
      (fun a ha => by rw [G4SB.coord_apply]; exact (hS0.2.1 a).mp ha w') hm
  have hOadd : ∀ (w' : v₀.Extension (𝓞 L)), ∀ a ∈ (w'.1.adicCompletionIntegers L : Set (w'.1.adicCompletion L)),
      ∀ b ∈ (w'.1.adicCompletionIntegers L : Set (w'.1.adicCompletion L)),
        a + b ∈ (w'.1.adicCompletionIntegers L : Set (w'.1.adicCompletion L)) :=
    fun w' a ha b hb => (w'.1.adicCompletionIntegers L).add_mem _ _ ha hb
  have hOmul : ∀ (w' : v₀.Extension (𝓞 L)), ∀ a ∈ (w'.1.adicCompletionIntegers L : Set (w'.1.adicCompletion L)),
      ∀ b ∈ (w'.1.adicCompletionIntegers L : Set (w'.1.adicCompletion L)),
        a * b ∈ (w'.1.adicCompletionIntegers L : Set (w'.1.adicCompletion L)) :=
    fun w' a ha b hb => (w'.1.adicCompletionIntegers L).mul_mem _ _ ha hb
  by_cases hv₀ST : v₀ ∈ S ∪ T
  ·
    have hv₀T : v₀ ∈ T := by
      rcases Finset.mem_union.mp hv₀ST with hS' | hT''
      · exact hA hS'
      · exact hT''
    rw [hprod _ hint]
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero hv₀ST
    simp only [if_pos hv₀T]
    apply Finset.sum_eq_zero
    intro ι _
    apply Set.indicator_of_notMem
    intro hmem
    apply hv₀sat

    have hE1 : ∀ w' : v₀.Extension (𝓞 L), w' ≠ ws v₀ →
        ∀ X : GL (Fin 2) ((ws v₀).1.adicCompletion L),
          Matrix.GeneralLinearGroup.map (G4SB.coord K L v₀ w')
            (semiLocalComponent K L v₀ (AdelicDock.localEmbed (𝓞 L) L (ws v₀).1 X)) = 1 := by
      intro w' hw' X
      apply Units.ext
      ext i j
      show G4SB.coord K L v₀ w' (((semiLocalComponent K L v₀ (AdelicDock.localEmbed (𝓞 L) L (ws v₀).1 X)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] v₀.adicCompletion K)) i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j
      rw [G4SB.coord_apply]
      exact (hS0.1 (ws v₀) X i j).2 w' hw'
    refine G4SB.key K L D σ hgen v₀ hB t ζ (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) (ws v₀)
      (fun w' hw' => ?_)
    have hfac' : semiLocalComponent K L v₀ (glFin (𝓞 L) L W) =
        semiLocalComponent K L v₀ (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
          semiLocalComponent K L v₀ (AdelicDock.localEmbed (𝓞 L) L (ws v₀).1
            ((List.ofFn fun m => rTs v₀ (ι m)).prod * zs v₀ ^ js v₀)) *
          ((semiLocalComponent K L v₀ (AdelicDock.localEmbed (𝓞 L) L (ws v₀).1
            ((List.ofFn fun m => rTs v₀ (ι m)).prod * zs v₀ ^ js v₀)))⁻¹ *
            semiLocalComponent K L v₀ (glFin (𝓞 L) L g)) *
          (semiLocalComponent K L v₀ (glFin (𝓞 L) L
            (AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))))⁻¹ := by
      rw [hcompW v₀]; group
    rw [← hW, hfac', map_mul, map_mul, map_mul, map_inv, hE1 w' hw', mul_one]
    exact G4SB.mul_mem_integralUnitsSet (hOadd w') (hOmul w')
      (G4SB.mul_mem_integralUnitsSet (hOadd w') (hOmul w') (hcoord_int w' hk_int) (hcoord_int w' hmem))
      (G4SB.inv_mem_integralUnitsSet (hcoord_int w' hσk_int))
  ·
    exfalso
    apply hv₀sat
    have hg_int := hint v₀ hv₀ST
    have hW_int : semiLocalComponent K L v₀ (glFin (𝓞 L) L W) ∈ semiLocalIntegralSet K L v₀ := by
      rw [hcompW v₀]
      exact G4SB.mul_mem_integralUnitsSet hRadd hRmul (G4SB.mul_mem_integralUnitsSet hRadd hRmul hk_int hg_int)
        (G4SB.inv_mem_integralUnitsSet hσk_int)
    rcases isEmpty_or_nonempty (v₀.Extension (𝓞 L)) with hemp | ⟨⟨w₁⟩⟩
    ·
      have hIU := (TwistedUnipotentTerm.isCompact_isOpen_integralUnits_and_mem_iff_forall_valued_eq_one K L v₀).2.2
      have hu : AutomorphicForm.TransversalMeasure.semiLocalIdele K L v₀ t ∈
          AutomorphicForm.TransversalMeasure.integralUnits K L v₀ :=
        (hIU _).mpr fun w' => (IsEmpty.false w').elim
      exact ⟨_, hu, 1, ⟨1, map_one _⟩, mul_one _⟩
    · exact G4SB.key K L D σ hgen v₀ hB t ζ _ w₁ (fun w' _ => hcoord_int w' (hW.symm ▸ hW_int))

end S_AutomorphicForm_TwistedBruhat_apply_unipotent_diagOne_act_eq_zero_of_not_mem_saturated_of_isSemiLocalFactorization_unram
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_apply_unipotent_diagOne_act_eq_zero_of_not_mem_saturated_of_isSemiLocalFactorization_unram (solution)
