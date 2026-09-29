-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_apply_le_mul_prod_of_isSemiLocalFactorization_of_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2cd097cc-4afd-5837-aed9-7993833fe2db

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
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_AutomorphicForm_exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_uniformizerIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_apply_le_mul_prod_of_isSemiLocalFactorization_of_apply_ne_zero
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace R1CharPeel

open NumberField.TateGlobal AutomorphicForm

variable {L : Type} [Field L] [NumberField L]

def ideleNormHom (L : Type) [Field L] [NumberField L] : (AdeleRing (𝓞 L) L)ˣ →* ℝ :=
  (NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 L) L))

theorem iN_eq_hom (x : (AdeleRing (𝓞 L) L)ˣ) : ideleNorm L x = ideleNormHom L x := rfl

theorem iN_mul (x y : (AdeleRing (𝓞 L) L)ˣ) :
    ideleNorm L (x * y) = ideleNorm L x * ideleNorm L y := by
  simp only [iN_eq_hom, map_mul]

theorem iN_one : ideleNorm L (1 : (AdeleRing (𝓞 L) L)ˣ) = 1 := by
  simp only [iN_eq_hom, map_one]

theorem iN_inv (x : (AdeleRing (𝓞 L) L)ˣ) : ideleNorm L x⁻¹ = (ideleNorm L x)⁻¹ := by
  have h : ideleNorm L x⁻¹ * ideleNorm L x = 1 := by rw [← iN_mul, inv_mul_cancel, iN_one]
  exact eq_inv_of_mul_eq_one_left h

theorem iN_pow (x : (AdeleRing (𝓞 L) L)ˣ) (n : ℕ) : ideleNorm L (x ^ n) = ideleNorm L x ^ n := by
  simp only [iN_eq_hom, map_pow]

theorem iN_prod {ι : Type*} (T : Finset ι) (f : ι → (AdeleRing (𝓞 L) L)ˣ) :
    ideleNorm L (∏ i ∈ T, f i) = ∏ i ∈ T, ideleNorm L (f i) := by
  simp only [iN_eq_hom, map_prod]

theorem mem_normOneIdeles_iff' (x : (AdeleRing (𝓞 L) L)ˣ) : x ∈ normOneIdeles L ↔ ideleNorm L x = 1 := by
  rw [normOneIdeles, MonoidHom.mem_ker, ideleNorm]
  constructor
  · intro h; rw [h]; rfl
  · intro h; exact_mod_cast h

theorem mul_inv_mem_normOneIdeles_of_ideleNorm_eq {a b : (AdeleRing (𝓞 L) L)ˣ}
    (h : ideleNorm L a = ideleNorm L b) : a * b⁻¹ ∈ normOneIdeles L := by
  rw [mem_normOneIdeles_iff', iN_mul, iN_inv, h, mul_inv_cancel₀ (ideleNorm_pos b).ne']

def modChar (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) : (AdeleRing (𝓞 L) L)ˣ →* ℝ where
  toFun z := ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖
  map_one' := by
    have h : (⟨1, Subgroup.mem_top (1 : (AdeleRing (𝓞 L) L)ˣ)⟩ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)) = 1 :=
      rfl
    rw [h, map_one, Units.val_one, norm_one]
  map_mul' a b := by
    have h : (⟨a * b, Subgroup.mem_top (a * b)⟩ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)) =
        ⟨a, Subgroup.mem_top a⟩ * ⟨b, Subgroup.mem_top b⟩ := rfl
    rw [h, map_mul, Units.val_mul, norm_mul]

variable (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)

theorem modChar_apply (z : (AdeleRing (𝓞 L) L)ˣ) :
    modChar ξL z = ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ := rfl

theorem modChar_pos (z : (AdeleRing (𝓞 L) L)ˣ) : 0 < modChar ξL z := by
  rw [modChar_apply]
  exact norm_pos_iff.mpr (Units.ne_zero _)

theorem modChar_nonneg (z : (AdeleRing (𝓞 L) L)ˣ) : 0 ≤ modChar ξL z := (modChar_pos ξL z).le

theorem modChar_mul_inv (z : (AdeleRing (𝓞 L) L)ˣ) : modChar ξL z * modChar ξL z⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem modChar_inv (z : (AdeleRing (𝓞 L) L)ˣ) : modChar ξL z⁻¹ = (modChar ξL z)⁻¹ :=
  eq_inv_of_mul_eq_one_right (modChar_mul_inv ξL z)

theorem modChar_principal
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (η : Lˣ) : modChar ξL (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom η) = 1 := by
  have hmem : Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom η ∈
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range := ⟨η, rfl⟩
  have h := hξt _ hmem
  rw [modChar_apply, h, Units.val_one, norm_one]

theorem continuous_modChar
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) :
    Continuous (modChar ξL) :=
  continuous_norm.comp hξc

theorem modChar_eq_one_of_mem_normOneIdeles
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (x : (AdeleRing (𝓞 L) L)ˣ) (hx : x ∈ normOneIdeles L) : modChar ξL x = 1 := by

  obtain ⟨Kc, hKc, -, hrep⟩ :=
    NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul L

  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn
    (f := fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) hξc.continuousOn

  have hbound : ∀ y ∈ normOneIdeles L, modChar ξL y ≤ B := by
    intro y hy
    obtain ⟨η, κ, hκ, rfl⟩ := hrep y hy
    rw [map_mul, modChar_principal ξL hξt η, one_mul]
    exact hB κ hκ

  have hle : ∀ y ∈ normOneIdeles L, modChar ξL y ≤ 1 := by
    intro y hy
    by_contra h
    rw [not_le] at h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
    have hyn : y ^ n ∈ normOneIdeles L := pow_mem hy n
    have := hbound _ hyn
    rw [map_pow] at this
    exact absurd (hn.trans_le this) (lt_irrefl _)
  have h1 : modChar ξL x ≤ 1 := hle x hx
  have h2 : modChar ξL x⁻¹ ≤ 1 := hle x⁻¹ (inv_mem hx)
  rw [modChar_inv] at h2
  have h3 : 1 ≤ modChar ξL x := by
    rwa [inv_le_one₀ (modChar_pos ξL x)] at h2
  exact le_antisymm h1 h3

theorem modChar_eq_of_ideleNorm_eq
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    {a b : (AdeleRing (𝓞 L) L)ˣ} (h : ideleNorm L a = ideleNorm L b) : modChar ξL a = modChar ξL b := by
  have h1 : modChar ξL (a * b⁻¹) = 1 :=
    modChar_eq_one_of_mem_normOneIdeles ξL hξc hξt _ (mul_inv_mem_normOneIdeles_of_ideleNorm_eq h)
  have : a = a * b⁻¹ * b := by rw [inv_mul_cancel_right]
  rw [this, map_mul, h1, one_mul]

omit [NumberField L] in
theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![(a : A), 1]) = a
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem det_heckeGen (w : HeightOneSpectrum (𝓞 L)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w) = uniformizerIdele L w := by
  show Matrix.GeneralLinearGroup.det (diagOne _) = _
  rw [det_diagOne]
  rfl

theorem ideleNorm_det_heckeGen (w : HeightOneSpectrum (𝓞 L)) :
    ideleNorm L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) =
      ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [det_heckeGen, NumberField.TateGlobal.ideleNorm_uniformizerIdele]

theorem absNorm_smul_ideal {K : Type} [Field K] [Algebra K L] (σ : L ≃ₐ[K] L) (I : Ideal (𝓞 L)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  rw [Ideal.pointwise_smul_def, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I _
    (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ) rfl).toEquiv).symm

theorem det_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z) = z ^ 2 := by
  show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) z) = z ^ 2
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

def unitOfIcc {m M : ℝ} (hm : 0 < m) (r : Set.Icc m M) : ℝ≥0ˣ :=
  Units.mk0 (Real.toNNReal (r : ℝ)) (ne_of_gt (Real.toNNReal_pos.mpr (hm.trans_le r.2.1)))

theorem coe_unitOfIcc {m M : ℝ} (hm : 0 < m) (r : Set.Icc m M) :
    (((unitOfIcc hm r : ℝ≥0ˣ) : ℝ≥0) : ℝ) = r := by
  show ((Real.toNNReal (r : ℝ)) : ℝ) = r
  exact Real.coe_toNNReal _ (hm.trans_le r.2.1).le

theorem continuous_unitOfIcc {m M : ℝ} (hm : 0 < m) : Continuous (unitOfIcc (M := M) hm) := by
  rw [Units.continuous_iff]
  have hval : Continuous fun r : Set.Icc m M => Real.toNNReal (r : ℝ) :=
    continuous_real_toNNReal.comp continuous_subtype_val
  refine ⟨hval, ?_⟩
  have h0 : ∀ r : Set.Icc m M, Real.toNNReal (r : ℝ) ≠ 0 := fun r =>
    ne_of_gt (Real.toNNReal_pos.mpr (hm.trans_le r.2.1))
  have : (fun r : Set.Icc m M => (((unitOfIcc hm r)⁻¹ : ℝ≥0ˣ) : ℝ≥0)) =
      fun r : Set.Icc m M => (Real.toNNReal (r : ℝ))⁻¹ := by
    funext r
    rw [Units.val_inv_eq_inv_val]
    rfl
  rw [this]
  exact hval.inv₀ h0

theorem exists_bound_modChar_section
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (s : ℝ≥0ˣ →* (AdeleRing (𝓞 L) L)ˣ) (hsc : Continuous s) {m M : ℝ} (hm : 0 < m) :
    ∃ B : ℝ, ∀ r : Set.Icc m M, modChar ξL (s (unitOfIcc hm r)) ≤ B := by
  have hcont : Continuous fun r : Set.Icc m M =>
      ((ξL ⟨s (unitOfIcc hm r), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) :=
    hξc.comp (hsc.comp (continuous_unitOfIcc hm))
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Set.Icc m M)).exists_bound_of_continuousOn hcont.continuousOn
  exact ⟨B, fun r => hB r (Set.mem_univ r)⟩

omit [NumberField L] [Field L] in
theorem sqrt_prod_pow_eq {ι : Type*} (T : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (k j : ι → ℕ) :
    (∏ i ∈ T, Real.sqrt (x i) ^ k i * x i ^ j i) ^ 2 = ∏ i ∈ T, x i ^ (k i + 2 * j i) := by
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k i) 2, pow_mul, Real.sq_sqrt (hx i), pow_add,
    mul_comm (j i) 2]

end R1CharPeel

end

open R1CharPeel NumberField.TateGlobal AutomorphicForm in
open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      ∃ A : ℝ, 0 ≤ A ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∀ (t : GL (Fin 2) L) (y : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
        φ (y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ≠ 0 →
        ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ ≤
          A * ∏ v ∈ T,
            (Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ^ ks v *
              ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ^ js v) := by
  intro T _hT _hSL ws w' hw' ϖs hϖs hϖs0 ns rTs hrTs zs hzs

  obtain ⟨m, M, hm, hmM⟩ :=
    AutomorphicForm.exists_pos_forall_mul_prod_le_ideleNorm_det_le_of_isSemiLocalFactorization_of_apply_ne_zero
      K L S φa φS T ws ϖs hϖs hϖs0 ns rTs hrTs zs hzs

  obtain ⟨s, hsc, hsn, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq L
  obtain ⟨B, hB⟩ := exists_bound_modChar_section ξL hξc s hsc (M := M) hm
  refine ⟨Real.sqrt (max B 0), Real.sqrt_nonneg _, ?_⟩
  intro ks js φ φf hfac t y z hne

  set χ : (AdeleRing (𝓞 L) L)ˣ →* ℝ := modChar ξL with hχ
  set P : ℝ := ∏ v ∈ T, (((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℝ)⁻¹) ^ (ks v + 2 * js v) with hP
  set ξv : HeightOneSpectrum (𝓞 K) → ℝ := fun v =>
    χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v))) with hξv

  change χ z ≤ Real.sqrt (max B 0) * ∏ v ∈ T, Real.sqrt (ξv v) ^ ks v * ξv v ^ js v

  have hNpos : ∀ w : HeightOneSpectrum (𝓞 L), (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by
    intro w
    have h1 : 1 < Ideal.absNorm w.asIdeal := by
      refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨?_, ?_⟩
      · rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
      · rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
    exact_mod_cast (zero_lt_one.trans h1)
  have hPpos : 0 < P := by
    rw [hP]
    exact Finset.prod_pos fun v _ => pow_pos (inv_pos.mpr (hNpos _)) _

  set g : AdelicGL2 (𝓞 L) L := y⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
      AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * y) with hg
  have hdet : ideleNorm L (Matrix.GeneralLinearGroup.det g) = ideleNorm L z ^ 2 := by
    rw [hg, map_mul, map_mul, map_inv, iN_mul, iN_mul, iN_inv,
      AutomorphicForm.ideleNorm_det_globalPoints, AutomorphicForm.ideleNorm_det_sigmaAdelicAct,
      map_mul, iN_mul, det_centralScalar, iN_pow, mul_one]
    have hy : ideleNorm L (Matrix.GeneralLinearGroup.det y) ≠ 0 := (ideleNorm_pos _).ne'
    field_simp

  obtain ⟨hlow, hupp⟩ := hmM ks js φ φf hfac g hne
  rw [hdet] at hlow hupp

  set r₀ : ℝ := ideleNorm L z ^ 2 / P with hr₀
  have hr₀mem : r₀ ∈ Set.Icc m M := by
    refine ⟨?_, ?_⟩
    · rw [hr₀, le_div_iff₀ hPpos]; exact hlow
    · rw [hr₀, div_le_iff₀ hPpos]; exact hupp
  set r : Set.Icc m M := ⟨r₀, hr₀mem⟩ with hr

  set b : (AdeleRing (𝓞 L) L)ˣ := s (unitOfIcc hm r) *
      ∏ v ∈ T, Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)) ^ (ks v + 2 * js v) with hb
  have hNeq : ∀ v ∈ T, ((Ideal.absNorm (w' v).asIdeal : ℕ) : ℝ) = ((Ideal.absNorm (ws v).1.asIdeal : ℕ) : ℝ) := by
    intro v hv
    rw [hw' v hv, absNorm_smul_ideal]
  have hbnorm : ideleNorm L b = ideleNorm L (z ^ 2) := by
    rw [hb, iN_mul, hsn, coe_unitOfIcc, iN_prod, iN_pow]
    have hprod : ∏ v ∈ T, ideleNorm L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' v)) ^
        (ks v + 2 * js v)) = P := by
      rw [hP]
      refine Finset.prod_congr rfl fun v hv => ?_
      rw [iN_pow, ideleNorm_det_heckeGen, hNeq v hv]
    rw [hprod]
    show r₀ * P = ideleNorm L z ^ 2
    rw [hr₀, div_mul_cancel₀ _ hPpos.ne']

  have hχsq : χ z ^ 2 = χ (s (unitOfIcc hm r)) * ∏ v ∈ T, ξv v ^ (ks v + 2 * js v) := by
    rw [← map_pow, ← modChar_eq_of_ideleNorm_eq ξL hξc hξt hbnorm, hb, map_mul, map_prod]
    simp only [map_pow]
    rfl

  have hξv0 : ∀ v, 0 ≤ ξv v := fun v => modChar_nonneg ξL _
  have hprod0 : 0 ≤ ∏ v ∈ T, ξv v ^ (ks v + 2 * js v) :=
    Finset.prod_nonneg fun v _ => pow_nonneg (hξv0 v) _
  have hsqle : χ z ^ 2 ≤ max B 0 * ∏ v ∈ T, ξv v ^ (ks v + 2 * js v) := by
    rw [hχsq]
    exact mul_le_mul_of_nonneg_right ((hB r).trans (le_max_left _ _)) hprod0
  have hR0 : 0 ≤ ∏ v ∈ T, Real.sqrt (ξv v) ^ ks v * ξv v ^ js v :=
    Finset.prod_nonneg fun v _ => mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (pow_nonneg (hξv0 v) _)
  have hAR0 : 0 ≤ Real.sqrt (max B 0) * ∏ v ∈ T, Real.sqrt (ξv v) ^ ks v * ξv v ^ js v :=
    mul_nonneg (Real.sqrt_nonneg _) hR0
  rw [← pow_le_pow_iff_left₀ (modChar_nonneg ξL z) hAR0 two_ne_zero, mul_pow,
    Real.sq_sqrt (le_max_right _ _), sqrt_prod_pow_eq T ξv hξv0 ks js]
  exact hsqle

end S_AutomorphicForm_exists_forall_norm_apply_le_mul_prod_of_isSemiLocalFactorization_of_apply_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_apply_le_mul_prod_of_isSemiLocalFactorization_of_apply_ne_zero (solution)
