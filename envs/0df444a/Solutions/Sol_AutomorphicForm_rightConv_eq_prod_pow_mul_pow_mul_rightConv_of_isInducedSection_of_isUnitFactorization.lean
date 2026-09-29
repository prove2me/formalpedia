-- Prove2me | solution 1 for AutomorphicForm.rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e5a7fc7f-be19-51f1-815e-a6b8f036719a

import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_LocalGL2_iwasawa_decomposition
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

namespace HeckeShift

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private noncomputable def compAt (y : GL (Fin 2) (AdeleRing (𝓞 K) K)) : GL (Fin 2) (v.adicCompletion K) :=
  Units.map ((AdelicLevel.finAdeleEval (𝓞 K) K v).mapMatrix.toMonoidHom) (AdelicLevel.glFin (𝓞 K) K y)

private noncomputable def embAt (g : GL (Fin 2) (v.adicCompletion K)) : GL (Fin 2) (AdeleRing (𝓞 K) K) :=
  AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v g)

private theorem embAt_mul (g h : GL (Fin 2) (v.adicCompletion K)) : embAt K v (g * h) = embAt K v g * embAt K v h := by
  simp only [embAt, map_mul]

private theorem embAt_mul_comm (g : GL (Fin 2) (v.adicCompletion K)) (y : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hy : (AdelicLevel.finAdeleEval (𝓞 K) K v).mapMatrix
        ((AdelicLevel.adeleFin (𝓞 K) K).mapMatrix (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) = 1) :
    embAt K v g * y = y * embAt K v g := by
  apply Units.ext
  simp only [Units.val_mul, embAt, AdelicDock.coe_finEmbed]
  apply AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq
  · simp only [map_mul, AdelicDock.mapMatrix_arch_finMat, one_mul, mul_one]
  · simp only [map_mul, AdelicDock.mapMatrix_fin_finMat]
    apply AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq
    intro w
    by_cases hw : w = v
    · subst hw
      simp only [map_mul, hy, mul_one, one_mul]
    · have h1 : (AdelicLevel.finAdeleEval (𝓞 K) K w).mapMatrix
          ((AdelicDock.localEmbed (𝓞 K) K v g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) = 1 :=
        AdelicDock.mapMatrix_localMat_of_ne (𝓞 K) K v _ hw
      simp only [map_mul, h1, one_mul, mul_one]

end HeckeShift

namespace HeckeShift

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem compAt_mul (a b : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    compAt K v (a * b) = compAt K v a * compAt K v b := by
  simp only [compAt, map_mul]

private theorem compAt_inv (a : GL (Fin 2) (AdeleRing (𝓞 K) K)) : compAt K v a⁻¹ = (compAt K v a)⁻¹ := by
  simp only [compAt, map_inv]

private theorem compAt_embAt (g : GL (Fin 2) (v.adicCompletion K)) : compAt K v (embAt K v g) = g := by
  apply Units.ext
  simp only [compAt, embAt, AdelicDock.glFin_finEmbed, Units.coe_map]
  exact AdelicDock.mapMatrix_localMat_self (𝓞 K) K v _

private theorem coe_compAt (y : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    ((compAt K v y : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
      = (AdelicLevel.finAdeleEval (𝓞 K) K v).mapMatrix
          ((AdelicLevel.adeleFin (𝓞 K) K).mapMatrix (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) := by
  simp only [compAt, Units.coe_map]
  rfl

private theorem embAt_mul_comm_of_compAt_eq_one (g : GL (Fin 2) (v.adicCompletion K))
    (y : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hy : compAt K v y = 1) :
    embAt K v g * y = y * embAt K v g := by
  apply embAt_mul_comm
  rw [← coe_compAt, hy, Units.val_one]

private noncomputable def restAt (y : GL (Fin 2) (AdeleRing (𝓞 K) K)) : GL (Fin 2) (AdeleRing (𝓞 K) K) :=
  (embAt K v (compAt K v y))⁻¹ * y

private theorem compAt_restAt (y : GL (Fin 2) (AdeleRing (𝓞 K) K)) : compAt K v (restAt K v y) = 1 := by
  simp only [restAt, compAt_mul, compAt_inv, compAt_embAt, inv_mul_cancel]

private theorem embAt_compAt_mul_restAt (y : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    embAt K v (compAt K v y) * restAt K v y = y := by
  simp only [restAt, mul_inv_cancel_left]

end HeckeShift

namespace HeckeShift

open MeasureTheory

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private noncomputable def heckeShift {n : ℕ} (reps : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ :=
  fun z => ∑ i, f ((reps i)⁻¹ * z)

private theorem sum_apply_mul_reps_mul_eq (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    {n : ℕ} (reps : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K)) (c : ℂ)
    (heig : ∀ x, ∑ i, φ (x * reps i) = c * φ x)
    (hreps : ∀ i, ∃ r : GL (Fin 2) (v.adicCompletion K), reps i = embAt K v r)
    (Uv : Set (GL (Fin 2) (v.adicCompletion K)))
    (hfU : ∀ z, f z ≠ 0 → compAt K v z ∈ Uv)
    (hφU : ∀ x, ∀ u ∈ Uv, φ (x * embAt K v u) = φ x)
    (x z : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    (∑ i, φ (x * reps i * z)) * f z = c * φ (x * z) * f z := by
  by_cases hz : f z = 0
  · simp [hz]
  have hu : compAt K v z ∈ Uv := hfU z hz
  set z' := restAt K v z with hz'
  have hsplit : embAt K v (compAt K v z) * z' = z := embAt_compAt_mul_restAt K v z
  have hz'1 : compAt K v z' = 1 := compAt_restAt K v z
  have hcomm_u : embAt K v (compAt K v z) * z' = z' * embAt K v (compAt K v z) :=
    embAt_mul_comm_of_compAt_eq_one K v _ z' hz'1

  have hxz : φ (x * z) = φ (x * z') := by
    calc φ (x * z) = φ (x * (embAt K v (compAt K v z) * z')) := by rw [hsplit]
      _ = φ (x * z' * embAt K v (compAt K v z)) := by rw [hcomm_u, mul_assoc]
      _ = φ (x * z') := hφU _ _ hu

  have hterm : ∀ i, φ (x * reps i * z) = φ (x * z' * reps i) := by
    intro i
    obtain ⟨r, hr⟩ := hreps i
    have hcomm_r : embAt K v r * z' = z' * embAt K v r :=
      embAt_mul_comm_of_compAt_eq_one K v r z' hz'1
    calc φ (x * reps i * z)
        = φ (x * embAt K v r * (embAt K v (compAt K v z) * z')) := by rw [hr, hsplit]
      _ = φ (x * embAt K v r * (z' * embAt K v (compAt K v z))) := by rw [hcomm_u]
      _ = φ (x * embAt K v r * z' * embAt K v (compAt K v z)) := by rw [mul_assoc (x * embAt K v r)]
      _ = φ (x * embAt K v r * z') := hφU _ _ hu
      _ = φ (x * (z' * embAt K v r)) := by rw [mul_assoc, hcomm_r]
      _ = φ (x * z' * reps i) := by rw [hr, mul_assoc]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), heig (x * z'), hxz]

private theorem rightConv_heckeShift (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 K) K) (c : ℂ)
    (heig : ∀ x, ∑ i, φ (x * reps i) = c * φ x)
    (hreps : ∀ i, ∃ r : GL (Fin 2) (v.adicCompletion K), reps i = embAt K v r)
    (Uv : Set (GL (Fin 2) (v.adicCompletion K)))
    (hfU : ∀ z, f z ≠ 0 → compAt K v z ∈ Uv)
    (hφU : ∀ x, ∀ u ∈ Uv, φ (x * embAt K v u) = φ x) :
    AutomorphicForm.rightConv K φ (heckeShift K reps f) = c • AutomorphicForm.rightConv K φ f := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hint : ∀ (a : AdelicGL2 (𝓞 K) K) (F : AdelicGL2 (𝓞 K) K → ℂ), Continuous F →
      HasCompactSupport F →
        Integrable (fun z => φ (a * z) * F z) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro a F hF hFc
    have hc : Continuous fun z : AdelicGL2 (𝓞 K) K => φ (a * z) * F z :=
      (hφ.comp (continuous_const.mul continuous_id)).mul hF
    exact hc.integrable_of_hasCompactSupport hFc.mul_left
  have hfi : ∀ i, Continuous (fun z => f ((reps i)⁻¹ * z)) ∧
      HasCompactSupport (fun z => f ((reps i)⁻¹ * z)) := fun i =>
    ⟨hf.comp (continuous_const.mul continuous_id),
      hfc.comp_homeomorph (Homeomorph.mulLeft ((reps i)⁻¹))⟩
  funext x
  simp only [AutomorphicForm.rightConv_apply, Pi.smul_apply, smul_eq_mul, heckeShift]
  set μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K with hμ

  have hexpand : ∀ z, φ (x * z) * (∑ i, f ((reps i)⁻¹ * z)) = ∑ i, φ (x * z) * f ((reps i)⁻¹ * z) :=
    fun z => Finset.mul_sum _ _ _
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => by
    simpa using hint x (fun z => f ((reps i)⁻¹ * z)) (hfi i).1 (hfi i).2)]
  have hsub : ∀ i, ∫ z, φ (x * z) * f ((reps i)⁻¹ * z) ∂μ = ∫ z, φ (x * reps i * z) * f z ∂μ := by
    intro i
    symm
    calc ∫ z, φ (x * reps i * z) * f z ∂μ
        = ∫ z, φ (x * (reps i * z)) * f ((reps i)⁻¹ * (reps i * z)) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall fun z => by
            simp only [inv_mul_cancel_left, mul_assoc])
      _ = ∫ w, φ (x * w) * f ((reps i)⁻¹ * w) ∂μ :=
          integral_mul_left_eq_self (μ := μ) (fun w => φ (x * w) * f ((reps i)⁻¹ * w)) (reps i)
  simp_rw [hsub]
  rw [← integral_finsetSum _ (fun i _ => by
    simpa using hint (x * reps i) f hf hfc)]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [← Finset.sum_mul, ← mul_assoc]
  exact sum_apply_mul_reps_mul_eq K v φ f reps c heig hreps Uv hfU hφU x z

end HeckeShift

namespace HeckeShift

section Words

variable {G : Type*} [Monoid G]

private def prodWord {n : ℕ} (reps : Fin n → G) : (k : ℕ) → (Fin k → Fin n) → G
  | 0, _ => 1
  | k + 1, ι => reps (ι 0) * prodWord reps k (Fin.tail ι)

@[scoped simp] private theorem prodWord_zero {n : ℕ} (reps : Fin n → G) (ι : Fin 0 → Fin n) :
    prodWord reps 0 ι = 1 := rfl

@[scoped simp] private theorem prodWord_succ {n : ℕ} (reps : Fin n → G) (k : ℕ) (ι : Fin (k + 1) → Fin n) :
    prodWord reps (k + 1) ι = reps (ι 0) * prodWord reps k (Fin.tail ι) := rfl

private theorem sum_prodWord_eq (φ : G → ℂ) {n : ℕ} (reps : Fin n → G) (c : ℂ)
    (heig : ∀ x, ∑ i, φ (x * reps i) = c * φ x) :
    ∀ (k : ℕ) (x : G), ∑ ι : Fin k → Fin n, φ (x * prodWord reps k ι) = c ^ k * φ x
  | 0, x => by simp
  | k + 1, x => by
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
    have hterm : ∀ (i : Fin n) (ι' : Fin k → Fin n),
        φ (x * prodWord reps (k + 1) ((Fin.consEquiv fun _ : Fin (k + 1) => Fin n) (i, ι'))) =
          φ (x * reps i * prodWord reps k ι') := by
      intro i ι'
      show φ (x * prodWord reps (k + 1) (Fin.cons i ι')) = _
      rw [prodWord_succ, Fin.cons_zero, Fin.tail_cons, mul_assoc]
    simp only [hterm, sum_prodWord_eq φ reps c heig k]
    rw [← Finset.mul_sum, heig x, pow_succ, mul_assoc]

private noncomputable def powReps {n : ℕ} (reps : Fin n → G) (k : ℕ) :
    Fin (Fintype.card (Fin k → Fin n)) → G :=
  fun j => prodWord reps k ((Fintype.equivFin (Fin k → Fin n)).symm j)

private theorem sum_powReps_eq (φ : G → ℂ) {n : ℕ} (reps : Fin n → G) (c : ℂ)
    (heig : ∀ x, ∑ i, φ (x * reps i) = c * φ x) (k : ℕ) (x : G) :
    ∑ j, φ (x * powReps reps k j) = c ^ k * φ x := by
  rw [← sum_prodWord_eq φ reps c heig k x]
  exact (Fintype.equivFin (Fin k → Fin n)).symm.sum_comp (fun ι => φ (x * prodWord reps k ι))

private noncomputable def mulReps {n₁ n₂ : ℕ} (reps₁ : Fin n₁ → G) (reps₂ : Fin n₂ → G) :
    Fin (Fintype.card (Fin n₁ × Fin n₂)) → G :=
  fun j => reps₁ ((Fintype.equivFin (Fin n₁ × Fin n₂)).symm j).1 *
    reps₂ ((Fintype.equivFin (Fin n₁ × Fin n₂)).symm j).2

private theorem sum_mulReps_eq (φ : G → ℂ) {n₁ n₂ : ℕ} (reps₁ : Fin n₁ → G) (reps₂ : Fin n₂ → G)
    (c₁ c₂ : ℂ) (h₁ : ∀ x, ∑ i, φ (x * reps₁ i) = c₁ * φ x)
    (h₂ : ∀ x, ∑ j, φ (x * reps₂ j) = c₂ * φ x) (x : G) :
    ∑ j, φ (x * mulReps reps₁ reps₂ j) = (c₁ * c₂) * φ x := by
  have hprod : ∑ p : Fin n₁ × Fin n₂, φ (x * (reps₁ p.1 * reps₂ p.2)) = (c₁ * c₂) * φ x := by
    rw [Fintype.sum_prod_type]
    simp only [← mul_assoc, h₂]
    rw [← Finset.mul_sum, h₁ x]
    ring
  rw [← hprod]
  exact (Fintype.equivFin (Fin n₁ × Fin n₂)).symm.sum_comp
    (fun p : Fin n₁ × Fin n₂ => φ (x * (reps₁ p.1 * reps₂ p.2)))

end Words

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem embAt_one : embAt K v 1 = 1 := by
  have h := embAt_mul K v 1 1
  rw [one_mul] at h
  exact mul_left_cancel (a := embAt K v 1) (by rw [mul_one]; exact h.symm)

private theorem prodWord_local {n : ℕ} (reps : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hreps : ∀ i, ∃ r : GL (Fin 2) (v.adicCompletion K), reps i = embAt K v r) :
    ∀ (k : ℕ) (ι : Fin k → Fin n),
      ∃ r : GL (Fin 2) (v.adicCompletion K), prodWord reps k ι = embAt K v r
  | 0, _ => ⟨1, by rw [prodWord_zero, embAt_one]⟩
  | k + 1, ι => by
    obtain ⟨r₀, hr₀⟩ := hreps (ι 0)
    obtain ⟨r', hr'⟩ := prodWord_local reps hreps k (Fin.tail ι)
    exact ⟨r₀ * r', by rw [prodWord_succ, hr₀, hr', embAt_mul]⟩

private theorem powReps_local {n : ℕ} (reps : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hreps : ∀ i, ∃ r : GL (Fin 2) (v.adicCompletion K), reps i = embAt K v r) (k : ℕ)
    (j : Fin (Fintype.card (Fin k → Fin n))) :
    ∃ r : GL (Fin 2) (v.adicCompletion K), powReps reps k j = embAt K v r :=
  prodWord_local K v reps hreps k _

private theorem mulReps_local {n₁ n₂ : ℕ} (reps₁ : Fin n₁ → GL (Fin 2) (AdeleRing (𝓞 K) K))
    (reps₂ : Fin n₂ → GL (Fin 2) (AdeleRing (𝓞 K) K))
    (h₁ : ∀ i, ∃ r : GL (Fin 2) (v.adicCompletion K), reps₁ i = embAt K v r)
    (h₂ : ∀ j, ∃ r : GL (Fin 2) (v.adicCompletion K), reps₂ j = embAt K v r)
    (j : Fin (Fintype.card (Fin n₁ × Fin n₂))) :
    ∃ r : GL (Fin 2) (v.adicCompletion K), mulReps reps₁ reps₂ j = embAt K v r := by
  obtain ⟨r₁, hr₁⟩ := h₁ ((Fintype.equivFin (Fin n₁ × Fin n₂)).symm j).1
  obtain ⟨r₂, hr₂⟩ := h₂ ((Fintype.equivFin (Fin n₁ × Fin n₂)).symm j).2
  exact ⟨r₁ * r₂, by rw [mulReps, hr₁, hr₂, embAt_mul]⟩

private theorem heckeShift_continuous {n : ℕ} (reps : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K))
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : Continuous f) :
    Continuous (heckeShift K reps f) := by
  unfold heckeShift
  exact continuous_finsetSum _ fun i _ => hf.comp (continuous_const.mul continuous_id)

private theorem heckeShift_hasCompactSupport {n : ℕ} (reps : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K))
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (heckeShift K reps f) := by
  have hsum : heckeShift K reps f = ∑ i, fun z => f ((reps i)⁻¹ * z) := by
    funext z
    simp only [heckeShift, Finset.sum_apply]
  rw [hsum]
  exact HasCompactSupport.finset_sum fun i _ =>
    hfc.comp_homeomorph (Homeomorph.mulLeft ((reps i)⁻¹))

private theorem rightConv_heckeShift_powReps (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 K) K) (c : ℂ)
    (heig : ∀ x, ∑ i, φ (x * reps i) = c * φ x)
    (hreps : ∀ i, ∃ r : GL (Fin 2) (v.adicCompletion K), reps i = embAt K v r)
    (Uv : Set (GL (Fin 2) (v.adicCompletion K)))
    (hfU : ∀ z, f z ≠ 0 → compAt K v z ∈ Uv)
    (hφU : ∀ x, ∀ u ∈ Uv, φ (x * embAt K v u) = φ x) (k : ℕ) :
    AutomorphicForm.rightConv K φ (heckeShift K (powReps reps k) f) =
      (c ^ k) • AutomorphicForm.rightConv K φ f :=
  rightConv_heckeShift K v φ hφ f hf hfc (powReps reps k) (c ^ k) (sum_powReps_eq φ reps c heig k)
    (powReps_local K v reps hreps k) Uv hfU hφU

private theorem rightConv_heckeShift_mulReps (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {n₁ n₂ : ℕ} (reps₁ : Fin n₁ → AdelicGL2 (𝓞 K) K) (reps₂ : Fin n₂ → AdelicGL2 (𝓞 K) K)
    (c₁ c₂ : ℂ) (h₁ : ∀ x, ∑ i, φ (x * reps₁ i) = c₁ * φ x)
    (h₂ : ∀ x, ∑ j, φ (x * reps₂ j) = c₂ * φ x)
    (hreps₁ : ∀ i, ∃ r : GL (Fin 2) (v.adicCompletion K), reps₁ i = embAt K v r)
    (hreps₂ : ∀ j, ∃ r : GL (Fin 2) (v.adicCompletion K), reps₂ j = embAt K v r)
    (Uv : Set (GL (Fin 2) (v.adicCompletion K)))
    (hfU : ∀ z, f z ≠ 0 → compAt K v z ∈ Uv)
    (hφU : ∀ x, ∀ u ∈ Uv, φ (x * embAt K v u) = φ x) :
    AutomorphicForm.rightConv K φ (heckeShift K (mulReps reps₁ reps₂) f) =
      (c₁ * c₂) • AutomorphicForm.rightConv K φ f :=
  rightConv_heckeShift K v φ hφ f hf hfc (mulReps reps₁ reps₂) (c₁ * c₂)
    (sum_mulReps_eq φ reps₁ reps₂ c₁ c₂ h₁ h₂) (mulReps_local K v reps₁ reps₂ hreps₁ hreps₂)
    Uv hfU hφU

end HeckeShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

namespace HeckeShift

section CosetShift

variable {G : Type*} [Group G]

private noncomputable def cosetShift {n : ℕ} (reps : Fin n → G) (h : G → ℂ) : G → ℂ :=
  fun x => ∑ i, h ((reps i)⁻¹ * x)

private theorem cosetShift_apply {n : ℕ} (reps : Fin n → G) (h : G → ℂ) (x : G) :
    cosetShift reps h x = ∑ i, h ((reps i)⁻¹ * x) := rfl

private theorem sum_eq_cosetShift_indicator_mul {n : ℕ} (reps : Fin n → G) (U : Set G) (x : G) (P : ℂ)
    (F : Fin n → ℂ) (hin : ∀ i, (reps i)⁻¹ * x ∈ U → F i = P)
    (hout : ∀ i, (reps i)⁻¹ * x ∉ U → F i = 0) :
    ∑ i, F i = cosetShift reps (U.indicator fun _ => (1 : ℂ)) x * P := by
  classical
  rw [cosetShift_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : (reps i)⁻¹ * x ∈ U
  · rw [hin i hi]
    simp only [Set.indicator_apply, if_pos hi, one_mul]
  · rw [hout i hi]
    simp only [Set.indicator_apply, if_neg hi, zero_mul]

variable [TopologicalSpace G]

private theorem isLocallyConstant_finset_sum {X ι : Type*} [TopologicalSpace X] (s : Finset ι)
    {g : ι → X → ℂ} (hg : ∀ i ∈ s, IsLocallyConstant (g i)) :
    IsLocallyConstant (fun x => ∑ i ∈ s, g i x) := by
  classical
  revert hg
  refine Finset.induction_on s (fun _ => ?_) (fun a t hat iht hg => ?_)
  · simp only [Finset.sum_empty]
    exact IsLocallyConstant.const 0
  · simp only [Finset.sum_insert hat]
    exact (hg a (Finset.mem_insert_self a t)).add
      (iht fun i hi => hg i (Finset.mem_insert_of_mem hi))

private theorem cosetShift_isLocallyConstant [ContinuousMul G] {n : ℕ} (reps : Fin n → G) {h : G → ℂ}
    (hh : IsLocallyConstant h) : IsLocallyConstant (cosetShift reps h) := by
  unfold cosetShift
  exact isLocallyConstant_finset_sum Finset.univ fun i _ =>
    hh.comp_continuous (continuous_const.mul continuous_id)

private theorem cosetShift_hasCompactSupport [ContinuousMul G] {n : ℕ} (reps : Fin n → G) {h : G → ℂ}
    (hc : HasCompactSupport h) : HasCompactSupport (cosetShift reps h) := by
  have hsum : cosetShift reps h = ∑ i, fun x => h ((reps i)⁻¹ * x) := by
    funext x
    simp only [cosetShift, Finset.sum_apply]
  rw [hsum]
  exact HasCompactSupport.finset_sum fun i _ => hc.comp_homeomorph (Homeomorph.mulLeft ((reps i)⁻¹))

end CosetShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

private theorem comp_mul_left_mem_typeSubmodule {H G W : Type*} [Group H] [Group G] [AddCommGroup W]
    [Module ℂ W] {ι : H →* G} {ρ : Representation ℂ H W} {f : G → ℂ} (hf : f ∈ typeSubmodule ι ρ)
    (g : G) : (fun x => f (g * x)) ∈ typeSubmodule ι ρ := by
  refine Submodule.span_induction (p := fun f _ => (fun x => f (g * x)) ∈ typeSubmodule ι ρ)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, u, rfl⟩
    let Lg : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
      { toFun := fun φ x => φ (g * x)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hLT : IsRightEquivariant ι ρ (Lg ∘ₗ T) := fun k w x => by
      show T (ρ k w) (g * x) = T w (g * (x * ι k))
      rw [hT k w (g * x), mul_assoc]
    exact mem_typeSubmodule_of_isRightEquivariant hLT u
  · exact (typeSubmodule ι ρ).zero_mem
  · exact fun _ _ _ _ hu hw => (typeSubmodule ι ρ).add_mem hu hw
  · exact fun c _ _ hu => (typeSubmodule ι ρ).smul_mem c hu

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem comp_mul_left_mem_archDualCutSubmodule (tys : ArchTypeFamily K)
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : f ∈ archDualCutSubmodule K tys) (g : AdelicGL2 (𝓞 K) K) :
    (fun x => f (g * x)) ∈ archDualCutSubmodule K tys := by
  rw [mem_archDualCutSubmodule_iff] at hf ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (g * x)) ∈ ⨆ i, archDualTypeSubmoduleAt K w (tys.rep w i))
    (hf w) ?_ ?_ ?_
  · intro i f hfi
    exact le_iSup (fun i => archDualTypeSubmoduleAt K w (tys.rep w i)) i
      (comp_mul_left_mem_typeSubmodule (ι := rowIsometryInclAt₀ K w) hfi g)
  · show (fun x => (0 : AdelicGL2 (𝓞 K) K → ℂ) (g * x)) ∈
      ⨆ i, archDualTypeSubmoduleAt K w (tys.rep w i)
    have h0 : (fun x => (0 : AdelicGL2 (𝓞 K) K → ℂ) (g * x)) = 0 := funext fun _ => rfl
    rw [h0]
    exact Submodule.zero_mem _
  · intro a b ha hb
    have hab : (fun x => (a + b) (g * x)) = (fun x => a (g * x)) + fun x => b (g * x) :=
      funext fun _ => rfl
    rw [hab]
    exact Submodule.add_mem _ ha hb

private theorem compAt_archIsometryInclAt₀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) :
    compAt K v (rowIsometryInclAt₀ K w k) = 1 := by
  simp only [compAt, glFin_rowIsometryInclAt₀, map_one]

private theorem comp_mul_embAt_mem_archCutSubmodule (tys : ArchTypeFamily K) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : f ∈ archCutSubmodule K tys) (r : GL (Fin 2) (v.adicCompletion K)) :
    (fun x => f (x * embAt K v r)) ∈ archCutSubmodule K tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  have hcomm : ∀ k : rowIsometrySubgroup₀ w.Completion,
      Commute (embAt K v r) (rowIsometryInclAt₀ K w k) := fun k =>
    embAt_mul_comm_of_compAt_eq_one K v r _ (compAt_archIsometryInclAt₀ K v w k)
  refine Submodule.iSup_induction _
    (motive := fun f =>
      (fun x => f (x * embAt K v r)) ∈ ⨆ i, archTypeSubmoduleAt K w (tys.rep w i))
    (hf w) ?_ ?_ ?_
  · intro i f hfi
    exact le_iSup (fun i => archTypeSubmoduleAt K w (tys.rep w i)) i
      (comp_mul_mem_typeSubmodule_of_commute (ι := rowIsometryInclAt₀ K w) hfi _ hcomm)
  · show (fun x => (0 : AdelicGL2 (𝓞 K) K → ℂ) (x * embAt K v r)) ∈
      ⨆ i, archTypeSubmoduleAt K w (tys.rep w i)
    have h0 : (fun x => (0 : AdelicGL2 (𝓞 K) K → ℂ) (x * embAt K v r)) = 0 := funext fun _ => rfl
    rw [h0]
    exact Submodule.zero_mem _
  · intro a b ha hb
    have hab : (fun x => (a + b) (x * embAt K v r)) =
        (fun x => a (x * embAt K v r)) + fun x => b (x * embAt K v r) :=
      funext fun _ => rfl
    rw [hab]
    exact Submodule.add_mem _ ha hb

private theorem isArchBiFinite_heckeShift (tys : ArchTypeFamily K) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : IsArchBiFinite K tys f) {n : ℕ} (r : Fin n → GL (Fin 2) (v.adicCompletion K)) :
    IsArchBiFinite K tys (heckeShift K (fun i => embAt K v (r i)) f) := by
  refine ⟨?_, ?_⟩
  · have h1 : (fun x : AdelicGL2 (𝓞 K) K => heckeShift K (fun i => embAt K v (r i)) f x⁻¹) =
        ∑ i, fun x : AdelicGL2 (𝓞 K) K => f (x * embAt K v (r i))⁻¹ := by
      funext x
      simp only [heckeShift, Finset.sum_apply, mul_inv_rev]
    rw [h1]
    exact Submodule.sum_mem _ fun i _ => comp_mul_embAt_mem_archCutSubmodule K v tys hf.1 (r i)
  · have h2 : heckeShift K (fun i => embAt K v (r i)) f =
        ∑ i, fun x : AdelicGL2 (𝓞 K) K => f ((embAt K v (r i))⁻¹ * x) := by
      funext x
      simp only [heckeShift, Finset.sum_apply]
    rw [h2]
    exact Submodule.sum_mem _ fun i _ => comp_mul_left_mem_archDualCutSubmodule K tys hf.2 _

private theorem heckeShift_isBiInvariantUnder (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsBiInvariantUnder K U f) {n : ℕ}
    (reps : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hleft : ∀ u ∈ U, ∀ x, heckeShift K reps f (u * x) = heckeShift K reps f x) :
    IsBiInvariantUnder K U (heckeShift K reps f) := by
  intro u hu x
  refine ⟨hleft u hu x, ?_⟩
  simp only [heckeShift, ← mul_assoc]
  exact Finset.sum_congr rfl fun i _ => (hf u hu _).2

private theorem isUnitFactorization_heckeShift [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hv : v ∉ S) {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    {fS : ∀ w : HeightOneSpectrum (𝓞 K), GL (Fin 2) (w.adicCompletion K) → ℂ}
    (h : IsUnitFactorization K S f fa ff fS) {n : ℕ} (r : Fin n → GL (Fin 2) (v.adicCompletion K)) :
    IsUnitFactorization K (insert v S) (heckeShift K (fun i => embAt K v (r i)) f) fa
      (cosetShift (fun i => AdelicDock.localEmbed (𝓞 K) K v (r i)) ff)
      (Function.update fS v
        (cosetShift r ((localIntegralSet K v).indicator fun _ => (1 : ℂ)))) := by
  obtain ⟨hfa, hff, hfS, hprod, hzero, hfac⟩ := h
  refine ⟨hfa, ⟨cosetShift_isLocallyConstant _ hff.1, cosetShift_hasCompactSupport _ hff.2⟩,
    ?_, ?_, ?_, ?_⟩
  · intro w hw
    by_cases hwv : w = v
    · rw [hwv, Function.update_self]
      obtain ⟨hlc, hcs⟩ := isLocalTestFn_indicator_localIntegralSet K v
      exact ⟨cosetShift_isLocallyConstant r hlc, cosetShift_hasCompactSupport r hcs⟩
    · rw [Function.update_of_ne hwv]
      exact hfS w ((Finset.mem_insert.mp hw).resolve_left hwv)
  · intro g hint
    rw [Finset.prod_insert hv, Function.update_self]
    have hprodS : ∏ w ∈ S, Function.update fS v
          (cosetShift r ((localIntegralSet K v).indicator fun _ => (1 : ℂ))) w
            (AdelicLevel.finComponent (𝓞 K) K w g) =
        ∏ w ∈ S, fS w (AdelicLevel.finComponent (𝓞 K) K w g) :=
      Finset.prod_congr rfl fun w hw => by
        rw [Function.update_of_ne (fun e => hv (by rw [← e]; exact hw))]
    rw [hprodS, cosetShift_apply]
    refine sum_eq_cosetShift_indicator_mul r (localIntegralSet K v)
      (AdelicLevel.finComponent (𝓞 K) K v g) _
      (fun i => ff ((AdelicDock.localEmbed (𝓞 K) K v (r i))⁻¹ * g)) ?_ ?_
    · intro i hi
      show ff ((AdelicDock.localEmbed (𝓞 K) K v (r i))⁻¹ * g) = _
      rw [hprod _ ?_]
      · refine Finset.prod_congr rfl fun w hw => ?_
        rw [map_mul, map_inv, AdelicDock.finComponent_localEmbed_of_ne (𝓞 K) K v (r i)
          (fun e => hv (by rw [← e]; exact hw)), inv_one, one_mul]
      · intro w hwS
        rw [map_mul, map_inv]
        by_cases hwv : w = v
        · rw [hwv, AdelicDock.finComponent_localEmbed_self]
          exact hi
        · rw [AdelicDock.finComponent_localEmbed_of_ne (𝓞 K) K v (r i) hwv, inv_one, one_mul]
          exact hint w fun hmem => (Finset.mem_insert.mp hmem).elim hwv hwS
    · intro i hi
      show ff ((AdelicDock.localEmbed (𝓞 K) K v (r i))⁻¹ * g) = 0
      refine hzero _ ⟨v, hv, ?_⟩
      rw [map_mul, map_inv, AdelicDock.finComponent_localEmbed_self]
      exact hi
  · rintro g ⟨w, hw, hwint⟩
    have hwv : w ≠ v := fun e => hw (by rw [e]; exact Finset.mem_insert_self v S)
    have hwS : w ∉ S := fun e => hw (Finset.mem_insert_of_mem e)
    rw [cosetShift_apply]
    refine Finset.sum_eq_zero fun i _ => hzero _ ⟨w, hwS, ?_⟩
    rw [map_mul, map_inv, AdelicDock.finComponent_localEmbed_of_ne (𝓞 K) K v (r i) hwv, inv_one,
      one_mul]
    exact hwint
  · intro g
    simp only [heckeShift, cosetShift_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfac, map_mul, map_inv, map_mul, map_inv, embAt, AdelicDock.glArch_finEmbed,
      AdelicDock.glFin_finEmbed, inv_one, one_mul]

private theorem isUnitFactorizableOfTypeAt_heckeShift [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (tys : ArchTypeFamily K) (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hv : v ∉ S) {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableOfTypeAt K tys U S f) {n : ℕ}
    (r : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hleft : ∀ u ∈ U, ∀ x, heckeShift K (fun i => embAt K v (r i)) f (u * x) =
      heckeShift K (fun i => embAt K v (r i)) f x) :
    IsUnitFactorizableOfTypeAt K tys U (insert v S)
      (heckeShift K (fun i => embAt K v (r i)) f) := by
  obtain ⟨⟨hbi, fa, ff, fS, hfac⟩, harch⟩ := hf
  exact ⟨⟨heckeShift_isBiInvariantUnder K U hbi _ hleft, fa, _, _,
    isUnitFactorization_heckeShift K v S hv hfac r⟩, isArchBiFinite_heckeShift K v tys harch r⟩

end HeckeShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

namespace HeckeShift

section LeftStable

variable {G : Type*} [Group G]

private def IsLeftStable (U : Subgroup G) {ι : Type*} (r : ι → G) : Prop :=
  ∀ k ∈ U, ∃ π : Equiv.Perm ι, ∀ i, ∃ k' ∈ U, k⁻¹ * r i = r (π i) * k'

private theorem IsLeftStable.reindex {U : Subgroup G} {ι ι' : Type*} {r : ι → G} (hr : IsLeftStable U r)
    (e : ι' ≃ ι) : IsLeftStable U (fun j => r (e j)) := by
  intro k hk
  obtain ⟨π, hπ⟩ := hr k hk
  refine ⟨e.trans (π.trans e.symm), fun j => ?_⟩
  obtain ⟨k', hk', h⟩ := hπ (e j)
  exact ⟨k', hk', by simpa using h⟩

private theorem isLeftStable_const_one (U : Subgroup G) {ι : Type*} : IsLeftStable U (fun _ : ι => 1) :=
  fun k hk => ⟨Equiv.refl ι, fun _ => ⟨k⁻¹, U.inv_mem hk, by simp⟩⟩

private theorem IsLeftStable.pair {U : Subgroup G} {ι₁ ι₂ : Type*} {r₁ : ι₁ → G} {r₂ : ι₂ → G}
    (h₁ : IsLeftStable U r₁) (h₂ : IsLeftStable U r₂) :
    IsLeftStable U (fun p : ι₁ × ι₂ => r₁ p.1 * r₂ p.2) := by
  intro k hk
  obtain ⟨π₁, hπ₁⟩ := h₁ k hk
  choose k₁ hk₁ hk₁eq using hπ₁
  have h₂' : ∀ i, ∃ σ : Equiv.Perm ι₂, ∀ j, ∃ k' ∈ U, k₁ i * r₂ j = r₂ (σ j) * k' := fun i => by
    obtain ⟨σ, hσ⟩ := h₂ (k₁ i)⁻¹ (U.inv_mem (hk₁ i))
    exact ⟨σ, fun j => by simpa using hσ j⟩
  choose σ hσ using h₂'
  refine ⟨Equiv.prodShear π₁ σ, fun p => ?_⟩
  obtain ⟨k', hk', hk'eq⟩ := hσ p.1 p.2
  refine ⟨k', hk', ?_⟩
  simp only [Equiv.prodShear_apply]
  rw [← mul_assoc, hk₁eq p.1, mul_assoc, hk'eq, mul_assoc]

private theorem isLeftStable_prodWord {U : Subgroup G} {n : ℕ} {r : Fin n → G} (hr : IsLeftStable U r) :
    ∀ k : ℕ, IsLeftStable U (fun ι : Fin k → Fin n => prodWord r k ι)
  | 0 => by simpa only [prodWord_zero] using isLeftStable_const_one U (ι := Fin 0 → Fin n)
  | k + 1 => by
    have h := (hr.pair (isLeftStable_prodWord hr k)).reindex
      (Fin.consEquiv fun _ : Fin (k + 1) => Fin n).symm
    have hfun : (fun ι : Fin (k + 1) → Fin n => prodWord r (k + 1) ι) =
        fun ι => (fun p : Fin n × (Fin k → Fin n) => r p.1 * prodWord r k p.2)
          ((Fin.consEquiv fun _ : Fin (k + 1) => Fin n).symm ι) := by
      funext ι
      rfl
    rw [hfun]
    exact h

private theorem isLeftStable_powReps {U : Subgroup G} {n : ℕ} {r : Fin n → G} (hr : IsLeftStable U r)
    (k : ℕ) : IsLeftStable U (powReps r k) :=
  (isLeftStable_prodWord hr k).reindex (Fintype.equivFin (Fin k → Fin n)).symm

private theorem isLeftStable_mulReps {U : Subgroup G} {n₁ n₂ : ℕ} {r₁ : Fin n₁ → G} {r₂ : Fin n₂ → G}
    (h₁ : IsLeftStable U r₁) (h₂ : IsLeftStable U r₂) : IsLeftStable U (mulReps r₁ r₂) :=
  (h₁.pair h₂).reindex (Fintype.equivFin (Fin n₁ × Fin n₂)).symm

private theorem isLeftStable_of_isHeckeCosetSystem {U : Subgroup G} {g : G} {n : ℕ} {r : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g r) : IsLeftStable U r := by
  intro k hk
  have hcov : ∀ i, ∃ j, (QuotientGroup.mk (k⁻¹ * r i) : G ⧸ U) = QuotientGroup.mk (r j) := fun i =>
    hsys.covers _ (HeckePair.mul_mem_doubleCoset (hsys.mem_doubleCoset i) (U.inv_mem hk))
  choose j hj using hcov
  have hinj : Function.Injective j := by
    intro i₁ i₂ h
    apply hsys.mk_injective
    show (QuotientGroup.mk (r i₁) : G ⧸ U) = QuotientGroup.mk (r i₂)
    have h3 : (QuotientGroup.mk (k⁻¹ * r i₁) : G ⧸ U) = QuotientGroup.mk (k⁻¹ * r i₂) := by
      rw [hj i₁, hj i₂, h]
    rw [QuotientGroup.eq] at h3 ⊢
    simpa only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using h3
  refine ⟨Equiv.ofBijective j (Finite.injective_iff_bijective.mp hinj), fun i => ?_⟩
  have hu := QuotientGroup.eq.mp (hj i)
  refine ⟨((k⁻¹ * r i)⁻¹ * r (j i))⁻¹, U.inv_mem hu, ?_⟩
  show k⁻¹ * r i = r (j i) * ((k⁻¹ * r i)⁻¹ * r (j i))⁻¹
  group

private theorem sum_apply_inv_mul_eq_of_isLeftStable {H : Type*} [Group H] (e : H → G)
    (he_mul : ∀ a b, e (a * b) = e a * e b) (he_inv : ∀ a, e a⁻¹ = (e a)⁻¹) (U : Subgroup G)
    (Uv : Subgroup H) (hUv : ∀ h ∈ Uv, e h ∈ U) {f : G → ℂ} (hf : ∀ u ∈ U, ∀ x, f (u * x) = f x)
    {n : ℕ} {r : Fin n → H} (hr : IsLeftStable Uv r) {c : H} (hc : c ∈ Uv) {w : G} (hw : w ∈ U)
    (hwc : ∀ h : H, Commute (e h) w) (x : G) :
    ∑ i, f ((e (r i))⁻¹ * (e c * w * x)) = ∑ i, f ((e (r i))⁻¹ * x) := by
  obtain ⟨π, hπ⟩ := hr c hc
  have hterm : ∀ i, f ((e (r i))⁻¹ * (e c * w * x)) = f ((e (r (π i)))⁻¹ * x) := by
    intro i
    obtain ⟨k', hk', hk'eq⟩ := hπ i
    have h1 : (r i)⁻¹ * c = k'⁻¹ * (r (π i))⁻¹ := by
      rw [← mul_inv_rev, ← hk'eq, mul_inv_rev, inv_inv]
    have h2 : (e (r i))⁻¹ * (e c * w * x) = e k'⁻¹ * (w * ((e (r (π i)))⁻¹ * x)) := by
      have h3 : (e (r i))⁻¹ * e c = e k'⁻¹ * (e (r (π i)))⁻¹ := by
        rw [← he_inv, ← he_mul, h1, he_mul, he_inv, he_inv]
      rw [mul_assoc (e c), ← mul_assoc, h3, mul_assoc, ← mul_assoc (e (r (π i)))⁻¹ w x,
        ((hwc (r (π i))).inv_left).eq, mul_assoc]
    rw [h2, hf _ (hUv _ (Uv.inv_mem hk')), hf _ hw]
  simp only [hterm]
  exact Equiv.sum_comp π fun j => f ((e (r j))⁻¹ * x)

end LeftStable
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem embAt_inv (g : GL (Fin 2) (v.adicCompletion K)) : embAt K v g⁻¹ = (embAt K v g)⁻¹ := by
  simp only [embAt, map_inv]

private theorem restAt_mem (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (Uv : Subgroup (GL (Fin 2) (v.adicCompletion K))) (hUv₁ : ∀ x ∈ Uv, embAt K v x ∈ U)
    (hUv₂ : ∀ u ∈ U, compAt K v u ∈ Uv) {u : GL (Fin 2) (AdeleRing (𝓞 K) K)} (hu : u ∈ U) :
    restAt K v u ∈ U :=
  U.mul_mem (U.inv_mem (hUv₁ _ (hUv₂ u hu))) hu

private theorem heckeShift_apply_mul_eq_of_isLeftStable (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (Uv : Subgroup (GL (Fin 2) (v.adicCompletion K))) (hUv₁ : ∀ x ∈ Uv, embAt K v x ∈ U)
    (hUv₂ : ∀ u ∈ U, compAt K v u ∈ Uv) {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsBiInvariantUnder K U f) {n : ℕ} {r : Fin n → GL (Fin 2) (v.adicCompletion K)}
    (hr : IsLeftStable Uv r) {u : GL (Fin 2) (AdeleRing (𝓞 K) K)} (hu : u ∈ U)
    (x : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    heckeShift K (fun i => embAt K v (r i)) f (u * x) =
      heckeShift K (fun i => embAt K v (r i)) f x := by
  simp only [heckeShift]
  rw [← embAt_compAt_mul_restAt K v u]
  exact sum_apply_inv_mul_eq_of_isLeftStable (embAt K v) (embAt_mul K v) (embAt_inv K v) U Uv hUv₁
    (fun w hw y => (hf w hw y).1) hr (hUv₂ u hu) (restAt_mem K v U Uv hUv₁ hUv₂ hu)
    (fun h => embAt_mul_comm_of_compAt_eq_one K v h _ (compAt_restAt K v u)) x

private theorem isUnitFactorizableOfTypeAt_heckeShift_of_isLeftStable
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (tys : ArchTypeFamily K)
    (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (Uv : Subgroup (GL (Fin 2) (v.adicCompletion K))) (hUv₁ : ∀ x ∈ Uv, embAt K v x ∈ U)
    (hUv₂ : ∀ u ∈ U, compAt K v u ∈ Uv) (S : Finset (HeightOneSpectrum (𝓞 K))) (hv : v ∉ S)
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsUnitFactorizableOfTypeAt K tys U S f) {n : ℕ}
    {r : Fin n → GL (Fin 2) (v.adicCompletion K)} (hr : IsLeftStable Uv r) :
    IsUnitFactorizableOfTypeAt K tys U (insert v S) (heckeShift K (fun i => embAt K v (r i)) f) :=
  isUnitFactorizableOfTypeAt_heckeShift K v tys U S hv hf r fun _u hu x =>
    heckeShift_apply_mul_eq_of_isLeftStable K v U Uv hUv₁ hUv₂ hf.1.1 hr hu x

end HeckeShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

namespace HeckeShift

section Reindex

variable {G : Type*} [Group G]

private theorem isHeckeCosetSystem_mul_of_mem {U : Subgroup G} {g : G} {ι : Type*} {reps : ι → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) (u : ι → G) (hu : ∀ i, u i ∈ U) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g (fun i => reps i * u i) where
  mem_doubleCoset i := HeckePair.doubleCoset_mul_mem (hsys.mem_doubleCoset i) (hu i)
  covers x hx := by
    obtain ⟨i, hi⟩ := hsys.covers x hx
    exact ⟨i, hi.trans (QuotientGroup.eq.mpr (by simpa using hu i))⟩
  mk_injective i j hij := by
    apply hsys.mk_injective
    show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    rw [show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps i * u i) from
        QuotientGroup.eq.mpr (by simpa using hu i),
      show (QuotientGroup.mk (reps j) : G ⧸ U) = QuotientGroup.mk (reps j * u j) from
        QuotientGroup.eq.mpr (by simpa using hu j)]
    exact hij

private theorem sum_apply_inv_mul_eq_of_isLeftStable_self {U : Subgroup G} {f : G → ℂ}
    (hf : ∀ u ∈ U, ∀ x, f (u * x) = f x) {n : ℕ} {r : Fin n → G} (hr : IsLeftStable U r) {u : G}
    (hu : u ∈ U) (x : G) : ∑ i, f ((r i)⁻¹ * (u * x)) = ∑ i, f ((r i)⁻¹ * x) := by
  have h := sum_apply_inv_mul_eq_of_isLeftStable (id : G → G) (fun _ _ => rfl) (fun _ => rfl) U U
    (fun _ h => h) hf hr hu U.one_mem (fun _ => Commute.one_right _) x
  simpa only [id_eq, mul_one] using h

end Reindex
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem restAt_mul (a b : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    restAt K v (a * b) = restAt K v a * restAt K v b := by
  have hcm : Commute (embAt K v (compAt K v b)) (restAt K v a) :=
    embAt_mul_comm_of_compAt_eq_one K v _ _ (compAt_restAt K v a)
  calc restAt K v (a * b) = (embAt K v (compAt K v b))⁻¹ * restAt K v a * b := by
        simp only [restAt, compAt_mul, embAt_mul, mul_inv_rev, mul_assoc]
    _ = restAt K v a * (embAt K v (compAt K v b))⁻¹ * b := by rw [hcm.inv_left.eq]
    _ = restAt K v a * restAt K v b := by simp only [restAt, mul_assoc]

private theorem restAt_embAt (g : GL (Fin 2) (v.adicCompletion K)) : restAt K v (embAt K v g) = 1 := by
  simp only [restAt, compAt_embAt, inv_mul_cancel]

private theorem restAt_mem_of_split (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (hsplit : ∀ u ∈ U, embAt K v (compAt K v u) ∈ U) {u : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hu : u ∈ U) : restAt K v u ∈ U :=
  U.mul_mem (U.inv_mem (hsplit u hu)) hu

private theorem restAt_mem_of_mem_doubleCoset (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (hsplit : ∀ u ∈ U, embAt K v (compAt K v u) ∈ U) {gv : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hgv : restAt K v gv = 1) {y : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hy : y ∈ HeckePair.doubleCoset U gv) : restAt K v y ∈ U := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hy
  rw [restAt_mul, restAt_mul, hgv, mul_one]
  exact U.mul_mem (restAt_mem_of_split K v U hsplit hu₁) (restAt_mem_of_split K v U hsplit hu₂)

private theorem embAt_compAt_eq_mul_inv (y : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    embAt K v (compAt K v y) = y * (restAt K v y)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, embAt_compAt_mul_restAt]

private theorem localize (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (hsplit : ∀ u ∈ U, embAt K v (compAt K v u) ∈ U) {gv : AdelicGL2 (𝓞 K) K}
    (hgv : restAt K v gv = 1) {n : ℕ} {reps : Fin n → AdelicGL2 (𝓞 K) K}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps) :
    HeckeIntegralSeam.IsHeckeCosetSystem U gv (fun i => embAt K v (compAt K v (reps i))) ∧
      ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g) →
        ∀ x, ∑ i, φ (x * embAt K v (compAt K v (reps i))) = ∑ i, φ (x * reps i) := by
  have hmem : ∀ i, (restAt K v (reps i))⁻¹ ∈ U := fun i =>
    U.inv_mem (restAt_mem_of_mem_doubleCoset K v U hsplit hgv (hsys.mem_doubleCoset i))
  refine ⟨?_, fun φ hφ x => ?_⟩
  · simp only [embAt_compAt_eq_mul_inv]
    exact isHeckeCosetSystem_mul_of_mem hsys _ hmem
  · have h := SmoothCusp.heckeCosetSum_mul_right K hφ reps (fun i => (restAt K v (reps i))⁻¹) hmem x
    simp only [SmoothCusp.heckeCosetSum] at h
    simp only [embAt_compAt_eq_mul_inv]
    exact h

private theorem isLeftStable_local (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (Uv : Subgroup (GL (Fin 2) (v.adicCompletion K))) (hUv₁ : ∀ x ∈ Uv, embAt K v x ∈ U)
    (hUv₂ : ∀ u ∈ U, compAt K v u ∈ Uv) {n : ℕ} {r : Fin n → GL (Fin 2) (v.adicCompletion K)}
    (hr : IsLeftStable U (fun i => embAt K v (r i))) : IsLeftStable Uv r := by
  intro k hk
  obtain ⟨π, hπ⟩ := hr (embAt K v k) (hUv₁ k hk)
  refine ⟨π, fun i => ?_⟩
  obtain ⟨k', hk', hk'eq⟩ := hπ i
  refine ⟨compAt K v k', hUv₂ k' hk', ?_⟩
  have h := congrArg (compAt K v) hk'eq
  simpa only [compAt_mul, compAt_inv, compAt_embAt] using h

private theorem exists_local_system_of_isHeckeCosetEigenfunctionAt (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (Uv : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hsplit : ∀ u ∈ U, embAt K v (compAt K v u) ∈ U)
    (hUv₁ : ∀ x ∈ Uv, embAt K v x ∈ U) (hUv₂ : ∀ u ∈ U, compAt K v u ∈ Uv) {gv : AdelicGL2 (𝓞 K) K}
    (hgv : restAt K v gv = 1) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g) {c : ℂ}
    (h : SmoothCusp.IsHeckeCosetEigenfunctionAt K U gv v φ c) :
    ∃ r : Fin (Ideal.absNorm v.asIdeal + 1) → GL (Fin 2) (v.adicCompletion K),
      IsLeftStable Uv r ∧ ∀ x, ∑ i, φ (x * embAt K v (r i)) = c * φ x := by
  obtain ⟨reps, hsys, heig⟩ := h
  obtain ⟨hsys', htrans⟩ := localize K v U hsplit hgv hsys
  refine ⟨fun i => compAt K v (reps i), isLeftStable_local K v U Uv hUv₁ hUv₂
    (isLeftStable_of_isHeckeCosetSystem hsys'), fun x => (htrans φ hφ x).trans ?_⟩
  exact heig x

end HeckeShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

namespace HeckeShift

section ShiftIndicator

variable {G : Type*} [Group G]

private theorem sum_indicator_inv_mul_eq {U : Subgroup G} {g : G} {n : ℕ} {r : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g r) (x : G) :
    ∑ i, (U : Set G).indicator (fun _ => (1 : ℂ)) ((r i)⁻¹ * x) =
      (HeckePair.doubleCoset U g).indicator (fun _ => (1 : ℂ)) x := by
  classical
  have hterm : ∀ i, (U : Set G).indicator (fun _ => (1 : ℂ)) ((r i)⁻¹ * x) =
      if (QuotientGroup.mk (r i) : G ⧸ U) = QuotientGroup.mk x then 1 else 0 := fun i => by
    by_cases h : (QuotientGroup.mk (r i) : G ⧸ U) = QuotientGroup.mk x
    · rw [if_pos h, Set.indicator_of_mem (QuotientGroup.eq.mp h)]
    · rw [if_neg h, Set.indicator_of_notMem (fun hm => h (QuotientGroup.eq.mpr hm))]
  simp only [hterm]
  by_cases hx : x ∈ HeckePair.doubleCoset U g
  · obtain ⟨i₀, hi₀⟩ := hsys.covers x hx
    rw [Set.indicator_of_mem hx, Finset.sum_eq_single i₀]
    · rw [if_pos hi₀.symm]
    · intro i _ hi
      rw [if_neg]
      intro h
      exact hi (hsys.mk_injective (h.trans hi₀))
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  · rw [Set.indicator_of_notMem hx]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro h
    apply hx
    obtain ⟨u, hu, hux⟩ : ∃ u ∈ U, r i * u = x := by
      refine ⟨(r i)⁻¹ * x, QuotientGroup.eq.mp h, ?_⟩
      rw [mul_inv_cancel_left]
    rw [← hux]
    exact HeckePair.doubleCoset_mul_mem (hsys.mem_doubleCoset i) hu

private theorem cosetShift_indicator_eq {U : Subgroup G} {g : G} {n : ℕ} {r : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g r) :
    cosetShift r ((U : Set G).indicator fun _ => (1 : ℂ)) =
      (HeckePair.doubleCoset U g).indicator fun _ => (1 : ℂ) :=
  funext fun x => sum_indicator_inv_mul_eq hsys x

open scoped Pointwise in

private theorem cosetShift_indicator_eq_heckeIndicator {U : Subgroup G} {g : G} {n : ℕ} {r : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g r)
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ U)).Finite) :
    cosetShift r ((U : Set G).indicator fun _ => (1 : ℂ)) =
      ((HeckePair.heckeIndicator ℂ g hfin : HeckePair.HeckeAlgebra U ℂ) : G → ℂ) := by
  rw [cosetShift_indicator_eq hsys]
  funext x
  by_cases hx : x ∈ HeckePair.doubleCoset U g
  · rw [Set.indicator_of_mem hx, HeckePair.heckeIndicator_apply_of_mem hfin hx]
  · rw [Set.indicator_of_notMem hx, HeckePair.heckeIndicator_apply_of_notMem hfin hx]

end ShiftIndicator
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem isHeckeCosetSystem_local (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (Uv : Subgroup (GL (Fin 2) (v.adicCompletion K))) (hUv₁ : ∀ x ∈ Uv, embAt K v x ∈ U)
    (hUv₂ : ∀ u ∈ U, compAt K v u ∈ Uv) {g₀ : GL (Fin 2) (v.adicCompletion K)} {n : ℕ}
    {r : Fin n → GL (Fin 2) (v.adicCompletion K)}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U (embAt K v g₀) (fun i => embAt K v (r i))) :
    HeckeIntegralSeam.IsHeckeCosetSystem Uv g₀ r where
  mem_doubleCoset i := by
    obtain ⟨u₁, hu₁, u₂, hu₂, h⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    refine HeckePair.mem_doubleCoset_iff.mpr ⟨compAt K v u₁, hUv₂ u₁ hu₁, compAt K v u₂,
      hUv₂ u₂ hu₂, ?_⟩
    have h' := congrArg (compAt K v) h
    simpa only [compAt_mul, compAt_embAt] using h'
  covers x hx := by
    obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    have hmem : embAt K v (a * g₀ * b) ∈ HeckePair.doubleCoset U (embAt K v g₀) :=
      HeckePair.mem_doubleCoset_iff.mpr ⟨embAt K v a, hUv₁ a ha, embAt K v b, hUv₁ b hb,
        by rw [embAt_mul, embAt_mul]⟩
    obtain ⟨i, hi⟩ := hsys.covers _ hmem
    refine ⟨i, QuotientGroup.eq.mpr ?_⟩
    have h1 := QuotientGroup.eq.mp hi
    have h2 := hUv₂ _ h1
    simpa only [compAt_mul, compAt_inv, compAt_embAt] using h2
  mk_injective i j hij := by
    apply hsys.mk_injective
    have h1 : (r i)⁻¹ * r j ∈ Uv := QuotientGroup.eq.mp hij
    have h2 := hUv₁ _ h1
    rw [embAt_mul, embAt_inv] at h2
    exact QuotientGroup.eq.mpr h2

private theorem embAt_compAt_of_restAt_eq_one {gv : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hgv : restAt K v gv = 1) : embAt K v (compAt K v gv) = gv := by
  rw [embAt_compAt_eq_mul_inv, hgv, inv_one, mul_one]

private theorem exists_local_cosetSystem_of_isHeckeCosetEigenfunctionAt (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (Uv : Subgroup (GL (Fin 2) (v.adicCompletion K)))
    (hsplit : ∀ u ∈ U, embAt K v (compAt K v u) ∈ U)
    (hUv₁ : ∀ x ∈ Uv, embAt K v x ∈ U) (hUv₂ : ∀ u ∈ U, compAt K v u ∈ Uv) {gv : AdelicGL2 (𝓞 K) K}
    (hgv : restAt K v gv = 1) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g) {c : ℂ}
    (h : SmoothCusp.IsHeckeCosetEigenfunctionAt K U gv v φ c) :
    ∃ r : Fin (Ideal.absNorm v.asIdeal + 1) → GL (Fin 2) (v.adicCompletion K),
      HeckeIntegralSeam.IsHeckeCosetSystem Uv (compAt K v gv) r ∧ IsLeftStable Uv r ∧
        ∀ x, ∑ i, φ (x * embAt K v (r i)) = c * φ x := by
  obtain ⟨reps, hsys, heig⟩ := h
  obtain ⟨hsys', htrans⟩ := localize K v U hsplit hgv hsys
  have hsys'' : HeckeIntegralSeam.IsHeckeCosetSystem U (embAt K v (compAt K v gv))
      (fun i => embAt K v (compAt K v (reps i))) := by
    rwa [embAt_compAt_of_restAt_eq_one K v hgv]
  refine ⟨fun i => compAt K v (reps i), isHeckeCosetSystem_local K v U Uv hUv₁ hUv₂ hsys'',
    isLeftStable_local K v U Uv hUv₁ hUv₂ (isLeftStable_of_isHeckeCosetSystem hsys'),
    fun x => (htrans φ hφ x).trans ?_⟩
  exact heig x

end HeckeShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

namespace HeckeShift

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem isLocalLevelOne_mapMatrix {N : Ideal (𝓞 K)}
    {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (h : AdelicLevel.IsLevelOneMatrix (𝓞 K) K N m) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v N ((AdelicLevel.finAdeleEval (𝓞 K) K v).mapMatrix m) := by
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply]
    exact h.integral i j v
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.finAdeleEval_apply]
    exact h.lowerLeft v
  · rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← map_one (AdelicLevel.finAdeleEval (𝓞 K) K v),
      ← map_sub, AdelicLevel.finAdeleEval_apply]
    exact h.lowerRight v

private theorem compAt_mem_localLevelOne {N : Ideal (𝓞 K)} {y : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hy : y ∈ AdelicLevel.levelOne (𝓞 K) K N) : compAt K v y ∈ AdelicDock.localLevelOne (𝓞 K) K v N := by
  have hy' := (AdelicLevel.mem_finiteLevelOne_iff.mp (AdelicLevel.mem_levelOne_iff.mp hy))
  rw [← map_inv] at hy'
  rw [AdelicDock.mem_localLevelOne_iff, ← compAt_inv, coe_compAt, coe_compAt]
  exact ⟨isLocalLevelOne_mapMatrix K v hy'.1, isLocalLevelOne_mapMatrix K v hy'.2⟩

private theorem embAt_mem_levelOne_inf {N : Ideal (𝓞 K)} {k : GL (Fin 2) (v.adicCompletion K)}
    (hk : k ∈ AdelicDock.localLevelOne (𝓞 K) K v N) :
    embAt K v k ∈ AdelicLevel.levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (AdelicDock.finEmbed_mem_levelOne_iff (𝓞 K) K _).mpr
      ((AdelicDock.localEmbed_mem_finiteLevelOne_iff (𝓞 K) K v k).mpr hk)
  · exact (mem_finiteAdelicGL2Subgroup_iff K _).mpr (AdelicDock.glArch_finEmbed (𝓞 K) K _)

private theorem compAt_mem_localLevelOne_of_mem_inf {N : Ideal (𝓞 K)} {u : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hu : u ∈ AdelicLevel.levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) :
    compAt K v u ∈ AdelicDock.localLevelOne (𝓞 K) K v N :=
  compAt_mem_localLevelOne K v (Subgroup.mem_inf.mp hu).1

private theorem embAt_compAt_mem_levelOne_inf {N : Ideal (𝓞 K)} {u : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hu : u ∈ AdelicLevel.levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) :
    embAt K v (compAt K v u) ∈ AdelicLevel.levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K :=
  embAt_mem_levelOne_inf K v (compAt_mem_localLevelOne_of_mem_inf K v hu)

private theorem isLocalLevelOne_iff_of_not_dvd {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N)
    (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    AdelicDock.IsLocalLevelOne (𝓞 K) K v N m ↔ ∀ i j, m i j ∈ v.adicCompletionIntegers K := by
  have hb : AdelicLevel.idealBound (𝓞 K) N v = 1 := AdelicLevel.idealBound_eq_one_of_not_dvd hN hv
  refine ⟨fun h => h.integral, fun h => ⟨h, ?_, ?_⟩⟩
  · rw [hb]
    exact h 1 0
  · rw [hb]
    exact sub_mem (h 1 1) (one_mem _)

private theorem coe_localLevelOne_of_not_dvd {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N) :
    (AdelicDock.localLevelOne (𝓞 K) K v N : Set (GL (Fin 2) (v.adicCompletion K))) =
      localIntegralSet K v := by
  ext k
  rw [SetLike.mem_coe, AdelicDock.mem_localLevelOne_iff, isLocalLevelOne_iff_of_not_dvd K v hN hv,
    isLocalLevelOne_iff_of_not_dvd K v hN hv, mem_localIntegralSet]

private theorem coe_integralSubgroup_eq_localIntegralSet :
    (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :
        Set (GL (Fin 2) (v.adicCompletion K))) = localIntegralSet K v := by
  ext g
  rw [SetLike.mem_coe, FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem
    (fun a b h => Subtype.ext h), mem_localIntegralSet]
  have hr : ∀ x : v.adicCompletion K,
      x ∈ Set.range (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) ↔
        x ∈ v.adicCompletionIntegers K := fun x =>
    ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  simp only [hr]

private theorem localLevelOne_eq_integralSubgroup_of_not_dvd {N : Ideal (𝓞 K)} (hN : N ≠ ⊥)
    (hv : ¬ v.asIdeal ∣ N) :
    AdelicDock.localLevelOne (𝓞 K) K v N =
      LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  SetLike.coe_injective
    ((coe_localLevelOne_of_not_dvd K v hN hv).trans (coe_integralSubgroup_eq_localIntegralSet K v).symm)

private theorem compAt_weyl_mem_localLevelOne {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N) :
    compAt K v (AdelicLevel.weyl (𝓞 K) K) ∈ AdelicDock.localLevelOne (𝓞 K) K v N := by
  rw [← SetLike.mem_coe, coe_localLevelOne_of_not_dvd K v hN hv, mem_localIntegralSet, ← compAt_inv,
    coe_compAt, coe_compAt]
  refine ⟨fun i j => ?_, fun i j => ?_⟩ <;>
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] <;>
    fin_cases i <;> fin_cases j <;>
    simp only [AdelicLevel.weyl, Units.inv_mk, Units.val_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue, map_zero,
      map_one] <;>
    first | exact zero_mem _ | exact one_mem _

private theorem inv_mul_embAt_mul (W : GL (Fin 2) (AdeleRing (𝓞 K) K)) (k : GL (Fin 2) (v.adicCompletion K)) :
    W⁻¹ * embAt K v k * W = embAt K v ((compAt K v W)⁻¹ * k * compAt K v W) := by
  have hW := embAt_compAt_mul_restAt K v W
  have hRe : ∀ z, Commute (restAt K v W) (embAt K v z) := fun z =>
    (embAt_mul_comm_of_compAt_eq_one K v z _ (compAt_restAt K v W) : Commute (embAt K v z) _).symm
  have hX : Commute (restAt K v W)
      ((embAt K v (compAt K v W))⁻¹ * embAt K v k * embAt K v (compAt K v W)) :=
    ((hRe _).inv_right.mul_right (hRe k)).mul_right (hRe _)
  rw [embAt_mul, embAt_mul, embAt_inv]
  calc W⁻¹ * embAt K v k * W
      = (embAt K v (compAt K v W) * restAt K v W)⁻¹ * embAt K v k *
          (embAt K v (compAt K v W) * restAt K v W) := by rw [hW]
    _ = (restAt K v W)⁻¹ *
          (((embAt K v (compAt K v W))⁻¹ * embAt K v k * embAt K v (compAt K v W)) * restAt K v W) := by
        simp only [mul_inv_rev, mul_assoc]
    _ = (restAt K v W)⁻¹ * (restAt K v W *
          ((embAt K v (compAt K v W))⁻¹ * embAt K v k * embAt K v (compAt K v W))) := by rw [← hX.eq]
    _ = (embAt K v (compAt K v W))⁻¹ * embAt K v k * embAt K v (compAt K v W) := inv_mul_cancel_left _ _

private theorem embAt_mem_principalLevel_inf {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion K)} (hk : k ∈ AdelicDock.localLevelOne (𝓞 K) K v N) :
    embAt K v k ∈ AdelicLevel.principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  have h1 := embAt_mem_levelOne_inf K v hk
  have hw := compAt_weyl_mem_localLevelOne K v (N := N) hN hv
  refine Subgroup.mem_inf.mpr ⟨(AdelicLevel.mem_principalLevel_iff (𝓞 K) K N).mpr
    ⟨(Subgroup.mem_inf.mp h1).1, ?_⟩, (Subgroup.mem_inf.mp h1).2⟩
  refine Subgroup.mem_map.mpr ⟨(AdelicLevel.weyl (𝓞 K) K)⁻¹ * embAt K v k * AdelicLevel.weyl (𝓞 K) K,
    ?_, ?_⟩
  · rw [inv_mul_embAt_mul]
    exact (Subgroup.mem_inf.mp (embAt_mem_levelOne_inf K v
      (mul_mem (mul_mem (inv_mem hw) hk) hw))).1
  · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private theorem localLevelOne_data_of_not_dvd {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N) :
    (∀ u ∈ AdelicLevel.levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        embAt K v (compAt K v u) ∈ AdelicLevel.levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) ∧
      (∀ u ∈ AdelicLevel.levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        compAt K v u ∈ AdelicDock.localLevelOne (𝓞 K) K v N) ∧
      (∀ x ∈ AdelicDock.localLevelOne (𝓞 K) K v N,
        embAt K v x ∈ AdelicLevel.principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) ∧
      ∀ u ∈ AdelicLevel.principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        compAt K v u ∈ AdelicDock.localLevelOne (𝓞 K) K v N :=
  ⟨fun _ hu => embAt_compAt_mem_levelOne_inf K v hu, fun _ hu => compAt_mem_localLevelOne_of_mem_inf K v hu,
    fun _ hx => embAt_mem_principalLevel_inf K v hN hv hx, fun _ hu =>
      compAt_mem_localLevelOne K v (AdelicLevel.principalLevel_le_levelOne (𝓞 K) K N (Subgroup.mem_inf.mp hu).1)⟩

end HeckeShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

namespace HeckeShift

section GLMap

private theorem coe_glMap {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (g : GL (Fin 2) A) :
    ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) =
      f.mapMatrix (g : Matrix (Fin 2) (Fin 2) A) := by
  simp only [Matrix.GeneralLinearGroup.map, Units.coe_map]
  rfl

private theorem glMap_comp_piRingHom_eq_one {A : Type*} [CommRing A] {ι : Type*} {B : ι → Type*}
    [∀ i, CommRing (B i)] {C : Type*} [CommRing C] (E : (∀ i, B i) →+* C) (F : ∀ i, A →+* B i)
    (g : GL (Fin 2) A) (hg : ∀ i, Matrix.GeneralLinearGroup.map (F i) g = 1) :
    Matrix.GeneralLinearGroup.map (E.comp (RingHom.pi F)) g = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [coe_glMap, Units.val_one, RingHom.mapMatrix_apply, Matrix.map_apply]
  have hone : (E.comp (RingHom.pi F)) ((1 : Matrix (Fin 2) (Fin 2) A) i j) =
      (1 : Matrix (Fin 2) (Fin 2) C) i j := by
    rw [← Matrix.map_apply (f := E.comp (RingHom.pi F)), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [← hone]
  simp only [RingHom.comp_apply]
  congr 1
  funext k
  have hentry := congrArg (fun u : GL (Fin 2) (B k) => (u : Matrix (Fin 2) (Fin 2) (B k)) i j) (hg k)
  simp only [coe_glMap, Units.val_one, RingHom.mapMatrix_apply, Matrix.map_apply] at hentry
  show F k ((g : Matrix (Fin 2) (Fin 2) A) i j) = F k ((1 : Matrix (Fin 2) (Fin 2) A) i j)
  rw [hentry, ← Matrix.map_apply (f := F k), Matrix.map_one _ (map_zero _) (map_one _)]

end GLMap
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

end HeckeShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

namespace HeckeShift

open TensorProduct
open scoped TensorProduct.RightActions

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 K))

private noncomputable def semiEmb (x : GL (Fin 2) (w.adicCompletion L)) :
    GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
  semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w x)

private theorem semiLocalComponent_localEmbed (x : GL (Fin 2) (w.adicCompletion L)) :
    semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w x) = semiEmb K L w v x := rfl

private theorem semiLocalComponent_localEmbed_of_ne (hw : w.under (𝓞 K) = v) {v' : HeightOneSpectrum (𝓞 K)}
    (hv' : v' ≠ v) (x : GL (Fin 2) (w.adicCompletion L)) :
    semiLocalComponent K L v' (AdelicDock.localEmbed (𝓞 L) L w x) = 1 := by
  unfold semiLocalComponent semiLocalEval
  exact glMap_comp_piRingHom_eq_one _ _ _ fun w' =>
    AdelicDock.finComponent_localEmbed_of_ne (𝓞 L) L w x fun e => hv' (by rw [← w'.2, e, hw])

private theorem isSemiLocalFactorization_heckeShift [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (hw : w.under (𝓞 K) = v) (S : Finset (HeightOneSpectrum (𝓞 K))) (hv : v ∉ S)
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ}
    {φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {φS : ∀ v' : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v'.adicCompletion K) → ℂ}
    (h : IsSemiLocalFactorization K L S φ φa φf φS) {n : ℕ} (r : Fin n → GL (Fin 2) (w.adicCompletion L)) :
    IsSemiLocalFactorization K L (insert v S) (heckeShift L (fun i => embAt L w (r i)) φ) φa
      (cosetShift (fun i => AdelicDock.localEmbed (𝓞 L) L w (r i)) φf)
      (Function.update φS v
        (cosetShift (fun i => semiEmb K L w v (r i))
          ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)))) := by
  obtain ⟨hφa, hφf, hφS, hprod, hzero, hfac⟩ := h
  refine ⟨hφa, ⟨cosetShift_isLocallyConstant _ hφf.1, cosetShift_hasCompactSupport _ hφf.2⟩,
    ?_, ?_, ?_, ?_⟩
  · intro v' hv'
    by_cases hv'v : v' = v
    · rw [hv'v, Function.update_self]
      haveI : ContinuousMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :=
        (isTopologicalGroup_tensorGL K L (v.adicCompletion K)).toContinuousMul
      obtain ⟨hlc, hcs⟩ := isSemiLocalTestFn_indicator_semiLocalIntegralSet K L v
      exact ⟨cosetShift_isLocallyConstant _ hlc, cosetShift_hasCompactSupport _ hcs⟩
    · rw [Function.update_of_ne hv'v]
      exact hφS v' ((Finset.mem_insert.mp hv').resolve_left hv'v)
  · intro g hint
    rw [Finset.prod_insert hv, Function.update_self]
    have hprodS : ∏ v' ∈ S, Function.update φS v
          (cosetShift (fun i => semiEmb K L w v (r i))
            ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))) v'
            (semiLocalComponent K L v' g) =
        ∏ v' ∈ S, φS v' (semiLocalComponent K L v' g) :=
      Finset.prod_congr rfl fun v' hv' => by
        rw [Function.update_of_ne (fun e => hv (by rw [← e]; exact hv'))]
    rw [hprodS, cosetShift_apply]
    refine sum_eq_cosetShift_indicator_mul (fun i => semiEmb K L w v (r i)) (semiLocalIntegralSet K L v)
      (semiLocalComponent K L v g) _
      (fun i => φf ((AdelicDock.localEmbed (𝓞 L) L w (r i))⁻¹ * g)) ?_ ?_
    · intro i hi
      show φf ((AdelicDock.localEmbed (𝓞 L) L w (r i))⁻¹ * g) = _
      rw [hprod _ ?_]
      · refine Finset.prod_congr rfl fun v' hv' => ?_
        rw [map_mul, map_inv, semiLocalComponent_localEmbed_of_ne K L w v hw
          (fun e => hv (by rw [← e]; exact hv')), inv_one, one_mul]
      · intro v' hv'S
        rw [map_mul, map_inv]
        by_cases hv'v : v' = v
        · subst hv'v
          rw [semiLocalComponent_localEmbed]
          exact hi
        · rw [semiLocalComponent_localEmbed_of_ne K L w v hw hv'v, inv_one, one_mul]
          exact hint v' fun hmem => (Finset.mem_insert.mp hmem).elim hv'v hv'S
    · intro i hi
      show φf ((AdelicDock.localEmbed (𝓞 L) L w (r i))⁻¹ * g) = 0
      refine hzero _ ⟨v, hv, ?_⟩
      rw [map_mul, map_inv, semiLocalComponent_localEmbed]
      exact hi
  · rintro g ⟨v', hv', hv'int⟩
    have hv'v : v' ≠ v := fun e => hv' (by rw [e]; exact Finset.mem_insert_self v S)
    have hv'S : v' ∉ S := fun e => hv' (Finset.mem_insert_of_mem e)
    rw [cosetShift_apply]
    refine Finset.sum_eq_zero fun i _ => hzero _ ⟨v', hv'S, ?_⟩
    rw [map_mul, map_inv, semiLocalComponent_localEmbed_of_ne K L w v hw hv'v, inv_one, one_mul]
    exact hv'int
  · intro g
    simp only [heckeShift, cosetShift_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfac, map_mul, map_inv, map_mul, map_inv, embAt, AdelicDock.glArch_finEmbed,
      AdelicDock.glFin_finEmbed, inv_one, one_mul]

private theorem isUnitFactorizableAboveOfType_heckeShift [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (hw : w.under (𝓞 K) = v) (tys : ArchTypeFamily L) (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hv : v ∉ S) {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U S φ) {n : ℕ}
    (r : Fin n → GL (Fin 2) (w.adicCompletion L))
    (hleft : ∀ u ∈ U, ∀ x, heckeShift L (fun i => embAt L w (r i)) φ (u * x) =
      heckeShift L (fun i => embAt L w (r i)) φ x) :
    IsUnitFactorizableAboveOfType K L tys U (insert v S) (heckeShift L (fun i => embAt L w (r i)) φ) := by
  obtain ⟨⟨hbi, φa, φf, φS, hfac⟩, harch⟩ := hφ
  exact ⟨⟨heckeShift_isBiInvariantUnder L U hbi _ hleft, φa, _, _,
    isSemiLocalFactorization_heckeShift K L w v hw S hv hfac r⟩, isArchBiFinite_heckeShift L w tys harch r⟩

private theorem isUnitFactorizableAboveOfType_heckeShift_of_isLeftStable [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (hw : w.under (𝓞 K) = v) (tys : ArchTypeFamily L) (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 L) L)))
    (Uw : Subgroup (GL (Fin 2) (w.adicCompletion L))) (hUw₁ : ∀ x ∈ Uw, embAt L w x ∈ U)
    (hUw₂ : ∀ u ∈ U, compAt L w u ∈ Uw) (S : Finset (HeightOneSpectrum (𝓞 K))) (hv : v ∉ S)
    {φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ} (hφ : IsUnitFactorizableAboveOfType K L tys U S φ) {n : ℕ}
    {r : Fin n → GL (Fin 2) (w.adicCompletion L)} (hr : IsLeftStable Uw r) :
    IsUnitFactorizableAboveOfType K L tys U (insert v S) (heckeShift L (fun i => embAt L w (r i)) φ) :=
  isUnitFactorizableAboveOfType_heckeShift K L w v hw tys U S hv hφ r fun _u hu x =>
    heckeShift_apply_mul_eq_of_isLeftStable L w U Uw hUw₁ hUw₂ hφ.1.1 hr hu x

end HeckeShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

namespace HeckeShift

section Uniformiser

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

private theorem isUnit_of_valued_eq_one {a : v.adicCompletionIntegers K}
    (ha : Valued.v (a : v.adicCompletion K) = 1) : IsUnit a := by
  have ha0 : (a : v.adicCompletion K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ha
    exact zero_ne_one ha
  have hmem : (a : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ha, inv_one]
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

private theorem irreducible_of_valued_eq_exp_neg_one (ϖ : v.adicCompletionIntegers K)
    (h : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) : Irreducible ϖ := by
  have hle : ∀ x : v.adicCompletionIntegers K, Valued.v (x : v.adicCompletion K) ≤ 1 := fun x => x.2
  have hlt : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
    simpa using (WithZero.exp_lt_exp.mpr (show (-1 : ℤ) < 0 by norm_num))
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · obtain ⟨u, rfl⟩ := hu
    have h1 := congrArg (fun x : v.adicCompletionIntegers K => Valued.v (x : v.adicCompletion K)) u.mul_inv
    simp only [MulMemClass.coe_mul, map_mul, OneMemClass.coe_one, map_one] at h1
    rw [h] at h1
    have h2 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-1 : ℤ) :=
      calc (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (-1 : ℤ) *
            Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) :
              v.adicCompletion K) := h1.symm
        _ ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr; exact hle _
        _ = WithZero.exp (-1 : ℤ) := mul_one _
    exact absurd h2 (not_le.mpr hlt)
  · have hv := congrArg (fun x : v.adicCompletionIntegers K => Valued.v (x : v.adicCompletion K)) hab
    simp only [MulMemClass.coe_mul, map_mul] at hv
    rw [h] at hv
    have ha0 : Valued.v (a : v.adicCompletion K) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hv
      exact WithZero.exp_ne_zero hv
    have hb0 : Valued.v (b : v.adicCompletion K) ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hv
      exact WithZero.exp_ne_zero hv
    have hlog := congrArg WithZero.log hv
    rw [WithZero.log_exp, WithZero.log_mul ha0 hb0] at hlog
    have hla : WithZero.log (Valued.v (a : v.adicCompletion K)) ≤ 0 :=
      (WithZero.log_le_iff_le_exp ha0).mpr (by rw [WithZero.exp_zero]; exact hle a)
    have hlb : WithZero.log (Valued.v (b : v.adicCompletion K)) ≤ 0 :=
      (WithZero.log_le_iff_le_exp hb0).mpr (by rw [WithZero.exp_zero]; exact hle b)
    rcases (by omega : WithZero.log (Valued.v (a : v.adicCompletion K)) = 0 ∨
        WithZero.log (Valued.v (b : v.adicCompletion K)) = 0) with h0 | h0
    · exact Or.inl (isUnit_of_valued_eq_one v (by rw [← WithZero.exp_log ha0, h0, WithZero.exp_zero]))
    · exact Or.inr (isUnit_of_valued_eq_one v (by rw [← WithZero.exp_log hb0, h0, WithZero.exp_zero]))

end Uniformiser
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

section GenData

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem compAt_eq_and_restAt_eq_one_of_embAt_eq {x : GL (Fin 2) (v.adicCompletion K)}
    {g : GL (Fin 2) (AdeleRing (𝓞 K) K)} (h : embAt K v x = g) :
    compAt K v g = x ∧ restAt K v g = 1 := by
  subst h
  exact ⟨compAt_embAt K v x, restAt_embAt K v x⟩

private theorem genData (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hval : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    (hgen : AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v (LocalGL2.diagPi ϖ hϖ0)) =
      AdelicLevel.heckeGen (𝓞 K) K v) :
    Irreducible ϖ ∧ compAt K v (AdelicLevel.heckeGen (𝓞 K) K v) = LocalGL2.diagPi ϖ hϖ0 ∧
      restAt K v (AdelicLevel.heckeGen (𝓞 K) K v) = 1 :=
  ⟨irreducible_of_valued_eq_exp_neg_one v ϖ hval, compAt_eq_and_restAt_eq_one_of_embAt_eq K v hgen⟩

end GenData
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

end HeckeShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

namespace HeckeShift

section WordShift

variable {G : Type*} [Group G]

private theorem sum_prodWord_inv_mul_eq {n : ℕ} (reps : Fin n → G) (h : G → ℂ) :
    ∀ (k : ℕ) (x : G), ∑ ι : Fin k → Fin n, h ((prodWord reps k ι)⁻¹ * x) = (cosetShift reps)^[k] h x
  | 0, x => by simp
  | k + 1, x => by
    rw [Function.iterate_succ_apply', cosetShift_apply,
      ← (Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_prodWord_inv_mul_eq reps h k]
    refine Finset.sum_congr rfl fun ι' _ => ?_
    show h ((prodWord reps (k + 1) (Fin.cons i ι'))⁻¹ * x) = _
    rw [prodWord_succ, Fin.cons_zero, Fin.tail_cons, mul_inv_rev, mul_assoc]

private theorem cosetShift_powReps {n : ℕ} (reps : Fin n → G) (k : ℕ) (h : G → ℂ) :
    cosetShift (powReps reps k) h = (cosetShift reps)^[k] h := by
  funext x
  rw [cosetShift_apply, ← sum_prodWord_inv_mul_eq reps h k x]
  exact (Fintype.equivFin (Fin k → Fin n)).symm.sum_comp fun ι => h ((prodWord reps k ι)⁻¹ * x)

private theorem finsum_eq_sum_of_system {U : Subgroup G} {n : ℕ} (r : Fin n → G)
    (hinj : Function.Injective fun i => (QuotientGroup.mk (r i) : G ⧸ U)) (F : G ⧸ U → ℂ)
    (hF : ∀ y : G, F (QuotientGroup.mk y) ≠ 0 → ∃ i, (QuotientGroup.mk y : G ⧸ U) = QuotientGroup.mk (r i)) :
    ∑ᶠ c, F c = ∑ i, F (QuotientGroup.mk (r i)) := by
  classical
  have hsupp : Function.support F ⊆
      ↑(Finset.univ.image fun i => (QuotientGroup.mk (r i) : G ⧸ U)) := by
    intro c hc
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨i, hi⟩ := hF y hc
    rw [Finset.coe_image]
    exact ⟨i, Finset.mem_coe.mpr (Finset.mem_univ i), hi.symm⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image fun i _ j _ hij => hinj hij]

end WordShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

section Mult

variable {G : Type*} [Group G] {U : Subgroup G}

private theorem coe_mul_eq_cosetShift {g : G} {n : ℕ} {r : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g r) {T : HeckePair.HeckeAlgebra U ℂ}
    (hT : (T : G → ℂ) = (HeckePair.doubleCoset U g).indicator fun _ => (1 : ℂ))
    (f : HeckePair.HeckeAlgebra U ℂ) :
    ((T * f : HeckePair.HeckeAlgebra U ℂ) : G → ℂ) = cosetShift r (f : G → ℂ) := by
  funext x
  rw [HeckePair.mul_apply, cosetShift_apply, finsum_eq_sum_of_system r hsys.mk_injective]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [HeckePair.convTerm_mk, hT, Set.indicator_of_mem (hsys.mem_doubleCoset i), one_mul]
  · intro y hy
    rw [HeckePair.convTerm_mk, hT] at hy
    refine hsys.covers y ?_
    by_contra hmem
    exact hy (by rw [Set.indicator_of_notMem hmem, zero_mul])

private theorem coe_pow_mul_eq_iterate {g : G} {n : ℕ} {r : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g r) {T : HeckePair.HeckeAlgebra U ℂ}
    (hT : (T : G → ℂ) = (HeckePair.doubleCoset U g).indicator fun _ => (1 : ℂ))
    (f : HeckePair.HeckeAlgebra U ℂ) :
    ∀ k : ℕ, ((T ^ k * f : HeckePair.HeckeAlgebra U ℂ) : G → ℂ) = (cosetShift r)^[k] (f : G → ℂ)
  | 0 => by rw [pow_zero, one_mul, Function.iterate_zero_apply]
  | k + 1 => by
    rw [pow_succ', mul_assoc, coe_mul_eq_cosetShift hsys hT, coe_pow_mul_eq_iterate hsys hT f k,
      Function.iterate_succ_apply']

private theorem coe_one_eq_indicator :
    ((1 : HeckePair.HeckeAlgebra U ℂ) : G → ℂ) = (U : Set G).indicator fun _ => (1 : ℂ) := rfl

private theorem cosetShift_powReps_indicator_eq_coe_pow {g : G} {n : ℕ} {r : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g r) {T : HeckePair.HeckeAlgebra U ℂ}
    (hT : (T : G → ℂ) = (HeckePair.doubleCoset U g).indicator fun _ => (1 : ℂ)) (k : ℕ) :
    cosetShift (powReps r k) ((U : Set G).indicator fun _ => (1 : ℂ)) =
      ((T ^ k : HeckePair.HeckeAlgebra U ℂ) : G → ℂ) := by
  rw [cosetShift_powReps, ← coe_one_eq_indicator, ← coe_pow_mul_eq_iterate hsys hT 1 k, mul_one]

end Mult
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

section Level

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem unitFactor_powReps_eq_coe_pow {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N)
    {g : GL (Fin 2) (v.adicCompletion K)} {n : ℕ} {r : Fin n → GL (Fin 2) (v.adicCompletion K)}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem (AdelicDock.localLevelOne (𝓞 K) K v N) g r)
    {T : HeckePair.HeckeAlgebra (AdelicDock.localLevelOne (𝓞 K) K v N) ℂ}
    (hT : (T : GL (Fin 2) (v.adicCompletion K) → ℂ) =
      (HeckePair.doubleCoset (AdelicDock.localLevelOne (𝓞 K) K v N) g).indicator fun _ => (1 : ℂ))
    (k : ℕ) :
    cosetShift (powReps r k) ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) =
      ((T ^ k : HeckePair.HeckeAlgebra (AdelicDock.localLevelOne (𝓞 K) K v N) ℂ) :
        GL (Fin 2) (v.adicCompletion K) → ℂ) := by
  rw [← coe_localLevelOne_of_not_dvd K v hN hv, cosetShift_powReps_indicator_eq_coe_pow hsys hT k]

end Level
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

end HeckeShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

namespace HeckeShift

section ShiftAlgebra

variable {G : Type*} [Group G]

private theorem cosetShift_smul {n : ℕ} (reps : Fin n → G) (c : ℂ) (h : G → ℂ) :
    cosetShift reps (c • h) = c • cosetShift reps h := by
  funext x
  simp only [cosetShift_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]

private theorem iterate_cosetShift_smul {n : ℕ} (reps : Fin n → G) (c : ℂ) (h : G → ℂ) :
    ∀ k : ℕ, (cosetShift reps)^[k] (c • h) = c • (cosetShift reps)^[k] h
  | 0 => by simp only [Function.iterate_zero_apply]
  | k + 1 => by
    rw [Function.iterate_succ_apply', iterate_cosetShift_smul reps c h k, cosetShift_smul,
      Function.iterate_succ_apply']

private theorem cosetShift_mulReps {n₁ n₂ : ℕ} (reps₁ : Fin n₁ → G) (reps₂ : Fin n₂ → G) (h : G → ℂ) :
    cosetShift (mulReps reps₁ reps₂) h = cosetShift reps₁ (cosetShift reps₂ h) := by
  funext x
  rw [cosetShift_apply, cosetShift_apply]
  simp only [cosetShift_apply]
  rw [← Fintype.sum_prod_type']
  refine ((Fintype.equivFin (Fin n₁ × Fin n₂)).symm.sum_comp fun p : Fin n₁ × Fin n₂ =>
    h ((reps₁ p.1 * reps₂ p.2)⁻¹ * x)).trans (Fintype.sum_congr _ _ fun p => ?_)
  rw [mul_inv_rev, mul_assoc]

private theorem isHeckeCosetSystem_central (U : Subgroup G) {z : G} (hz : ∀ x, z * x = x * z) :
    HeckeIntegralSeam.IsHeckeCosetSystem U z fun _ : Fin 1 => z where
  mem_doubleCoset _ := HeckePair.self_mem_doubleCoset z
  covers x hx := by
    obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    refine ⟨0, ?_⟩
    rw [QuotientGroup.eq, ← hz u]
    have h : (z * u * u')⁻¹ * z = (u * u')⁻¹ := by group
    rw [h]
    exact inv_mem (mul_mem hu hu')
  mk_injective i j _ := Subsingleton.elim i j

private theorem isLeftStable_central (U : Subgroup G) {z : G} (hz : ∀ x, z * x = x * z) :
    IsLeftStable U fun _ : Fin 1 => z :=
  fun k hk => ⟨1, fun _ => ⟨k⁻¹, inv_mem hk, (hz k⁻¹).symm⟩⟩

variable {U : Subgroup G}

private theorem coe_smul_indicator_mul_eq {g : G} {n : ℕ} {r : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g r) {q : ℂ} {E : HeckePair.HeckeAlgebra U ℂ}
    (hE : (E : G → ℂ) = q • (HeckePair.doubleCoset U g).indicator fun _ => (1 : ℂ))
    (f : HeckePair.HeckeAlgebra U ℂ) :
    ((E * f : HeckePair.HeckeAlgebra U ℂ) : G → ℂ) = q • cosetShift r (f : G → ℂ) := by
  funext x
  rw [HeckePair.mul_apply, Pi.smul_apply, cosetShift_apply, smul_eq_mul, Finset.mul_sum,
    finsum_eq_sum_of_system r hsys.mk_injective]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [HeckePair.convTerm_mk, hE, Pi.smul_apply, Set.indicator_of_mem (hsys.mem_doubleCoset i),
      smul_eq_mul, mul_one]
  · intro y hy
    rw [HeckePair.convTerm_mk, hE, Pi.smul_apply] at hy
    refine hsys.covers y ?_
    by_contra hmem
    exact hy (by rw [Set.indicator_of_notMem hmem, smul_zero, zero_mul])

private theorem coe_pow_mul_eq_smul_iterate {g : G} {n : ℕ} {r : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g r) {q : ℂ} {E : HeckePair.HeckeAlgebra U ℂ}
    (hE : (E : G → ℂ) = q • (HeckePair.doubleCoset U g).indicator fun _ => (1 : ℂ))
    (f : HeckePair.HeckeAlgebra U ℂ) :
    ∀ b : ℕ, ((E ^ b * f : HeckePair.HeckeAlgebra U ℂ) : G → ℂ) = q ^ b • (cosetShift r)^[b] (f : G → ℂ)
  | 0 => by rw [pow_zero, one_mul, pow_zero, one_smul, Function.iterate_zero_apply]
  | b + 1 => by
    rw [pow_succ', mul_assoc, coe_smul_indicator_mul_eq hsys hE, coe_pow_mul_eq_smul_iterate hsys hE f b,
      cosetShift_smul, smul_smul, ← pow_succ', Function.iterate_succ_apply']

private theorem coe_pow_mul_pow_eq_smul_cosetShift {g z : G} {n : ℕ} {r : Fin n → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g r) {T : HeckePair.HeckeAlgebra U ℂ}
    (hT : (T : G → ℂ) = (HeckePair.doubleCoset U g).indicator fun _ => (1 : ℂ))
    (hzsys : HeckeIntegralSeam.IsHeckeCosetSystem U z fun _ : Fin 1 => z) {q : ℂ}
    {E : HeckePair.HeckeAlgebra U ℂ}
    (hE : (E : G → ℂ) = q • (HeckePair.doubleCoset U z).indicator fun _ => (1 : ℂ)) (a b : ℕ) :
    ((T ^ a * E ^ b : HeckePair.HeckeAlgebra U ℂ) : G → ℂ) =
      q ^ b • cosetShift (mulReps (powReps r a) (powReps (fun _ : Fin 1 => z) b))
        ((U : Set G).indicator fun _ => (1 : ℂ)) := by
  have hEb : ((E ^ b : HeckePair.HeckeAlgebra U ℂ) : G → ℂ) =
      q ^ b • (cosetShift fun _ : Fin 1 => z)^[b] ((1 : HeckePair.HeckeAlgebra U ℂ) : G → ℂ) := by
    rw [← coe_pow_mul_eq_smul_iterate hzsys hE 1 b, mul_one]
  rw [coe_pow_mul_eq_iterate hsys hT (E ^ b) a, hEb, iterate_cosetShift_smul, cosetShift_mulReps,
    cosetShift_powReps, cosetShift_powReps, coe_one_eq_indicator]

end ShiftAlgebra
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

section Scalar

variable {F : Type*} [Field F]

private def centralGL (c : F) (hc : c ≠ 0) : GL (Fin 2) F :=
  ⟨c • (1 : Matrix (Fin 2) (Fin 2) F), c⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F),
    by rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hc, one_smul],
    by rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hc, one_smul]⟩

private theorem coe_centralGL_mul (c : F) (hc : c ≠ 0) (x : GL (Fin 2) F) :
    ((centralGL c hc * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = c • (x : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul]
  show c • (1 : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = _
  rw [smul_mul_assoc, one_mul]

private theorem centralGL_comm (c : F) (hc : c ≠ 0) (x : GL (Fin 2) F) : centralGL c hc * x = x * centralGL c hc := by
  apply Units.ext
  rw [coe_centralGL_mul, Units.val_mul]
  show _ = (x : Matrix (Fin 2) (Fin 2) F) * (c • (1 : Matrix (Fin 2) (Fin 2) F))
  rw [mul_smul_comm, mul_one]

private theorem coe_eq_smul_iff (c : F) (hc : c ≠ 0) (x u : GL (Fin 2) F) :
    (x : Matrix (Fin 2) (Fin 2) F) = c • (u : Matrix (Fin 2) (Fin 2) F) ↔ x = centralGL c hc * u := by
  rw [← coe_centralGL_mul c hc u]
  exact ⟨fun h => Units.ext h, fun h => by rw [h]⟩

private theorem setOf_coe_eq_smul_eq_doubleCoset (U : Subgroup (GL (Fin 2) F)) (c : F) (hc : c ≠ 0) :
    {x : GL (Fin 2) F | ∃ u ∈ U, (x : Matrix (Fin 2) (Fin 2) F) = c • (u : Matrix (Fin 2) (Fin 2) F)} =
      HeckePair.doubleCoset U (centralGL c hc) := by
  ext x
  constructor
  · rintro ⟨u, hu, h⟩
    rw [coe_eq_smul_iff c hc] at h
    exact HeckePair.mem_doubleCoset_iff.mpr ⟨1, one_mem U, u, hu, by rw [one_mul, h]⟩
  · intro hx
    obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    refine ⟨u * u', mul_mem hu hu', ?_⟩
    rw [← centralGL_comm, mul_assoc, coe_centralGL_mul]

private theorem central_data (U : Subgroup (GL (Fin 2) F)) (c : F) (hc : c ≠ 0) {q : ℂ}
    {E : HeckePair.HeckeAlgebra U ℂ}
    (hE : (E : GL (Fin 2) F → ℂ) = q • ({x : GL (Fin 2) F | ∃ u ∈ U,
      (x : Matrix (Fin 2) (Fin 2) F) = c • (u : Matrix (Fin 2) (Fin 2) F)}.indicator fun _ => (1 : ℂ))) :
    HeckeIntegralSeam.IsHeckeCosetSystem U (centralGL c hc) (fun _ : Fin 1 => centralGL c hc) ∧
      IsLeftStable U (fun _ : Fin 1 => centralGL c hc) ∧
      (E : GL (Fin 2) F → ℂ) = q • (HeckePair.doubleCoset U (centralGL c hc)).indicator fun _ => (1 : ℂ) :=
  ⟨isHeckeCosetSystem_central U (centralGL_comm c hc), isLeftStable_central U (centralGL_comm c hc),
    by rw [hE, setOf_coe_eq_smul_eq_doubleCoset U c hc]⟩

end Scalar
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

end HeckeShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

namespace HeckeShift

section WordFamily

variable {G : Type*} [Group G]

private theorem prodWord_eq_ofFn_prod {n : ℕ} (reps : Fin n → G) :
    ∀ (k : ℕ) (ι : Fin k → Fin n), prodWord reps k ι = (List.ofFn fun m => reps (ι m)).prod
  | 0, _ => by simp only [prodWord_zero, List.ofFn_zero, List.prod_nil]
  | k + 1, ι => by
    simp only [prodWord_succ, prodWord_eq_ofFn_prod reps k, List.ofFn_succ, List.prod_cons,
      Fin.tail]

private theorem prodWord_const (z : G) :
    ∀ (j : ℕ) (ι : Fin j → Fin 1), prodWord (fun _ : Fin 1 => z) j ι = z ^ j
  | 0, _ => by simp only [prodWord_zero, pow_zero]
  | j + 1, ι => by rw [prodWord_succ, prodWord_const z j (Fin.tail ι), pow_succ']

private theorem powReps_const_apply (z : G) (j : ℕ) (i : Fin (Fintype.card (Fin j → Fin 1))) :
    powReps (fun _ : Fin 1 => z) j i = z ^ j := by
  simp only [powReps, prodWord_const]

private theorem card_fin_fun_fin_one (j : ℕ) : Fintype.card (Fin (Fintype.card (Fin j → Fin 1))) = 1 := by
  simp

private theorem cosetShift_mulReps_powReps_eq {G' : Type*} [Group G'] (e : G → G') (ind : G' → ℂ) {n : ℕ}
    (rT : Fin n → G) (z : G) (k j : ℕ) :
    cosetShift (fun i => e (mulReps (powReps rT k) (powReps (fun _ : Fin 1 => z) j) i)) ind =
      fun x => ∑ ι : Fin k → Fin n, ind ((e ((List.ofFn fun m => rT (ι m)).prod * z ^ j))⁻¹ * x) := by
  funext x
  simp only [cosetShift_apply, mulReps, powReps_const_apply]
  refine (Fintype.sum_equiv
    (Fintype.equivFin (Fin (Fintype.card (Fin k → Fin n)) × Fin (Fintype.card (Fin j → Fin 1)))).symm
    (fun i => ind ((e (powReps rT k ((Fintype.equivFin
      (Fin (Fintype.card (Fin k → Fin n)) × Fin (Fintype.card (Fin j → Fin 1)))).symm i).1 * z ^ j))⁻¹ * x))
    (fun p => ind ((e (powReps rT k p.1 * z ^ j))⁻¹ * x)) fun _ => rfl).trans ?_
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, card_fin_fun_fin_one, one_nsmul]
  refine (Fintype.sum_equiv (Fintype.equivFin (Fin k → Fin n)).symm
    (fun a => ind ((e (powReps rT k a * z ^ j))⁻¹ * x))
    (fun ι => ind ((e (prodWord rT k ι * z ^ j))⁻¹ * x)) fun _ => rfl).trans ?_
  simp only [prodWord_eq_ofFn_prod]

end WordFamily
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

end HeckeShift
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

open NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open scoped TensorProduct
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

namespace GuardScaling

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

private theorem toEnd_eq_smul {V : Submodule ℂ M} {T₁ T₂ : M → M} (m : ℂ) (hT : ∀ u ∈ V, T₂ u = m • T₁ u)
    (h₁ : IsStableLinearOn V T₁) (h₂ : IsStableLinearOn V T₂) : h₂.toEnd = m • h₁.toEnd := by
  refine LinearMap.ext fun u => Subtype.ext ?_
  rw [IsStableLinearOn.coe_toEnd_apply, LinearMap.smul_apply, Submodule.coe_smul,
    IsStableLinearOn.coe_toEnd_apply]
  exact hT u u.2

private theorem traceOn_eq_mul_of_forall_smul {V : Submodule ℂ M} {T₁ T₂ : M → M} (m : ℂ)
    (hT : ∀ u ∈ V, T₂ u = m • T₁ u) (h₁ : IsStableLinearOn V T₁) (h₂ : IsStableLinearOn V T₂) :
    traceOn V T₂ h₂ = m * traceOn V T₁ h₁ := by
  rw [traceOn_eq, traceOn_eq, toEnd_eq_smul m hT h₁ h₂, map_smul, smul_eq_mul]

private theorem traceOn_eq_zero_of_forall_eq_zero {V : Submodule ℂ M} {T : M → M}
    (hT : ∀ u ∈ V, T u = 0) (h : IsStableLinearOn V T) : traceOn V T h = 0 := by
  have h0 : h.toEnd = 0 := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    rw [IsStableLinearOn.coe_toEnd_apply, LinearMap.zero_apply, Submodule.coe_zero]
    exact hT u u.2
  rw [traceOn_eq, h0, map_zero]

private theorem forall_mem_iff_of_forall_smul {V : Submodule ℂ M} {T₁ T₂ : M → M} {m : ℂ} (hm : m ≠ 0)
    (hT : ∀ u ∈ V, T₂ u = m • T₁ u) : (∀ u ∈ V, T₂ u ∈ V) ↔ ∀ u ∈ V, T₁ u ∈ V := by
  constructor
  · intro h u hu
    have hu' := h u hu
    rw [hT u hu] at hu'
    exact (V.smul_mem_iff hm).mp hu'
  · intro h u hu
    rw [hT u hu]
    exact V.smul_mem m (h u hu)

private theorem dite_traceOn_eq_mul_dite_traceOn {V : Submodule ℂ M} {T₁ T₂ : M → M} (m : ℂ)
    (hT : ∀ u ∈ V, T₂ u = m • T₁ u)
    (mk₁ : (∀ u ∈ V, T₁ u ∈ V) → IsStableLinearOn V T₁)
    (mk₂ : (∀ u ∈ V, T₂ u ∈ V) → IsStableLinearOn V T₂)
    [Decidable (∀ u ∈ V, T₁ u ∈ V)] [Decidable (∀ u ∈ V, T₂ u ∈ V)] :
    (if h : ∀ u ∈ V, T₂ u ∈ V then traceOn V T₂ (mk₂ h) else 0) =
      m * (if h : ∀ u ∈ V, T₁ u ∈ V then traceOn V T₁ (mk₁ h) else 0) := by
  by_cases hm : m = 0
  · have hT0 : ∀ u ∈ V, T₂ u = 0 := fun u hu => by rw [hT u hu, hm, zero_smul]
    have h₂ : ∀ u ∈ V, T₂ u ∈ V := fun u hu => by rw [hT0 u hu]; exact V.zero_mem
    rw [dif_pos h₂, hm, zero_mul]
    exact traceOn_eq_zero_of_forall_eq_zero hT0 (mk₂ h₂)
  · by_cases h₁ : ∀ u ∈ V, T₁ u ∈ V
    · have h₂ : ∀ u ∈ V, T₂ u ∈ V := (forall_mem_iff_of_forall_smul hm hT).mpr h₁
      rw [dif_pos h₂, dif_pos h₁]
      exact traceOn_eq_mul_of_forall_smul m hT (mk₁ h₁) (mk₂ h₂)
    · have h₂ : ¬ ∀ u ∈ V, T₂ u ∈ V := fun h => h₁ ((forall_mem_iff_of_forall_smul hm hT).mp h)
      rw [dif_neg h₂, dif_neg h₁, mul_zero]

private theorem forall_mem_span_eq_smul (s : Set M) (P : M → Prop) (hPs : ∀ u ∈ s, P u) (hP0 : P 0)
    (hPadd : ∀ u w, P u → P w → P (u + w)) (hPsmul : ∀ (a : ℂ) (u : M), P u → P (a • u))
    (T₁ T₂ : M → M) (m : ℂ) (h₁zero : T₁ 0 = 0) (h₂zero : T₂ 0 = 0)
    (h₁add : ∀ u w, P u → P w → T₁ (u + w) = T₁ u + T₁ w)
    (h₂add : ∀ u w, P u → P w → T₂ (u + w) = T₂ u + T₂ w)
    (h₁smul : ∀ (a : ℂ) (u : M), T₁ (a • u) = a • T₁ u)
    (h₂smul : ∀ (a : ℂ) (u : M), T₂ (a • u) = a • T₂ u)
    (hs : ∀ u ∈ s, T₂ u = m • T₁ u) :
    ∀ u ∈ Submodule.span ℂ s, T₂ u = m • T₁ u := by
  intro u hu
  refine (Submodule.span_induction (p := fun u _ => P u ∧ T₂ u = m • T₁ u)
    (mem := fun x hx => ⟨hPs x hx, hs x hx⟩)
    (zero := ⟨hP0, by rw [h₂zero, h₁zero, smul_zero]⟩)
    (add := fun x y _ _ hx hy => ⟨hPadd x y hx.1 hy.1, ?_⟩)
    (smul := fun a x _ hx => ⟨hPsmul a x hx.1, ?_⟩) hu).2
  · rw [h₂add x y hx.1 hy.1, h₁add x y hx.1 hy.1, hx.2, hy.2, smul_add]
  · rw [h₂smul, h₁smul, hx.2]
    exact smul_comm a m (T₁ x)

end GuardScaling
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

open IsDedekindDomain NumberField

namespace GuardScaling

section Untwisted

variable (K : Type) [Field K] [NumberField K]

private theorem convTraceOn_eq_mul_convTraceOn {V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)}
    (hVc : ∀ u ∈ V, Continuous u) {f fm : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfm : Continuous fm) (hfmc : HasCompactSupport fm) (c : ℂ)
    (hV : ∀ u ∈ V, convOp K fm u = c • convOp K f u) :
    convTraceOn K V hVc fm hfm hfmc = c * convTraceOn K V hVc f hf hfc := by
  by_cases hc : c = 0
  · have h0 : ∀ u ∈ V, convOp K fm u = 0 := fun u hu => by rw [hV u hu, hc, zero_smul]
    have h₂ : ∀ u ∈ V, convOp K fm u ∈ V := fun u hu => by rw [h0 u hu]; exact V.zero_mem
    rw [convTraceOn_eq_traceOn K hVc hfm hfmc h₂, hc, zero_mul]
    exact traceOn_eq_zero_of_forall_eq_zero h0 _
  · by_cases h₁ : ∀ u ∈ V, convOp K f u ∈ V
    · have h₂ : ∀ u ∈ V, convOp K fm u ∈ V := (forall_mem_iff_of_forall_smul hc hV).mpr h₁
      rw [convTraceOn_eq_traceOn K hVc hfm hfmc h₂, convTraceOn_eq_traceOn K hVc hf hfc h₁]
      exact traceOn_eq_mul_of_forall_smul c hV _ _
    · have h₂ : ¬ ∀ u ∈ V, convOp K fm u ∈ V := fun h =>
        h₁ ((forall_mem_iff_of_forall_smul hc hV).mp h)
      rw [convTraceOn_eq_zero K hVc hfm hfmc h₂, convTraceOn_eq_zero K hVc hf hfc h₁, mul_zero]

private theorem forall_mem_isotypicCuspSubmodule_convOp_eq_smul (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    {f fm : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfm : Continuous fm) (hfmc : HasCompactSupport fm) (c : ℂ)
    (hgen : ∀ φ, IsIsotypicCuspFormAt K pins ξ N S Ψ φ → convOp K fm φ = c • convOp K f φ) :
    ∀ u ∈ isotypicCuspSubmodule K pins ξ N S Ψ, convOp K fm u = c • convOp K f u :=
  forall_mem_span_eq_smul {φ | IsIsotypicCuspFormAt K pins ξ N S Ψ φ} Continuous
    (fun _ hφ => IsIsotypicCuspFormAt.continuous hφ) continuous_zero
    (fun _ _ hu hw => hu.add hw) (fun a _ hu => hu.const_smul a)
    (convOp K f) (convOp K fm) c (convOp_zero K f) (convOp_zero K fm)
    (fun _ _ hu hw => convOp_add K hf hfc hu hw) (fun _ _ hu hw => convOp_add K hfm hfmc hu hw)
    (convOp_smul K f) (convOp_smul K fm) (fun _ hφ => hgen _ hφ)

private theorem cutTrace_eq_mul_cutTrace (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) (tys : ArchTypeFamily K)
    {f fm : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfm : Continuous fm) (hfmc : HasCompactSupport fm) (c : ℂ)
    (hgen : ∀ φ, IsIsotypicCuspFormAt K pins ξ N S Ψ φ → convOp K fm φ = c • convOp K f φ) :
    cutTrace K pins ξ N S Ψ tys fm hfm hfmc = c * cutTrace K pins ξ N S Ψ tys f hf hfc := by
  simp only [cutTrace_eq]
  exact convTraceOn_eq_mul_convTraceOn K _ hf hfc hfm hfmc c fun u hu =>
    forall_mem_isotypicCuspSubmodule_convOp_eq_smul K pins ξ N S Ψ hf hfc hfm hfmc c hgen u
      (Submodule.mem_inf.mp hu).1

end Untwisted
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

section Twisted

variable (F L : Type) [Field F] [Field L] [NumberField L] [Algebra F L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) F L) (σ : L ≃ₐ[F] L)

private theorem twistedConvTraceOn_eq_mul_twistedConvTraceOn {V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)}
    (hVc : ∀ u ∈ V, Continuous u) {f fm : AdelicGL2 (𝓞 L) L → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfm : Continuous fm) (hfmc : HasCompactSupport fm) (c : ℂ)
    (hV : ∀ u ∈ V, twistedConvOp F L D σ fm u = c • twistedConvOp F L D σ f u) :
    twistedConvTraceOn F L D σ V hVc fm hfm hfmc =
      c * twistedConvTraceOn F L D σ V hVc f hf hfc := by
  by_cases hc : c = 0
  · have h0 : ∀ u ∈ V, twistedConvOp F L D σ fm u = 0 := fun u hu => by
      rw [hV u hu, hc, zero_smul]
    have h₂ : ∀ u ∈ V, twistedConvOp F L D σ fm u ∈ V := fun u hu => by
      rw [h0 u hu]; exact V.zero_mem
    rw [twistedConvTraceOn_eq_traceOn F L D σ hVc hfm hfmc h₂, hc, zero_mul]
    exact traceOn_eq_zero_of_forall_eq_zero h0 _
  · by_cases h₁ : ∀ u ∈ V, twistedConvOp F L D σ f u ∈ V
    · have h₂ : ∀ u ∈ V, twistedConvOp F L D σ fm u ∈ V :=
        (forall_mem_iff_of_forall_smul hc hV).mpr h₁
      rw [twistedConvTraceOn_eq_traceOn F L D σ hVc hfm hfmc h₂,
        twistedConvTraceOn_eq_traceOn F L D σ hVc hf hfc h₁]
      exact traceOn_eq_mul_of_forall_smul c hV _ _
    · have h₂ : ¬ ∀ u ∈ V, twistedConvOp F L D σ fm u ∈ V := fun h =>
        h₁ ((forall_mem_iff_of_forall_smul hc hV).mp h)
      rw [twistedConvTraceOn_eq_zero F L D σ hVc hfm hfmc h₂,
        twistedConvTraceOn_eq_zero F L D σ hVc hf hfc h₁, mul_zero]

private theorem twistedConvOp_zero' (f : AdelicGL2 (𝓞 L) L → ℂ) : twistedConvOp F L D σ f 0 = 0 := by
  simpa using twistedConvOp_smul F L D σ f (0 : ℂ) 0

private theorem forall_mem_isotypicCuspSubmodule_twistedConvOp_eq_smul (pins : CarrierPins L)
    (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (Ψ : HeckeEigensystem L ℂ) {f fm : AdelicGL2 (𝓞 L) L → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfm : Continuous fm) (hfmc : HasCompactSupport fm) (c : ℂ)
    (hgen : ∀ φ, IsIsotypicCuspFormAt L pins ξ N S Ψ φ →
      twistedConvOp F L D σ fm φ = c • twistedConvOp F L D σ f φ) :
    ∀ u ∈ isotypicCuspSubmodule L pins ξ N S Ψ,
      twistedConvOp F L D σ fm u = c • twistedConvOp F L D σ f u :=
  forall_mem_span_eq_smul {φ | IsIsotypicCuspFormAt L pins ξ N S Ψ φ} Continuous
    (fun _ hφ => IsIsotypicCuspFormAt.continuous hφ) continuous_zero
    (fun _ _ hu hw => hu.add hw) (fun a _ hu => hu.const_smul a)
    (twistedConvOp F L D σ f) (twistedConvOp F L D σ fm) c
    (twistedConvOp_zero' F L D σ f) (twistedConvOp_zero' F L D σ fm)
    (fun _ _ hu hw => twistedConvOp_add F L D σ hf hfc hu hw)
    (fun _ _ hu hw => twistedConvOp_add F L D σ hfm hfmc hu hw)
    (twistedConvOp_smul F L D σ f) (twistedConvOp_smul F L D σ fm) (fun _ hφ => hgen _ hφ)

private theorem twistedCutTrace_eq_mul_twistedCutTrace (pins : CarrierPins L) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ)
    (tys : ArchTypeFamily L) {f fm : AdelicGL2 (𝓞 L) L → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfm : Continuous fm) (hfmc : HasCompactSupport fm) (c : ℂ)
    (hgen : ∀ φ, IsIsotypicCuspFormAt L pins ξ N S Ψ φ →
      twistedConvOp F L D σ fm φ = c • twistedConvOp F L D σ f φ) :
    twistedCutTrace F L D σ pins ξ N S Ψ tys fm hfm hfmc =
      c * twistedCutTrace F L D σ pins ξ N S Ψ tys f hf hfc := by
  simp only [twistedCutTrace_eq]
  exact twistedConvTraceOn_eq_mul_twistedConvTraceOn F L D σ _ hf hfc hfm hfmc c fun u hu =>
    forall_mem_isotypicCuspSubmodule_twistedConvOp_eq_smul F L D σ pins ξ N S Ψ hf hfc hfm hfmc c
      hgen u (Submodule.mem_inf.mp hu).1

end Twisted
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

end GuardScaling
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

open HeckeIntegralSeam

namespace CosetIndependence

section DoubleCoset

variable {G : Type*} [Group G] {U : Subgroup G}

private theorem doubleCoset_mul_of_mem (g : G) {u : G} (hu : u ∈ U) :
    HeckePair.doubleCoset U (g * u) = HeckePair.doubleCoset U g := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    exact HeckePair.mem_doubleCoset_iff.mpr ⟨a, ha, u * b, U.mul_mem hu hb, by group⟩
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    exact HeckePair.mem_doubleCoset_iff.mpr
      ⟨a, ha, u⁻¹ * b, U.mul_mem (U.inv_mem hu) hb, by group⟩

private theorem isHeckeCosetSystem_of_doubleCoset_eq {g g' : G}
    (h : HeckePair.doubleCoset U g = HeckePair.doubleCoset U g') {ι : Type*} {reps : ι → G}
    (hs : IsHeckeCosetSystem U g reps) : IsHeckeCosetSystem U g' reps where
  mem_doubleCoset i := by rw [← h]; exact hs.mem_doubleCoset i
  covers x hx := hs.covers x (by rw [h]; exact hx)
  mk_injective := hs.mk_injective

private theorem isHeckeCosetSystem_of_mul_mem {g u : G} (hu : u ∈ U) {ι : Type*} {reps : ι → G}
    (hs : IsHeckeCosetSystem U (g * u) reps) : IsHeckeCosetSystem U g reps :=
  isHeckeCosetSystem_of_doubleCoset_eq (doubleCoset_mul_of_mem g hu) hs

end DoubleCoset
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

section Uniformiser

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private def diagUnits (a b : Rˣ) : GL (Fin 2) R :=
  ⟨Matrix.diagonal ![(a : R), b], Matrix.diagonal ![((a⁻¹ : Rˣ) : R), ((b⁻¹ : Rˣ) : R)], by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp, by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp⟩

@[scoped simp] private theorem coe_diagUnits (a b : Rˣ) :
    (diagUnits a b : Matrix (Fin 2) (Fin 2) R) = Matrix.diagonal ![(a : R), b] := rfl

private theorem map_diagUnits_mem (a b : Rˣ) :
    Matrix.GeneralLinearGroup.map (algebraMap R K) (diagUnits a b) ∈
      LocalGL2.integralSubgroup R K :=
  LocalGL2.mem_integralSubgroup_iff.mpr ⟨diagUnits a b, rfl⟩

private theorem coe_map_diagUnits (a b : Rˣ) :
    (Matrix.GeneralLinearGroup.map (algebraMap R K) (diagUnits a b) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![algebraMap R K a, algebraMap R K b] := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, coe_diagUnits]
  fin_cases i <;> fin_cases j <;> simp

private theorem diagPi_mul_units (ϖ : R) (u : Rˣ) (h0 : algebraMap R K ϖ ≠ 0)
    (h0' : algebraMap R K (ϖ * u) ≠ 0) :
    LocalGL2.diagPi (ϖ * u) h0' =
      LocalGL2.diagPi ϖ h0 * Matrix.GeneralLinearGroup.map (algebraMap R K) (diagUnits u 1) := by
  ext i j
  rw [Units.val_mul, coe_map_diagUnits, LocalGL2.coe_diagPi, LocalGL2.coe_diagPi]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable [IsDomain R] [IsDiscreteValuationRing R]

private theorem isHeckeCosetSystem_diagPi_of_irreducible {ϖ ϖ' : R} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') (h0 : algebraMap R K ϖ ≠ 0) (h0' : algebraMap R K ϖ' ≠ 0)
    {ι : Type*} {reps : ι → GL (Fin 2) K}
    (hs : IsHeckeCosetSystem (LocalGL2.integralSubgroup R K) (LocalGL2.diagPi ϖ' h0') reps) :
    IsHeckeCosetSystem (LocalGL2.integralSubgroup R K) (LocalGL2.diagPi ϖ h0) reps := by
  obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ hϖ'
  rw [diagPi_mul_units ϖ u h0 h0'] at hs
  exact isHeckeCosetSystem_of_mul_mem (map_diagUnits_mem u 1) hs

private theorem exists_mem_integralSubgroup_scalar_eq_mul {ϖ ϖ' : R} (hϖ : Irreducible ϖ)
    (hϖ' : Irreducible ϖ') {z z' : GL (Fin 2) K}
    (hz : (z : Matrix (Fin 2) (Fin 2) K) = algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K))
    (hz' : (z' : Matrix (Fin 2) (Fin 2) K) = algebraMap R K ϖ' • (1 : Matrix (Fin 2) (Fin 2) K)) :
    ∃ s ∈ LocalGL2.integralSubgroup R K, z' = z * s := by
  obtain ⟨u, rfl⟩ := IsDiscreteValuationRing.associated_of_irreducible R hϖ hϖ'
  refine ⟨_, map_diagUnits_mem u u, Units.ext ?_⟩
  rw [Units.val_mul, coe_map_diagUnits, hz, hz', map_mul, mul_smul, Algebra.smul_mul_assoc, one_mul,
    Matrix.smul_one_eq_diagonal]
  congr 2
  funext i
  fin_cases i <;> simp

end Uniformiser
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift"

end CosetIndependence
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.CosetIndependence"

section CosetSumIndependence

open HeckeIntegralSeam

namespace CosetIndependence

section Generic

variable {G : Type*} [Group G] {U : Subgroup G} {g : G}

private theorem exists_equiv_of_isHeckeCosetSystem {ι κ : Type*} {reps : ι → G} {reps' : κ → G}
    (h : IsHeckeCosetSystem U g reps) (h' : IsHeckeCosetSystem U g reps') :
    ∃ e : ι ≃ κ, ∀ i, (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps' (e i)) := by
  choose f hf using fun i => h'.covers (reps i) (h.mem_doubleCoset i)
  have hinj : Function.Injective f := by
    intro i₁ i₂ hi
    apply h.mk_injective
    show (QuotientGroup.mk (reps i₁) : G ⧸ U) = QuotientGroup.mk (reps i₂)
    rw [hf i₁, hf i₂, hi]
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := h.covers (reps' j) (h'.mem_doubleCoset j)
    exact ⟨i, h'.mk_injective ((hf i).symm.trans hi.symm)⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun i => hf i⟩

private theorem sum_eq_of_isHeckeCosetSystem {ι κ : Type*} [Fintype ι] [Fintype κ] {reps : ι → G}
    {reps' : κ → G} (h : IsHeckeCosetSystem U g reps) (h' : IsHeckeCosetSystem U g reps')
    {M : Type*} [AddCommMonoid M] {Φ : G → M} (hinv : ∀ x : G, ∀ u ∈ U, Φ (x * u) = Φ x) :
    ∑ i, Φ (reps i) = ∑ j, Φ (reps' j) := by
  obtain ⟨e, he⟩ := exists_equiv_of_isHeckeCosetSystem h h'
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hu : (reps i)⁻¹ * reps' (e i) ∈ U := QuotientGroup.eq.mp (he i)
  exact (hinv (reps i) _ hu).symm.trans (congrArg Φ (mul_inv_cancel_left (reps i) (reps' (e i))))

end Generic
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.CosetIndependence"

end CosetIndependence
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.CosetIndependence"

end CosetSumIndependence
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.CosetIndependence"

namespace HeckeCore

open HeckeShift

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem sum_apply_mul_embAt_eq_of_isHeckeCosetSystem
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (Uv : Subgroup (GL (Fin 2) (v.adicCompletion F)))
    (hsplit : ∀ u ∈ U, embAt F v (compAt F v u) ∈ U)
    (hUv₁ : ∀ x ∈ Uv, embAt F v x ∈ U) (hUv₂ : ∀ u ∈ U, compAt F v u ∈ Uv)
    {gv : AdelicGL2 (𝓞 F) F} (hgv : restAt F v gv = 1)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hinv : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (g * u) = φ g)
    {c : ℂ} (heig : SmoothCusp.IsHeckeCosetEigenfunctionAt F U gv v φ c)
    {n : ℕ} {rT : Fin n → GL (Fin 2) (v.adicCompletion F)}
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem Uv (compAt F v gv) rT) :
    ∀ x : AdelicGL2 (𝓞 F) F, ∑ i, φ (x * embAt F v (rT i)) = c * φ x := by
  intro x
  obtain ⟨r₀, hr₀, -, hsum⟩ :=
    exists_local_cosetSystem_of_isHeckeCosetEigenfunctionAt F v U Uv hsplit hUv₁ hUv₂ hgv hinv heig
  rw [← hsum x]
  exact CosetIndependence.sum_eq_of_isHeckeCosetSystem hrT hr₀ (Φ := fun r => φ (x * embAt F v r))
    fun y u hu => by
      simp only [embAt_mul, ← mul_assoc]
      exact hinv _ _ (hUv₁ u hu)

private theorem apply_mul_embAt_eq_of_central
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (Uv : Subgroup (GL (Fin 2) (v.adicCompletion F)))
    (hUv₁ : ∀ x ∈ Uv, embAt F v x ∈ U)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hinv : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (g * u) = φ g)
    {zc : AdelicGL2 (𝓞 F) F} (hzc : ∀ g : AdelicGL2 (𝓞 F) F, zc * g = g * zc)
    {b : ℂ} (hcen : ∀ g : AdelicGL2 (𝓞 F) F, φ (zc * g) = b * φ g)
    {z : GL (Fin 2) (v.adicCompletion F)} (hbr : ∃ u ∈ Uv, embAt F v z = zc * embAt F v u) :
    ∀ x : AdelicGL2 (𝓞 F) F, φ (x * embAt F v z) = b * φ x := by
  intro x
  obtain ⟨u, hu, hzu⟩ := hbr
  rw [hzu, ← mul_assoc, hinv _ _ (hUv₁ u hu), ← hzc x]
  exact hcen x

private theorem centralScalar_mul_comm (a : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F a * g = g * centralScalar (𝓞 F) F a := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (a : AdeleRing (𝓞 F) F) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    = (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) * Matrix.scalar (Fin 2) (a : AdeleRing (𝓞 F) F)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

end HeckeCore
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.CosetIndependence"

namespace GenBridge

open IsDedekindDomain NumberField AdelicDock

private theorem scalar_det_mem_integralSubgroup {R₀ K₀ : Type*} [CommRing R₀] [Field K₀] [Algebra R₀ K₀]
    {u : GL (Fin 2) K₀} (hu : u ∈ LocalGL2.integralSubgroup R₀ K₀) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det u) ∈
      LocalGL2.integralSubgroup R₀ K₀ := by
  obtain ⟨y, rfl⟩ := LocalGL2.mem_integralSubgroup_iff.mp hu
  refine LocalGL2.mem_integralSubgroup_iff.mpr
    ⟨CosetIndependence.diagUnits (Matrix.GeneralLinearGroup.det y) (Matrix.GeneralLinearGroup.det y),
      Units.ext ?_⟩
  rw [CosetIndependence.coe_map_diagUnits]
  change Matrix.diagonal _ = Matrix.scalar (Fin 2)
    (Matrix.det ((y : Matrix (Fin 2) (Fin 2) R₀).map (algebraMap R₀ K₀)))
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.scalar_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

variable {K : Type*} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}

private theorem finEmbed_localEmbed_eq_of_components (g : GL (Fin 2) (v.adicCompletion K))
    (G : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (harch : (AdelicLevel.adeleArch (𝓞 K) K).mapMatrix
      (G : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = 1)
    (hself : (AdelicLevel.finAdeleEval (𝓞 K) K v).mapMatrix ((AdelicLevel.adeleFin (𝓞 K) K).mapMatrix
      (G : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) = (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (hne : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v →
      (AdelicLevel.finAdeleEval (𝓞 K) K w).mapMatrix ((AdelicLevel.adeleFin (𝓞 K) K).mapMatrix
        (G : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) = 1) :
    finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v g) = G := by
  refine Units.ext ?_
  rw [coe_finEmbed, coe_localEmbed]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 K) K ?_ ?_
  · rw [mapMatrix_arch_finMat, harch]
  · rw [mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K fun w => ?_
    by_cases hw : w = v
    · rw [hw, mapMatrix_localMat_self, hself]
    · rw [mapMatrix_localMat_of_ne (𝓞 K) K v _ hw, hne w hw]

private theorem adeleArch_det_finEmbed_localEmbed (g : GL (Fin 2) (v.adicCompletion K)) :
    AdelicLevel.adeleArch (𝓞 K) K
      (Matrix.det (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v g) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)))
      = 1 := by
  rw [coe_finEmbed, coe_localEmbed, RingHom.map_det, mapMatrix_arch_finMat, Matrix.det_one]

private theorem finAdeleEval_adeleFin_det_finEmbed_localEmbed_self (g : GL (Fin 2) (v.adicCompletion K)) :
    AdelicLevel.finAdeleEval (𝓞 K) K v (AdelicLevel.adeleFin (𝓞 K) K
      (Matrix.det (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v g) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))))
      = Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  rw [coe_finEmbed, coe_localEmbed, RingHom.map_det, mapMatrix_fin_finMat, RingHom.map_det,
    mapMatrix_localMat_self]

private theorem finAdeleEval_adeleFin_det_finEmbed_localEmbed_of_ne (g : GL (Fin 2) (v.adicCompletion K))
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    AdelicLevel.finAdeleEval (𝓞 K) K w (AdelicLevel.adeleFin (𝓞 K) K
      (Matrix.det (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v g) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))))
      = 1 := by
  rw [coe_finEmbed, coe_localEmbed, RingHom.map_det, mapMatrix_fin_finMat, RingHom.map_det,
    mapMatrix_localMat_of_ne (𝓞 K) K v _ hw, Matrix.det_one]

private theorem centralScalar_det_finEmbed_localEmbed (g : GL (Fin 2) (v.adicCompletion K)) :
    AutomorphicForm.centralScalar (𝓞 K) K
        (Matrix.GeneralLinearGroup.det (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v g)))
      = finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det g))) := by
  symm
  refine finEmbed_localEmbed_eq_of_components _ _ ?_ ?_ ?_
  · ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
    change AdelicLevel.adeleArch (𝓞 K) K (Matrix.scalar (Fin 2) (Matrix.det
      (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v g) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) i j) = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact adeleArch_det_finEmbed_localEmbed g
    · exact map_zero _
  · ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    change AdelicLevel.finAdeleEval (𝓞 K) K v (AdelicLevel.adeleFin (𝓞 K) K (Matrix.scalar (Fin 2)
      (Matrix.det (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v g) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)))
        i j)) = Matrix.scalar (Fin 2) (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) i j
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs
    · exact finAdeleEval_adeleFin_det_finEmbed_localEmbed_self g
    · rw [map_zero, map_zero]
  · intro w hw
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
    change AdelicLevel.finAdeleEval (𝓞 K) K w (AdelicLevel.adeleFin (𝓞 K) K (Matrix.scalar (Fin 2)
      (Matrix.det (finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v g) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)))
        i j)) = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact finAdeleEval_adeleFin_det_finEmbed_localEmbed_of_ne g hw
    · rw [map_zero, map_zero]

private theorem coe_scalar_det_diagPi (ϖ : v.adicCompletionIntegers K)
    (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det (LocalGL2.diagPi ϖ hϖ0)) :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
      = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ •
          (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  change Matrix.scalar (Fin 2) (Matrix.det !![algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ, 0;
    0, 1]) = _
  rw [Matrix.det_fin_two_of, mul_one, zero_mul, sub_zero, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

private theorem exists_mem_integralSubgroup_finEmbed_localEmbed_eq {ϖ : v.adicCompletionIntegers K}
    (hϖ : Irreducible ϖ) (hϖ0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    {gv : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hgen : finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v (LocalGL2.diagPi ϖ hϖ0)) = gv)
    {ϖ' : v.adicCompletionIntegers K} (hϖ' : Irreducible ϖ') {z : GL (Fin 2) (v.adicCompletion K)}
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
      = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ' •
          (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) :
    ∃ u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
      finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v z)
        = AutomorphicForm.centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det gv) *
            finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v u) := by
  obtain ⟨u, hu, hzu⟩ := CosetIndependence.exists_mem_integralSubgroup_scalar_eq_mul hϖ hϖ'
    (coe_scalar_det_diagPi ϖ hϖ0) hz
  refine ⟨u, hu, ?_⟩
  rw [hzu, map_mul, map_mul, ← hgen, centralScalar_det_finEmbed_localEmbed]

end GenBridge
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.CosetIndependence"

namespace HeckeWordCut

private noncomputable def wordFamily {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
    {n : ℕ} (rT : Fin n → GL (Fin 2) (v.adicCompletion K)) (z : GL (Fin 2) (v.adicCompletion K))
    (k j : ℕ) :
    Fin (Fintype.card (Fin (Fintype.card (Fin k → Fin n)) × Fin (Fintype.card (Fin j → Fin 1)))) →
      GL (Fin 2) (v.adicCompletion K) :=
  HeckeShift.mulReps (HeckeShift.powReps rT k) (HeckeShift.powReps (fun _ : Fin 1 => z) j)

private theorem cosetShift_wordFamily_indicator (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (rT : Fin n → GL (Fin 2) (v.adicCompletion K))
    (z : GL (Fin 2) (v.adicCompletion K)) (k j : ℕ) :
    HeckeShift.cosetShift (wordFamily rT z k j) ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) =
      fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n,
          (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun m => rT (ι m)).prod * z ^ j)⁻¹ * x) :=
  HeckeShift.cosetShift_mulReps_powReps_eq (fun g => g) _ rT z k j

private theorem _root_.HeckeWordCut.sum_apply_mul_embAt_eq (K : Type) [Field K] [NumberField K]
    (W : Set (AdelicGL2 (𝓞 K) K)) (N' : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hvS : v ∉ SK) (hvN : ¬ v.asIdeal ∣ N')
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    {n : ℕ} (rT : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rT)
    (π : HeckeEigensystem K ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsIsotypicCuspFormAt K
      (productionPinsOf K W (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      ξK N' SK π φ) (y : AdelicGL2 (𝓞 K) K) :
    ∑ i, φ (y * HeckeShift.embAt K v (rT i)) = π.a v * φ y := by
  obtain ⟨ϖ₀, h₀, hval, hgen, -⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen K v
  obtain ⟨hirr, hcomp, hrest⟩ := HeckeShift.genData K v ϖ₀ h₀ hval hgen
  have hN0 : N' ≠ ⊥ := by
    rintro rfl
    exact hvN (by rw [← Ideal.zero_eq_bot]; exact dvd_zero _)
  have hUw := HeckeShift.localLevelOne_eq_integralSubgroup_of_not_dvd K v hN0 hvN
  obtain ⟨-, -, h3, h4⟩ := HeckeShift.localLevelOne_data_of_not_dvd K v hN0 hvN
  have hUv₁ : ∀ x ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
      HeckeShift.embAt K v x ∈ principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K :=
    fun x hx => h3 x (hUw ▸ hx)
  have hUv₂ : ∀ u ∈ principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K,
      HeckeShift.compAt K v u ∈
        LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :=
    fun u hu => hUw ▸ h4 u hu
  have hrT' : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (HeckeShift.compAt K v (heckeGen (𝓞 K) K v)) rT := by
    rw [hcomp]
    exact CosetIndependence.isHeckeCosetSystem_diagPi_of_irreducible hirr hϖK h₀ hϖK0 hrT
  exact HeckeCore.sum_apply_mul_embAt_eq_of_isHeckeCosetSystem K v
    (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) _ (fun u hu => h3 _ (h4 u hu)) hUv₁ hUv₂
    hrest hφ.level_invariant (hφ.hecke_eigen v hvS) hrT' y

p2m_export "HeckeWordCut" "sum_apply_mul_embAt_eq"

private theorem _root_.HeckeWordCut.apply_mul_embAt_central_eq (K : Type) [Field K] [NumberField K]
    (W : Set (AdelicGL2 (𝓞 K) K)) (N' : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hvS : v ∉ SK) (hvN : ¬ v.asIdeal ∣ N')
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (π : HeckeEigensystem K ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsIsotypicCuspFormAt K
      (productionPinsOf K W (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      ξK N' SK π φ) (y : AdelicGL2 (𝓞 K) K) :
    φ (y * HeckeShift.embAt K v z) = π.toRawCentral.b v * φ y := by
  obtain ⟨ϖ₀, h₀, hval, hgen, -⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen K v
  obtain ⟨hirr, -, -⟩ := HeckeShift.genData K v ϖ₀ h₀ hval hgen
  have hN0 : N' ≠ ⊥ := by
    rintro rfl
    exact hvN (by rw [← Ideal.zero_eq_bot]; exact dvd_zero _)
  have hUw := HeckeShift.localLevelOne_eq_integralSubgroup_of_not_dvd K v hN0 hvN
  obtain ⟨-, -, h3, -⟩ := HeckeShift.localLevelOne_data_of_not_dvd K v hN0 hvN
  have hUv₁ : ∀ x ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
      HeckeShift.embAt K v x ∈ principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K :=
    fun x hx => h3 x (hUw ▸ hx)
  have hbr := GenBridge.exists_mem_integralSubgroup_finEmbed_localEmbed_eq hirr h₀ hgen hϖK hz
  exact HeckeCore.apply_mul_embAt_eq_of_central K v
    (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) _ hUv₁ hφ.level_invariant
    (HeckeCore.centralScalar_mul_comm K _) (hφ.central_eigen v hvS) hbr y

p2m_export "HeckeWordCut" "apply_mul_embAt_central_eq"

private theorem compAt_mem_localIntegralSet_of_ne_zero (K : Type) [Field K] [NumberField K]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (S' : Finset (HeightOneSpectrum (𝓞 K)))
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ u : HeightOneSpectrum (𝓞 K), GL (Fin 2) (u.adicCompletion K) → ℂ)
    (hfact : IsUnitFactorization K S' f fa ff fS)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S') (x : AdelicGL2 (𝓞 K) K) (hx : f x ≠ 0) :
    HeckeShift.compAt K v x ∈ localIntegralSet K v := by
  obtain ⟨-, -, -, -, hzero, hfac⟩ := hfact
  change AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K x) ∈ localIntegralSet K v
  by_contra hnot
  apply hx
  rw [hfac x, hzero _ ⟨v, hv, hnot⟩, mul_zero]

private theorem apply_mul_embAt_of_mem_localIntegralSet (K : Type) [Field K] [NumberField K]
    (W : Set (AdelicGL2 (𝓞 K) K)) (N' : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K)) (hvN : ¬ v.asIdeal ∣ N')
    (π : HeckeEigensystem K ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsIsotypicCuspFormAt K
      (productionPinsOf K W (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      ξK N' SK π φ)
    (x : AdelicGL2 (𝓞 K) K) (u : GL (Fin 2) (v.adicCompletion K)) (hu : u ∈ localIntegralSet K v) :
    φ (x * HeckeShift.embAt K v u) = φ x := by
  have hN0 : N' ≠ ⊥ := by
    rintro rfl
    exact hvN (by rw [← Ideal.zero_eq_bot]; exact dvd_zero _)
  have hUw := HeckeShift.localLevelOne_eq_integralSubgroup_of_not_dvd K v hN0 hvN
  obtain ⟨-, -, h3, -⟩ := HeckeShift.localLevelOne_data_of_not_dvd K v hN0 hvN
  have hu' : u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) := by
    rw [← SetLike.mem_coe, HeckeShift.coe_integralSubgroup_eq_localIntegralSet]
    exact hu
  exact hφ.level_invariant x _ (h3 u (hUw ▸ hu'))

private theorem sum_apply_mul_embAt_wordFamily (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (φ : AdelicGL2 (𝓞 K) K → ℂ) {n : ℕ}
    (rT : Fin n → GL (Fin 2) (v.adicCompletion K)) (z : GL (Fin 2) (v.adicCompletion K)) (a b : ℂ)
    (hT : ∀ y, ∑ i, φ (y * HeckeShift.embAt K v (rT i)) = a * φ y)
    (hZ : ∀ y, φ (y * HeckeShift.embAt K v z) = b * φ y) (k j : ℕ) (y : AdelicGL2 (𝓞 K) K) :
    ∑ i, φ (y * HeckeShift.embAt K v (wordFamily rT z k j i)) = a ^ k * b ^ j * φ y := by
  have hone : HeckeShift.embAt K v 1 = 1 :=
    mul_left_cancel (a := HeckeShift.embAt K v 1) (by rw [← HeckeShift.embAt_mul, mul_one, mul_one])
  have h1 : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ∑ i, φ (y * HeckeShift.embAt K v (x * rT i)) = a * φ (y * HeckeShift.embAt K v x) := by
    intro x
    simp only [HeckeShift.embAt_mul, ← mul_assoc]
    exact hT _
  have h2 : ∀ x : GL (Fin 2) (v.adicCompletion K),
      ∑ i, φ (y * HeckeShift.embAt K v (x * (fun _ : Fin 1 => z) i)) =
        b * φ (y * HeckeShift.embAt K v x) := by
    intro x
    simp only [Fin.sum_univ_one, HeckeShift.embAt_mul, ← mul_assoc]
    exact hZ _
  have h := HeckeShift.sum_mulReps_eq (fun g => φ (y * HeckeShift.embAt K v g))
    (HeckeShift.powReps rT k) (HeckeShift.powReps (fun _ : Fin 1 => z) j) (a ^ k) (b ^ j)
    (HeckeShift.sum_powReps_eq (fun g => φ (y * HeckeShift.embAt K v g)) rT a h1 k)
    (HeckeShift.sum_powReps_eq (fun g => φ (y * HeckeShift.embAt K v g)) (fun _ : Fin 1 => z) b h2 j) 1
  simp only [one_mul, hone, mul_one] at h
  exact h

private theorem convOp_heckeShift_wordFamily
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (W : Set (AdelicGL2 (𝓞 K) K)) (N' : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S' : Finset (HeightOneSpectrum (𝓞 K)))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ u : HeightOneSpectrum (𝓞 K), GL (Fin 2) (u.adicCompletion K) → ℂ)
    (hfact : IsUnitFactorization K S' f fa ff fS)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S') (hvS : v ∉ SK) (hvN : ¬ v.asIdeal ∣ N')
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    {n : ℕ} (rT : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rT)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)
    (π : HeckeEigensystem K ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsIsotypicCuspFormAt K
      (productionPinsOf K W (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      ξK N' SK π φ) :
    convOp K (HeckeShift.heckeShift K (fun i => HeckeShift.embAt K v (wordFamily rT z k j i)) f) φ =
      (π.a v ^ k * π.toRawCentral.b v ^ j) • convOp K f φ := by
  have hword : ∀ y, ∑ i, φ (y * HeckeShift.embAt K v (wordFamily rT z k j i)) =
      π.a v ^ k * π.toRawCentral.b v ^ j * φ y := fun y =>
    sum_apply_mul_embAt_wordFamily K v φ rT z _ _
      (sum_apply_mul_embAt_eq K W N' SK ξK v hvS hvN ϖK hϖK hϖK0 rT hrT π φ hφ)
      (apply_mul_embAt_central_eq K W N' SK ξK v hvS hvN ϖK hϖK z hz π φ hφ) k j y
  rw [convOp_apply, convOp_apply]
  exact HeckeShift.rightConv_heckeShift K v φ hφ.continuous f hf hfc _ _ hword (fun i => ⟨_, rfl⟩)
    (localIntegralSet K v) (compAt_mem_localIntegralSet_of_ne_zero K S' f fa ff fS hfact v hv)
    (apply_mul_embAt_of_mem_localIntegralSet K W N' SK ξK v hvN π φ hφ)

private theorem isBiInvariantUnder_heckeShift_wordFamily (K : Type) [Field K] [NumberField K]
    (N' : Ideal (𝓞 K)) (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hbi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) f)
    (v : HeightOneSpectrum (𝓞 K)) (hvN : ¬ v.asIdeal ∣ N')
    (ϖK : v.adicCompletionIntegers K)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    {n : ℕ} (rT : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rT)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ) :
    IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K)
      (HeckeShift.heckeShift K (fun i => HeckeShift.embAt K v (wordFamily rT z k j i)) f) := by
  have hN0 : N' ≠ ⊥ := by
    rintro rfl
    exact hvN (by rw [← Ideal.zero_eq_bot]; exact dvd_zero _)
  have hzc : ∀ x : GL (Fin 2) (v.adicCompletion K), z * x = x * z := by
    intro x
    apply Units.ext
    simp only [Units.val_mul, hz, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  have hr := HeckeShift.isLeftStable_mulReps
    (HeckeShift.isLeftStable_powReps (HeckeShift.isLeftStable_of_isHeckeCosetSystem hrT) k)
    (HeckeShift.isLeftStable_powReps (HeckeShift.isLeftStable_central _ hzc) j)
  have hUw := HeckeShift.localLevelOne_eq_integralSubgroup_of_not_dvd K v hN0 hvN
  obtain ⟨-, -, h3, h4⟩ := HeckeShift.localLevelOne_data_of_not_dvd K v hN0 hvN
  refine HeckeShift.heckeShift_isBiInvariantUnder K _ hbi _ fun u hu x => ?_
  refine HeckeShift.heckeShift_apply_mul_eq_of_isLeftStable K v _
    (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) ?_ ?_ hbi hr hu x
  · intro y hy
    exact h3 y (hUw ▸ hy)
  · intro u' hu'
    exact hUw ▸ h4 u' hu'

private theorem cutTrace_heckeShift_wordFamily
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (W : Set (AdelicGL2 (𝓞 K) K)) (tysK : ArchTypeFamily K)
    (N' : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (S' : Finset (HeightOneSpectrum (𝓞 K)))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ u : HeightOneSpectrum (𝓞 K), GL (Fin 2) (u.adicCompletion K) → ℂ)
    (hfact : IsUnitFactorization K S' f fa ff fS)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S') (hvS : v ∉ SK) (hvN : ¬ v.asIdeal ∣ N')
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    {n : ℕ} (rT : Fin n → GL (Fin 2) (v.adicCompletion K))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rT)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)
    (π : HeckeEigensystem K ℂ) :
    cutTrace K
        (productionPinsOf K W (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        ξK N' SK π tysK (HeckeShift.heckeShift K (fun i => HeckeShift.embAt K v (wordFamily rT z k j i)) f)
        (HeckeShift.heckeShift_continuous K _ hf) (HeckeShift.heckeShift_hasCompactSupport K _ hfc) =
      π.a v ^ k * π.toRawCentral.b v ^ j *
        cutTrace K
          (productionPinsOf K W (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          ξK N' SK π tysK f hf hfc := by
  have h := GuardScaling.cutTrace_eq_mul_cutTrace K
    (productionPinsOf K W (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
    ξK N' SK π tysK hf hfc
    (HeckeShift.heckeShift_continuous K (fun i => HeckeShift.embAt K v (wordFamily rT z k j i)) hf)
    (HeckeShift.heckeShift_hasCompactSupport K (fun i => HeckeShift.embAt K v (wordFamily rT z k j i)) hfc)
    (π.a v ^ k * π.toRawCentral.b v ^ j)
    fun φ hφ => convOp_heckeShift_wordFamily K W N' SK ξK S' f hf hfc fa ff fS hfact v hv hvS hvN ϖK hϖK
      hϖK0 rT hrT z hz k j π φ hφ
  exact h

end HeckeWordCut
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.CosetIndependence"

namespace InducedHecke

open HeckeShift MeasureTheory

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private noncomputable def iotaAt : (v.adicCompletion K)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (Units.map (AdelicLevel.finIncl (𝓞 K) K)).comp (AdelicLevel.localUnit (𝓞 K) K v)

private theorem embAt_mem_adelicBorel (m : GL (Fin 2) (v.adicCompletion K))
    (hm : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0) :
    embAt K v m ∈ adelicBorel (𝓞 K) K := by
  show ((embAt K v m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0
  have e : ((embAt K v m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 =
      (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0,
        AdelicDock.localMat (𝓞 K) K v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0) :
          AdeleRing (𝓞 K) K) := rfl
  rw [e]
  refine Prod.ext ?_ ?_
  · show (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0
    exact Matrix.one_apply_ne (by decide)
  · show AdelicDock.localMat (𝓞 K) K v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0
    refine Subtype.ext (funext fun w => ?_)
    show (AdelicDock.localMat (𝓞 K) K v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0) w =
      (0 : FiniteAdeleRing (𝓞 K) K) w
    by_cases hw : w = v
    · subst hw
      rw [AdelicDock.localMat_apply_self, hm]
      rfl
    · rw [AdelicDock.localMat_apply_of_ne (𝓞 K) K v _ _ _ hw, Matrix.one_apply_ne (by decide)]
      rfl

private theorem upper_diag_ne_zero (m : GL (Fin 2) (v.adicCompletion K))
    (hm : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0) :
    (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 ≠ 0 ∧
      (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 ≠ 0 := by
  have hdet : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det m).ne_zero
  rw [Matrix.det_fin_two, hm, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

private theorem borelDiag_embAt (m : GL (Fin 2) (v.adicCompletion K))
    (hm : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0) :
    borelDiagFst (⟨embAt K v m, embAt_mem_adelicBorel K v m hm⟩ : ↥(adelicBorel (𝓞 K) K)) =
        iotaAt K v (Units.mk0 _ (upper_diag_ne_zero K v m hm).1) ∧
      borelDiagSnd (⟨embAt K v m, embAt_mem_adelicBorel K v m hm⟩ : ↥(adelicBorel (𝓞 K) K)) =
        iotaAt K v (Units.mk0 _ (upper_diag_ne_zero K v m hm).2) := by
  have key : ∀ (i : Fin 2) (t : v.adicCompletion K) (ht : t ≠ 0),
      (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i i = t →
      (((embAt K v m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i) =
        ((iotaAt K v (Units.mk0 t ht) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) := by
    intro i t ht hmt
    have e : ((embAt K v m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i i =
        (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i i,
          AdelicDock.localMat (𝓞 K) K v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i i) :
            AdeleRing (𝓞 K) K) := rfl
    rw [e]
    refine Prod.ext ?_ ?_
    · show (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i i = 1
      exact Matrix.one_apply_eq i
    · show AdelicDock.localMat (𝓞 K) K v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i i =
        ((AdelicLevel.localUnit (𝓞 K) K v (Units.mk0 t ht) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
          FiniteAdeleRing (𝓞 K) K)
      refine Subtype.ext (funext fun w => ?_)
      show (AdelicDock.localMat (𝓞 K) K v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i i) w =
        ((AdelicLevel.localUnit (𝓞 K) K v (Units.mk0 t ht) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
          FiniteAdeleRing (𝓞 K) K) w
      by_cases hw : w = v
      · subst hw
        rw [AdelicDock.localMat_apply_self, AdelicLevel.localUnit_apply_self]
        exact hmt
      · rw [AdelicDock.localMat_apply_of_ne (𝓞 K) K v _ _ _ hw, Matrix.one_apply_eq,
          AdelicLevel.localUnit_apply_of_ne (𝓞 K) K v _ hw]
  exact ⟨Units.ext (key 0 _ _ rfl), Units.ext (key 1 _ _ rfl)⟩

private theorem apply_embAt_mul_of_upper {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) (m : GL (Fin 2) (v.adicCompletion K))
    (hm : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0) (g : AdelicGL2 (𝓞 K) K) :
    φ (embAt K v m * g) =
      ((χ₁ (iotaAt K v (Units.mk0 _ (upper_diag_ne_zero K v m hm).1)) : ℂˣ) : ℂ) *
        ((χ₂ (iotaAt K v (Units.mk0 _ (upper_diag_ne_zero K v m hm).2)) : ℂˣ) : ℂ) * φ g := by
  have h := hφ (embAt K v m) (embAt_mem_adelicBorel K v m hm) g
  obtain ⟨h1, h2⟩ := borelDiag_embAt K v m hm
  rw [h1, h2] at h
  exact h

private theorem apply_centralScalar_mul {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) (a : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    φ (centralScalar (𝓞 K) K a * g) = ((χ₁ a : ℂˣ) : ℂ) * ((χ₂ a : ℂˣ) : ℂ) * φ g := by
  have hmem : centralScalar (𝓞 K) K a ∈ adelicBorel (𝓞 K) K := by
    show ((centralScalar (𝓞 K) K a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0
    show (Matrix.scalar (Fin 2) (a : AdeleRing (𝓞 K) K)) 1 0 = 0
    simp
  have h := hφ (centralScalar (𝓞 K) K a) hmem g
  have h1 : borelDiagFst (⟨centralScalar (𝓞 K) K a, hmem⟩ : ↥(adelicBorel (𝓞 K) K)) = a := by
    apply Units.ext
    show (Matrix.scalar (Fin 2) (a : AdeleRing (𝓞 K) K)) 0 0 = a
    simp
  have h2 : borelDiagSnd (⟨centralScalar (𝓞 K) K a, hmem⟩ : ↥(adelicBorel (𝓞 K) K)) = a := by
    apply Units.ext
    show (Matrix.scalar (Fin 2) (a : AdeleRing (𝓞 K) K)) 1 1 = a
    simp
  rw [h1, h2] at h
  exact h

private theorem det_embAt (m : GL (Fin 2) (v.adicCompletion K)) :
    Matrix.GeneralLinearGroup.det (embAt K v m) = iotaAt K v (Matrix.GeneralLinearGroup.det m) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  refine Prod.ext ?_ ?_
  · have h1 := congrArg Matrix.det (AdelicDock.mapMatrix_arch_finMat (𝓞 K) K
      (AdelicDock.localMat (𝓞 K) K v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))
    rw [← RingHom.map_det, Matrix.det_one] at h1
    exact h1
  · have step1 : ((((embAt K v m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det).2 :
        FiniteAdeleRing (𝓞 K) K) =
        (AdelicDock.localMat (𝓞 K) K v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det := by
      have h := (RingHom.map_det (AdelicLevel.adeleFin (𝓞 K) K)
        (AdelicDock.finMat (𝓞 K) K (AdelicDock.localMat (𝓞 K) K v
          (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))).symm
      rw [AdelicDock.mapMatrix_fin_finMat] at h
      exact h
    refine Subtype.ext (funext fun w => ?_)
    show ((((embAt K v m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det).2 :
        FiniteAdeleRing (𝓞 K) K) w =
      ((AdelicLevel.localUnit (𝓞 K) K v (Matrix.GeneralLinearGroup.det m) : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        FiniteAdeleRing (𝓞 K) K) w
    rw [step1]
    change AdelicLevel.finAdeleEval (𝓞 K) K w
        (AdelicDock.localMat (𝓞 K) K v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det = _
    rw [RingHom.map_det]
    by_cases hw : w = v
    · subst hw
      rw [AdelicDock.mapMatrix_localMat_self, AdelicLevel.localUnit_apply_self,
        Matrix.GeneralLinearGroup.val_det_apply]
    · rw [AdelicDock.mapMatrix_localMat_of_ne (𝓞 K) K v _ hw, Matrix.det_one,
        AdelicLevel.localUnit_apply_of_ne (𝓞 K) K v _ hw]

private theorem isHeckeCosetSystem_mul_left_of_mem {G : Type*} [Group G] {U : Subgroup G} {g : G}
    {ι : Type*} {reps : ι → G} (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) {u : G}
    (hu : u ∈ U) : HeckeIntegralSeam.IsHeckeCosetSystem U g (fun i => u * reps i) where
  mem_doubleCoset i := by
    obtain ⟨a, ha, b, hb, h⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    exact HeckePair.mem_doubleCoset_iff.mpr ⟨u * a, U.mul_mem hu ha, b, hb, by rw [← h]; group⟩
  covers x hx := by
    obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    have hx' : u⁻¹ * (a * g * b) ∈ HeckePair.doubleCoset U g :=
      HeckePair.mem_doubleCoset_iff.mpr ⟨u⁻¹ * a, U.mul_mem (U.inv_mem hu) ha, b, hb, by group⟩
    obtain ⟨i, hi⟩ := hsys.covers _ hx'
    refine ⟨i, QuotientGroup.eq.mpr ?_⟩
    have h1 := QuotientGroup.eq.mp hi
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] using h1
  mk_injective i j hij := by
    apply hsys.mk_injective
    have h1 : (u * reps i)⁻¹ * (u * reps j) ∈ U := QuotientGroup.eq.mp hij
    refine QuotientGroup.eq.mpr ?_
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using h1

private theorem apply_embAt_mul_of_entries {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) (m : GL (Fin 2) (v.adicCompletion K))
    (a d : v.adicCompletion K) (ha : a ≠ 0) (hd : d ≠ 0)
    (h10 : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)
    (h00 : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = a)
    (h11 : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = d) (g : AdelicGL2 (𝓞 K) K) :
    φ (embAt K v m * g) =
      ((χ₁ (iotaAt K v (Units.mk0 a ha)) : ℂˣ) : ℂ) * ((χ₂ (iotaAt K v (Units.mk0 d hd)) : ℂˣ) : ℂ) * φ g := by
  rw [apply_embAt_mul_of_upper K v hφ m h10 g]
  have e1 : Units.mk0 _ (upper_diag_ne_zero K v m h10).1 = Units.mk0 a ha := Units.ext h00
  have e2 : Units.mk0 _ (upper_diag_ne_zero K v m h10).2 = Units.mk0 d hd := Units.ext h11
  rw [e1, e2]

private theorem det_heckeGen_eq_iotaAt (ϖ : v.adicCompletionIntegers K)
    (h0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hgen : AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v (LocalGL2.diagPi ϖ h0)) =
      AdelicLevel.heckeGen (𝓞 K) K v) :
    Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v) =
      iotaAt K v (Units.mk0 (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) h0) := by
  have hgen' : embAt K v (LocalGL2.diagPi ϖ h0) = AdelicLevel.heckeGen (𝓞 K) K v := hgen
  rw [← hgen', det_embAt]
  congr 1
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, LocalGL2.coe_diagPi, Matrix.det_fin_two_of]
  simp

private theorem isHeckeCosetSystem_local' (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (Uv : Subgroup (GL (Fin 2) (v.adicCompletion K))) (hUv₁ : ∀ x ∈ Uv, embAt K v x ∈ U)
    (hUv₂ : ∀ u ∈ U, compAt K v u ∈ Uv) {g₀ : GL (Fin 2) (v.adicCompletion K)} {ι : Type*}
    {r : ι → GL (Fin 2) (v.adicCompletion K)}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U (embAt K v g₀) (fun i => embAt K v (r i))) :
    HeckeIntegralSeam.IsHeckeCosetSystem Uv g₀ r where
  mem_doubleCoset i := by
    obtain ⟨u₁, hu₁, u₂, hu₂, h⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    refine HeckePair.mem_doubleCoset_iff.mpr ⟨compAt K v u₁, hUv₂ u₁ hu₁, compAt K v u₂,
      hUv₂ u₂ hu₂, ?_⟩
    have h' := congrArg (compAt K v) h
    simpa only [compAt_mul, compAt_embAt] using h'
  covers x hx := by
    obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    have hmem : embAt K v (a * g₀ * b) ∈ HeckePair.doubleCoset U (embAt K v g₀) :=
      HeckePair.mem_doubleCoset_iff.mpr ⟨embAt K v a, hUv₁ a ha, embAt K v b, hUv₁ b hb,
        by rw [embAt_mul, embAt_mul]⟩
    obtain ⟨i, hi⟩ := hsys.covers _ hmem
    refine ⟨i, QuotientGroup.eq.mpr ?_⟩
    have h1 := QuotientGroup.eq.mp hi
    have h2 := hUv₂ _ h1
    simpa only [compAt_mul, compAt_inv, compAt_embAt] using h2
  mk_injective i j hij := by
    apply hsys.mk_injective
    have h1 : (r i)⁻¹ * r j ∈ Uv := QuotientGroup.eq.mp hij
    have h2 := hUv₁ _ h1
    rw [embAt_mul, embAt_inv] at h2
    exact QuotientGroup.eq.mpr h2

private theorem sum_apply_mul_embAt_std {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ)
    (hsph : ∀ u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
      ∀ g : AdelicGL2 (𝓞 K) K, φ (g * embAt K v u) = φ g)
    (ϖ : v.adicCompletionIntegers K) (h0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hgen : AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v (LocalGL2.diagPi ϖ h0)) =
      AdelicLevel.heckeGen (𝓞 K) K v)
    (sec : 𝓞 K ⧸ v.asIdeal → 𝓞 K) [Fintype (𝓞 K ⧸ v.asIdeal)]
    (hr₀ : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K)) (LocalGL2.diagPi ϖ h0)
      (fun i : Option (𝓞 K ⧸ v.asIdeal) => i.elim (LocalGL2.localRepInf ϖ h0)
        (fun c => LocalGL2.localRepSome ϖ h0 (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c)))))
    (y : AdelicGL2 (𝓞 K) K) :
    ∑ i : Option (𝓞 K ⧸ v.asIdeal),
        φ (y * embAt K v (i.elim (LocalGL2.localRepInf ϖ h0)
          (fun c => LocalGL2.localRepSome ϖ h0 (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c))))) =
      ((Fintype.card (𝓞 K ⧸ v.asIdeal) : ℂ) *
          ((χ₁ (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) +
        ((χ₂ (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)) * φ y := by
  classical

  obtain ⟨b, k, hk, hb10, hbk⟩ := LocalGL2.iwasawa_decomposition (v.adicCompletionIntegers K)
    (v.adicCompletion K) (compAt K v y)
  have hy : y = embAt K v b * restAt K v y * embAt K v k := by
    have h1 := embAt_compAt_mul_restAt K v y
    rw [hbk, embAt_mul, mul_assoc,
      embAt_mul_comm_of_compAt_eq_one K v k (restAt K v y) (compAt_restAt K v y), ← mul_assoc] at h1
    exact h1.symm
  set B := embAt K v b * restAt K v y with hB
  have hterm : ∀ r : GL (Fin 2) (v.adicCompletion K), y * embAt K v r = B * embAt K v (k * r) := by
    intro r
    rw [hy, embAt_mul, hB]
    simp only [mul_assoc]
  have hΦ : ∀ (x : GL (Fin 2) (v.adicCompletion K)),
      ∀ u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
        φ (B * embAt K v (x * u)) = φ (B * embAt K v x) := by
    intro x u hu
    rw [embAt_mul, ← mul_assoc]
    exact hsph u hu _

  set cb : ℂ := ((χ₁ (iotaAt K v (Units.mk0 _ (upper_diag_ne_zero K v b hb10).1)) : ℂˣ) : ℂ) *
    ((χ₂ (iotaAt K v (Units.mk0 _ (upper_diag_ne_zero K v b hb10).2)) : ℂˣ) : ℂ) with hcb
  have hBr : ∀ (r : GL (Fin 2) (v.adicCompletion K)) (a d : v.adicCompletion K) (ha : a ≠ 0) (hd : d ≠ 0),
      (r : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 →
      (r : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 = a →
      (r : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 = d →
        φ (B * embAt K v r) =
          cb * (((χ₁ (iotaAt K v (Units.mk0 a ha)) : ℂˣ) : ℂ) * ((χ₂ (iotaAt K v (Units.mk0 d hd)) : ℂˣ) : ℂ) *
            φ (restAt K v y)) := by
    intro r a d ha hd h10 h00 h11
    rw [hB, mul_assoc, ← embAt_mul_comm_of_compAt_eq_one K v r (restAt K v y) (compAt_restAt K v y),
      apply_embAt_mul_of_upper K v hφ b hb10, apply_embAt_mul_of_entries K v hφ r a d ha hd h10 h00 h11]
  have hφy : φ y = cb * φ (restAt K v y) := by
    have h := hsph k hk B
    rw [← hy] at h
    rw [h, hB, apply_embAt_mul_of_upper K v hφ b hb10]

  have hdet := det_heckeGen_eq_iotaAt K v ϖ h0 hgen
  have hone : iotaAt K v (Units.mk0 (1 : v.adicCompletion K) one_ne_zero) = 1 := by
    rw [show Units.mk0 (1 : v.adicCompletion K) one_ne_zero = 1 from Units.ext rfl, map_one]

  have hswap : ∑ i : Option (𝓞 K ⧸ v.asIdeal),
      φ (B * embAt K v (k * (i.elim (LocalGL2.localRepInf ϖ h0)
        (fun c => LocalGL2.localRepSome ϖ h0 (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c)))))) =
      ∑ i : Option (𝓞 K ⧸ v.asIdeal),
      φ (B * embAt K v (i.elim (LocalGL2.localRepInf ϖ h0)
        (fun c => LocalGL2.localRepSome ϖ h0 (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c))))) :=
    CosetIndependence.sum_eq_of_isHeckeCosetSystem (isHeckeCosetSystem_mul_left_of_mem hr₀ hk) hr₀
      (Φ := fun t => φ (B * embAt K v t)) hΦ
  calc ∑ i : Option (𝓞 K ⧸ v.asIdeal),
        φ (y * embAt K v (i.elim (LocalGL2.localRepInf ϖ h0)
          (fun c => LocalGL2.localRepSome ϖ h0 (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c)))))
      = ∑ i : Option (𝓞 K ⧸ v.asIdeal),
        φ (B * embAt K v (k * (i.elim (LocalGL2.localRepInf ϖ h0)
          (fun c => LocalGL2.localRepSome ϖ h0 (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c)))))) := by
        simp only [hterm]
    _ = ∑ i : Option (𝓞 K ⧸ v.asIdeal),
        φ (B * embAt K v (i.elim (LocalGL2.localRepInf ϖ h0)
          (fun c => LocalGL2.localRepSome ϖ h0 (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c))))) := hswap
    _ = cb * (((χ₁ (iotaAt K v (Units.mk0 (1 : v.adicCompletion K) one_ne_zero)) : ℂˣ) : ℂ) *
            ((χ₂ (iotaAt K v (Units.mk0 _ h0)) : ℂˣ) : ℂ) * φ (restAt K v y)) +
          ∑ c : 𝓞 K ⧸ v.asIdeal, cb * (((χ₁ (iotaAt K v (Units.mk0 _ h0)) : ℂˣ) : ℂ) *
            ((χ₂ (iotaAt K v (Units.mk0 (1 : v.adicCompletion K) one_ne_zero)) : ℂˣ) : ℂ) * φ (restAt K v y)) := by
        rw [Fintype.sum_option]
        congr 1
        · exact hBr _ _ _ _ _ (by simp [LocalGL2.coe_localRepInf]) (by simp [LocalGL2.coe_localRepInf])
            (by simp [LocalGL2.coe_localRepInf])
        · refine Finset.sum_congr rfl fun c _ => ?_
          exact hBr _ _ _ _ _ (by simp [LocalGL2.coe_localRepSome]) (by simp [LocalGL2.coe_localRepSome])
            (by simp [LocalGL2.coe_localRepSome])
    _ = ((Fintype.card (𝓞 K ⧸ v.asIdeal) : ℂ) *
          ((χ₁ (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) +
        ((χ₂ (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)) * φ y := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hone, map_one, map_one, Units.val_one, hdet, hφy]
        ring

private theorem sum_apply_mul_embAt_eq {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ)
    (hsph : ∀ u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
      ∀ g : AdelicGL2 (𝓞 K) K, φ (g * embAt K v u) = φ g)
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    {n : ℕ} {rT : Fin n → GL (Fin 2) (v.adicCompletion K)}
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rT) (y : AdelicGL2 (𝓞 K) K) :
    ∑ i, φ (y * embAt K v (rT i)) =
      (HeckeEigensystem.cNorm v *
          ((χ₁ (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) +
        ((χ₂ (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)) * φ y := by
  classical
  obtain ⟨ϖ₀, h₀, hval, hgen, sec, -, hsys⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen K v
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  obtain ⟨hirr₀, -, -⟩ := HeckeShift.genData K v ϖ₀ h₀ hval hgen

  have htop : ¬ v.asIdeal ∣ (⊤ : Ideal (𝓞 K)) := fun h =>
    v.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp h))
  have hN : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
  have hUw := HeckeShift.localLevelOne_eq_integralSubgroup_of_not_dvd K v hN htop
  have hUv₁ : ∀ x ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
      embAt K v x ∈ AdelicLevel.levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K :=
    fun x hx => HeckeShift.embAt_mem_levelOne_inf K v (hUw ▸ hx)
  have hUv₂ : ∀ u ∈ AdelicLevel.levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K,
      compAt K v u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K) :=
    fun u hu => hUw ▸ HeckeShift.compAt_mem_localLevelOne_of_mem_inf K v hu
  have hgen' : embAt K v (LocalGL2.diagPi ϖ₀ h₀) = AdelicLevel.heckeGen (𝓞 K) K v := hgen
  have hsys' : HeckeIntegralSeam.IsHeckeCosetSystem
      (AdelicLevel.levelOne (𝓞 K) K ⊤ ⊓ finiteAdelicGL2Subgroup K) (embAt K v (LocalGL2.diagPi ϖ₀ h₀))
      (fun i : Option (𝓞 K ⧸ v.asIdeal) => embAt K v (i.elim (LocalGL2.localRepInf ϖ₀ h₀)
        (fun c => LocalGL2.localRepSome ϖ₀ h₀ (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c))))) := by
    rw [hgen']
    have e : (fun i : Option (𝓞 K ⧸ v.asIdeal) => embAt K v (i.elim (LocalGL2.localRepInf ϖ₀ h₀)
        (fun c => LocalGL2.localRepSome ϖ₀ h₀ (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c))))) =
        (fun i : Option (𝓞 K ⧸ v.asIdeal) => AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v
          (i.elim (LocalGL2.localRepInf ϖ₀ h₀)
            (fun c => LocalGL2.localRepSome ϖ₀ h₀ (algebraMap (𝓞 K) (v.adicCompletionIntegers K) (sec c)))))) := by
      funext i; cases i <;> rfl
    rw [e]
    exact hsys ⊤ htop
  have hr₀ := isHeckeCosetSystem_local' K v _ _ hUv₁ hUv₂ hsys'

  have hrT₀ := CosetIndependence.isHeckeCosetSystem_diagPi_of_irreducible hirr₀ hϖK h₀ hϖK0 hrT
  have hinv : ∀ (x : GL (Fin 2) (v.adicCompletion K)),
      ∀ u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
        φ (y * embAt K v (x * u)) = φ (y * embAt K v x) := by
    intro x u hu
    rw [embAt_mul, ← mul_assoc]
    exact hsph u hu _
  rw [CosetIndependence.sum_eq_of_isHeckeCosetSystem hrT₀ hr₀ (Φ := fun t => φ (y * embAt K v t)) hinv,
    sum_apply_mul_embAt_std K v hφ hsph ϖ₀ h₀ hgen sec hr₀ y]
  have hcard : (Fintype.card (𝓞 K ⧸ v.asIdeal) : ℂ) = HeckeEigensystem.cNorm v := by
    show (Fintype.card (𝓞 K ⧸ v.asIdeal) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  rw [hcard]

private theorem apply_mul_embAt_central_eq {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ)
    (hsph : ∀ u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
      ∀ g : AdelicGL2 (𝓞 K) K, φ (g * embAt K v u) = φ g)
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (z : GL (Fin 2) (v.adicCompletion K))
    (hz : (z : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) (y : AdelicGL2 (𝓞 K) K) :
    φ (y * embAt K v z) =
      ((χ₁ (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) *
        ((χ₂ (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) * φ y := by
  obtain ⟨ϖ₀, h₀, hval, hgen, -⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen K v
  obtain ⟨hirr₀, -, -⟩ := HeckeShift.genData K v ϖ₀ h₀ hval hgen
  obtain ⟨u, hu, hzu⟩ := GenBridge.exists_mem_integralSubgroup_finEmbed_localEmbed_eq hirr₀ h₀ hgen hϖK hz
  have hzu' : embAt K v z =
      centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) * embAt K v u := hzu
  rw [hzu', ← mul_assoc, hsph u hu, ← HeckeCore.centralScalar_mul_comm K _ y]
  exact apply_centralScalar_mul K hφ _ y

private theorem distribHaarChar_det_heckeGen :
    ((distribHaarChar (AdeleRing (𝓞 K) K)
        (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : NNReal) : ℝ) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  classical
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
  have hdet : ((Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v) : (AdeleRing (𝓞 K) K)ˣ) :
      AdeleRing (𝓞 K) K) =
      AdelicLevel.finIncl (𝓞 K) K ((AdelicLevel.localUnit (𝓞 K) K v (AdelicLevel.uniformizerUnit K v) :
        (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show Matrix.det ((AdelicLevel.diagOne ((Units.map (AdelicLevel.finIncl (𝓞 K) K))
        (AdelicLevel.localUnit (𝓞 K) K v (AdelicLevel.uniformizerUnit K v))) :
          GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = _
    rw [Matrix.det_fin_two, AdelicLevel.diagOne_coe_apply, AdelicLevel.diagOne_coe_apply,
      AdelicLevel.diagOne_coe_apply, AdelicLevel.diagOne_coe_apply, Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
      Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one, mul_zero, sub_zero,
      Units.coe_map]
  rw [hdet]
  have h1 : ∀ w : InfinitePlace K,
      ‖(AdelicLevel.finIncl (𝓞 K) K ((AdelicLevel.localUnit (𝓞 K) K v (AdelicLevel.uniformizerUnit K v) :
        (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K)).1 w‖ ^ w.mult = 1 := by
    intro w
    rw [AdelicLevel.finIncl_apply_fst]
    show ‖(1 : w.Completion)‖ ^ w.mult = 1
    rw [norm_one, one_pow]
  rw [Finset.prod_eq_one (fun w _ => h1 w), one_mul, AdelicLevel.finIncl_apply_snd]
  rw [finprod_eq_single _ v (fun w hw => by
    rw [AdelicLevel.localUnit_apply_of_ne (𝓞 K) K v _ hw, norm_one])]
  rw [AdelicLevel.localUnit_apply_self, NumberField.FinitePlace.norm_def, AdelicLevel.valued_uniformizerUnit,
    WithZero.exp, WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, zpow_neg_one]
  norm_cast

private theorem scalars_eq (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ)
    (hαdef : α = ((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) :
    (HeckeEigensystem.cNorm v *
          ((etaFst μ α hα s (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) +
        ((etaSnd ν α hα s (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)) =
      (HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
        (((μ (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) *
            (HeckeEigensystem.cNorm v) ^ (-s) +
          ((ν (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) *
            (HeckeEigensystem.cNorm v) ^ s) ∧
    ((etaFst μ α hα s (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) *
        ((etaSnd ν α hα s (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) =
      (HeckeEigensystem.cNorm v)⁻¹ *
        ((HeckeEigensystem.cNorm v) *
          ((μ (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) *
          ((ν (Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)) := by
  set A := Matrix.GeneralLinearGroup.det (AdelicLevel.heckeGen (𝓞 K) K v) with hA
  set q : ℂ := HeckeEigensystem.cNorm v with hq
  have hq' : q = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := rfl
  have hq0 : q ≠ 0 := by
    rw [hq']
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)

  have hαA : ((((α A : ℝˣ) : ℝ) : ℂ)) = q⁻¹ := by
    rw [hαdef]
    show (((NNReal.toRealHom : NNReal →+* ℝ) (distribHaarChar (AdeleRing (𝓞 K) K) A) : ℝ) : ℂ) = q⁻¹
    rw [show ((NNReal.toRealHom : NNReal →+* ℝ) (distribHaarChar (AdeleRing (𝓞 K) K) A) : ℝ) =
        ((distribHaarChar (AdeleRing (𝓞 K) K) A : NNReal) : ℝ) from rfl,
      distribHaarChar_det_heckeGen K v, hq']
    push_cast
    rfl
  have harg : q.arg ≠ Real.pi := by
    rw [hq', Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  have hpow : ∀ w : ℂ, (q⁻¹) ^ w = q ^ (-w) := by
    intro w
    rw [Complex.inv_cpow _ _ harg, Complex.cpow_neg]
  have h1 : ((etaFst μ α hα s A : ℂˣ) : ℂ) = ((μ A : ℂˣ) : ℂ) * q ^ (-(s + 1 / 2)) := by
    rw [etaFst_apply, Units.val_mul, cpowChar_apply_val, hαA, hpow]
  have h2 : ((etaSnd ν α hα s A : ℂˣ) : ℂ) = ((ν A : ℂˣ) : ℂ) * q ^ (s + 1 / 2) := by
    rw [etaSnd_apply, Units.val_mul, cpowChar_apply_val, hαA, hpow, neg_neg]
  have hhalf : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [h1, h2, hhalf]
    have e1 : q * (((μ A : ℂˣ) : ℂ) * q ^ (-(s + 1 / 2))) = q ^ (1 / 2 : ℂ) * (((μ A : ℂˣ) : ℂ) * q ^ (-s)) := by
      have : q * q ^ (-(s + 1 / 2)) = q ^ (1 / 2 : ℂ) * q ^ (-s) := by
        rw [show q * q ^ (-(s + 1 / 2)) = q ^ (1 : ℂ) * q ^ (-(s + 1 / 2)) by rw [Complex.cpow_one],
          ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
        congr 1
        ring
      calc q * (((μ A : ℂˣ) : ℂ) * q ^ (-(s + 1 / 2))) = ((μ A : ℂˣ) : ℂ) * (q * q ^ (-(s + 1 / 2))) := by ring
        _ = ((μ A : ℂˣ) : ℂ) * (q ^ (1 / 2 : ℂ) * q ^ (-s)) := by rw [this]
        _ = _ := by ring
    have e2 : ((ν A : ℂˣ) : ℂ) * q ^ (s + 1 / 2) = q ^ (1 / 2 : ℂ) * (((ν A : ℂˣ) : ℂ) * q ^ s) := by
      rw [Complex.cpow_add _ _ hq0]
      ring
    rw [e1, e2]
    ring
  · rw [h1, h2]
    have e3 : q ^ (-(s + 1 / 2)) * q ^ (s + 1 / 2) = 1 := by
      rw [← Complex.cpow_add _ _ hq0, neg_add_cancel, Complex.cpow_zero]
    calc ((μ A : ℂˣ) : ℂ) * q ^ (-(s + 1 / 2)) * (((ν A : ℂˣ) : ℂ) * q ^ (s + 1 / 2))
        = ((μ A : ℂˣ) : ℂ) * ((ν A : ℂˣ) : ℂ) * (q ^ (-(s + 1 / 2)) * q ^ (s + 1 / 2)) := by ring
      _ = ((μ A : ℂˣ) : ℂ) * ((ν A : ℂˣ) : ℂ) := by rw [e3, mul_one]
      _ = q⁻¹ * (q * ((μ A : ℂˣ) : ℂ) * ((ν A : ℂˣ) : ℂ)) := by field_simp

private theorem eq_of_isUnitFactorization (S : Finset (HeightOneSpectrum (𝓞 K)))
    {f g : AdelicGL2 (𝓞 K) K → ℂ} {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff gf : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    {fS : ∀ w : HeightOneSpectrum (𝓞 K), GL (Fin 2) (w.adicCompletion K) → ℂ}
    (hf : IsUnitFactorization K S f fa ff fS) (hg : IsUnitFactorization K S g fa gf fS) : f = g := by
  obtain ⟨-, -, -, hprod, hzero, hfac⟩ := hf
  obtain ⟨-, -, -, hprod', hzero', hfac'⟩ := hg
  funext x
  rw [hfac x, hfac' x]
  congr 1
  by_cases h : ∀ w ∉ S, AdelicLevel.finComponent (𝓞 K) K w (AdelicLevel.glFin (𝓞 K) K x) ∈ localIntegralSet K w
  · rw [hprod _ h, hprod' _ h]
  · push Not at h
    obtain ⟨w, hw, hnot⟩ := h
    rw [hzero _ ⟨w, hw, hnot⟩, hzero' _ ⟨w, hw, hnot⟩]

private theorem isUnitFactorization_erase [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hvS : v ∈ S)
    {f : AdelicGL2 (𝓞 K) K → ℂ} {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ}
    {fS : ∀ w : HeightOneSpectrum (𝓞 K), GL (Fin 2) (w.adicCompletion K) → ℂ}
    (hf : IsUnitFactorization K S f fa ff fS)
    (hv : fS v = (localIntegralSet K v).indicator fun _ => (1 : ℂ)) :
    IsUnitFactorization K (S.erase v) f fa ff fS := by
  obtain ⟨hfa, hff, hloc, hprod, hzero, hfac⟩ := hf
  refine ⟨hfa, hff, fun w hw => hloc w (Finset.mem_of_mem_erase hw), ?_, ?_, hfac⟩
  · intro h hint
    by_cases hvint : AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v
    · have hall : ∀ w ∉ S, AdelicLevel.finComponent (𝓞 K) K w h ∈ localIntegralSet K w := by
        intro w hw
        exact hint w (fun hw' => hw (Finset.mem_of_mem_erase hw'))
      rw [hprod h hall, ← Finset.mul_prod_erase S _ hvS, hv, Set.indicator_of_mem hvint, one_mul]
    · exact absurd (hint v (Finset.notMem_erase v S)) hvint
  · rintro h ⟨w, hw, hnot⟩
    by_cases hwv : w = v
    · subst hwv
      by_cases hall : ∀ w' ∉ S, AdelicLevel.finComponent (𝓞 K) K w' h ∈ localIntegralSet K w'
      · rw [hprod h hall, ← Finset.mul_prod_erase S _ hvS, hv, Set.indicator_of_notMem hnot, zero_mul]
      · push Not at hall
        obtain ⟨w', hw', hnot'⟩ := hall
        exact hzero h ⟨w', hw', hnot'⟩
    · exact hzero h ⟨w, fun hwS => hw (Finset.mem_erase.mpr ⟨hwv, hwS⟩), hnot⟩

end InducedHecke
p2m_reactivate "P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.HeckeShift P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization.CosetIndependence"

open MeasureTheory NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTd : Disjoint T SK)
    (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hirr : ∀ v ∈ T, Irreducible (ϖKs v))
    (hϖKs0 : ∀ v ∈ T, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
    (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
    (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
    (hcos : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v))
    (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (hzKs : ∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hfact : IsUnitFactorization K (SK ∪ T) f faK ff
      (fun v => if v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι : Fin (ks v) → Fin (nKs v),
          (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
        else fSK v))
    (f₀ : AdelicGL2 (𝓞 K) K → ℂ) (hf₀ : Continuous f₀) (hf₀c : HasCompactSupport f₀)
    (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hfact₀ : IsUnitFactorization K (SK ∪ T) f₀ faK ff₀
      (fun v => if v ∈ T then (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) else fSK v)) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμν : ∀ v ∈ T, NumberField.TateGlobal.IsUnramifiedCharAt μ v ∧ NumberField.TateGlobal.IsUnramifiedCharAt ν v)
      (s : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 K) K
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ)
      (_hφsph : ∀ k ∈ AutomorphicForm.maximalCompactAway K SK, ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g)
      (x : AdelicGL2 (𝓞 K) K),
    AutomorphicForm.rightConv K φ f x =
      (∏ v ∈ T,
        ((HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
            (((μ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) * (HeckeEigensystem.cNorm v) ^ (-s) +
              ((ν (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) * (HeckeEigensystem.cNorm v) ^ s)) ^ ks v *
          ((HeckeEigensystem.cNorm v)⁻¹ *
            ((HeckeEigensystem.cNorm v) * ((μ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) * ((ν (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ))) ^ js v) *
        AutomorphicForm.rightConv K φ f₀ x := by
  intro αm hαm μ ν _hμν s φ hφ hφc hφsph x
  classical
  have hαdef : αm = ((NNReal.toRealHom : NNReal →+* ℝ).toMonoidHom.comp
      (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits := rfl

  set cT : HeightOneSpectrum (𝓞 K) → ℂ := fun v =>
    ((HeckeEigensystem.cNorm v) ^ ((1 / 2 : ℝ) : ℂ) *
        (((μ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) * (HeckeEigensystem.cNorm v) ^ (-s) +
          ((ν (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) * (HeckeEigensystem.cNorm v) ^ s)) ^ ks v *
      ((HeckeEigensystem.cNorm v)⁻¹ *
        ((HeckeEigensystem.cNorm v) * ((μ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) *
          ((ν (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ))) ^ js v with hcT

  have hvSK : ∀ v ∈ T, v ∉ SK := fun v hv => Finset.disjoint_left.mp hTd hv
  have hsphT : ∀ v ∈ T, ∀ u ∈ LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K),
      ∀ g : AdelicGL2 (𝓞 K) K, φ (g * HeckeShift.embAt K v u) = φ g := by
    intro v hv u hu g
    apply hφsph
    have hN : (⊤ : Ideal (𝓞 K)) ≠ ⊥ := top_ne_bot
    have htop : ¬ v.asIdeal ∣ (⊤ : Ideal (𝓞 K)) := fun h =>
      v.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp h))
    have hUw := HeckeShift.localLevelOne_eq_integralSubgroup_of_not_dvd K v hN htop
    have hlev := HeckeShift.embAt_mem_levelOne_inf K v (N := ⊤) (k := u) (hUw ▸ hu)
    have hfin : AdelicLevel.glFin (𝓞 K) K (HeckeShift.embAt K v u) ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K :=
      AdelicLevel.finiteLevelOne_le_finiteLevelZero (𝓞 K) K ⊤
        ((AdelicLevel.mem_levelOne_iff).mp (Subgroup.mem_inf.mp hlev).1)
    have harch : AdelicLevel.glArch (𝓞 K) K (HeckeShift.embAt K v u) = 1 := AdelicDock.glArch_finEmbed (𝓞 K) K _
    rw [mem_maximalCompactAway_iff]
    refine ⟨mem_adelicMaximalCompact_iff.mpr ⟨hfin, fun w => ?_⟩, harch, fun w hw => ?_⟩
    · rw [harch, map_one]
      exact WindowedSiegel.isRowIsometry_one
    · have hwv : w ≠ v := fun h => hvSK v hv (h ▸ hw)
      rw [show AdelicLevel.glFin (𝓞 K) K (HeckeShift.embAt K v u) = AdelicDock.localEmbed (𝓞 K) K v u from
        AdelicDock.glFin_finEmbed (𝓞 K) K _, AdelicDock.finComponent_localEmbed_of_ne (𝓞 K) K v u hwv]

  have heig : ∀ v ∈ T, ∀ y : AdelicGL2 (𝓞 K) K,
      ∑ i, φ (y * HeckeShift.embAt K v (HeckeWordCut.wordFamily (rKs v) (zKs v) (ks v) (js v) i)) = cT v * φ y := by
    intro v hv y
    have hT := fun y' => InducedHecke.sum_apply_mul_embAt_eq K v hφ (hsphT v hv) (ϖKs v) (hirr v hv) (hϖKs0 v hv)
      (hcos v hv) y'
    have hZ := fun y' => InducedHecke.apply_mul_embAt_central_eq K v hφ (hsphT v hv) (ϖKs v) (hirr v hv) (zKs v)
      (hzKs v hv) y'
    rw [HeckeWordCut.sum_apply_mul_embAt_wordFamily K v φ (rKs v) (zKs v) _ _ hT hZ (ks v) (js v) y]
    obtain ⟨e1, e2⟩ := InducedHecke.scalars_eq K v αm hαdef hαm μ ν s
    rw [e1, e2]

  have key : ∀ T' : Finset (HeightOneSpectrum (𝓞 K)), T' ⊆ T →
      ∃ (F : AdelicGL2 (𝓞 K) K → ℂ) (_ : Continuous F) (_ : HasCompactSupport F)
        (ffF : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
        IsUnitFactorization K (SK ∪ T) F faK ffF
          (fun v => if v ∈ T' then fun x : GL (Fin 2) (v.adicCompletion K) =>
              ∑ ι : Fin (ks v) → Fin (nKs v),
                (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
            else if v ∈ T then (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) else fSK v) ∧
        ∀ y, rightConv K φ F y = (∏ v ∈ T', cT v) * rightConv K φ f₀ y := by
    intro T'
    induction T' using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨f₀, hf₀, hf₀c, ff₀, ?_, fun y => by rw [Finset.prod_empty, one_mul]⟩
      have e : (fun v => if v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 K))) then
            fun x : GL (Fin 2) (v.adicCompletion K) =>
              ∑ ι : Fin (ks v) → Fin (nKs v),
                (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                  (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
            else if v ∈ T then (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) else fSK v) =
          (fun v => if v ∈ T then (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) else fSK v) := by
        funext v
        rw [if_neg (Finset.notMem_empty v)]
      rw [e]
      exact hfact₀
    | insert v T' hvT' ih =>
      intro hsub
      have hv : v ∈ T := hsub (Finset.mem_insert_self v T')
      obtain ⟨F, hF, hFc, ffF, hfactF, hconvF⟩ := ih ((Finset.subset_insert v T').trans hsub)
      set fam : ∀ w : HeightOneSpectrum (𝓞 K), GL (Fin 2) (w.adicCompletion K) → ℂ := fun w =>
        if w ∈ T' then fun x : GL (Fin 2) (w.adicCompletion K) =>
            ∑ ι : Fin (ks w) → Fin (nKs w),
              (localIntegralSet K w).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs w (ι m)).prod * zKs w ^ js w)⁻¹ * x)
          else if w ∈ T then (localIntegralSet K w).indicator (fun _ => (1 : ℂ)) else fSK w with hfam
      have hvS : v ∈ SK ∪ T := Finset.mem_union_right SK hv
      have hfamv : fam v = (localIntegralSet K v).indicator fun _ => (1 : ℂ) := by
        rw [hfam]
        simp only [hvT', hv, ↓reduceIte]
      have herase := InducedHecke.isUnitFactorization_erase K v (SK ∪ T) hvS hfactF hfamv
      have hvE : v ∉ (SK ∪ T).erase v := Finset.notMem_erase v _

      set r := HeckeWordCut.wordFamily (rKs v) (zKs v) (ks v) (js v) with hr
      have hshift := HeckeShift.isUnitFactorization_heckeShift (K := K) (v := v) ((SK ∪ T).erase v) hvE herase r
      rw [Finset.insert_erase hvS, HeckeWordCut.cosetShift_wordFamily_indicator] at hshift
      refine ⟨HeckeShift.heckeShift K (fun i => HeckeShift.embAt K v (r i)) F,
        HeckeShift.heckeShift_continuous K _ hF, HeckeShift.heckeShift_hasCompactSupport K _ hFc,
        HeckeShift.cosetShift (fun i => AdelicDock.localEmbed (𝓞 K) K v (r i)) ffF, ?_, ?_⟩
      · have e : Function.update fam v (fun x : GL (Fin 2) (v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (nKs v),
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)) =
            (fun w => if w ∈ insert v T' then fun x : GL (Fin 2) (w.adicCompletion K) =>
                ∑ ι : Fin (ks w) → Fin (nKs w),
                  (localIntegralSet K w).indicator (fun _ => (1 : ℂ))
                    (((List.ofFn fun m => rKs w (ι m)).prod * zKs w ^ js w)⁻¹ * x)
              else if w ∈ T then (localIntegralSet K w).indicator (fun _ => (1 : ℂ)) else fSK w) := by
          funext w
          by_cases hwv : w = v
          · subst hwv
            rw [Function.update_self, if_pos (Finset.mem_insert_self w T')]
          · rw [Function.update_of_ne hwv, hfam]
            simp only [Finset.mem_insert, hwv, false_or]
        rw [← e]
        exact hshift
      · intro y
        have hfU : ∀ z, F z ≠ 0 → HeckeShift.compAt K v z ∈ localIntegralSet K v :=
          fun z hz => HeckeWordCut.compAt_mem_localIntegralSet_of_ne_zero K ((SK ∪ T).erase v) F faK ffF fam
            herase v hvE z hz
        have hφU : ∀ x', ∀ u ∈ localIntegralSet K v, φ (x' * HeckeShift.embAt K v u) = φ x' := by
          intro x' u hu
          refine hsphT v hv u ?_ x'
          rw [← SetLike.mem_coe, HeckeShift.coe_integralSubgroup_eq_localIntegralSet]
          exact hu
        have hRC := HeckeShift.rightConv_heckeShift (K := K) (v := v) φ hφc F hF hFc
          (fun i => HeckeShift.embAt K v (r i)) (cT v) (heig v hv) (fun i => ⟨r i, rfl⟩)
          (localIntegralSet K v) hfU hφU
        rw [hRC, Pi.smul_apply, smul_eq_mul, hconvF y, Finset.prod_insert hvT']
        ring
  obtain ⟨F, hF, hFc, ffF, hfactF, hconvF⟩ := key T (Finset.Subset.refl T)
  have e : (fun v => if v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι : Fin (ks v) → Fin (nKs v),
          (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
      else if v ∈ T then (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) else fSK v) =
      (fun v => if v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι : Fin (ks v) → Fin (nKs v),
          (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
        else fSK v) := by
    funext v
    by_cases hv : v ∈ T
    · rw [if_pos hv, if_pos hv]
    · rw [if_neg hv, if_neg hv, if_neg hv]
  rw [e] at hfactF
  have hfF : f = F := InducedHecke.eq_of_isUnitFactorization K (SK ∪ T) hfact hfactF
  rw [hfF, hconvF x]

end S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization
end P2MW
export P2MW.S_AutomorphicForm_rightConv_eq_prod_pow_mul_pow_mul_rightConv_of_isInducedSection_of_isUnitFactorization (solution)
