-- Prove2me | solution 1 for AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/46815e02-d770-5df8-95d6-1be280722e22

import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.SmoothCusp IsDedekindDomain UnramifiedWhittaker HeckeIntegralSeam

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace RS11CH

variable {G : Type*} [Group G]

theorem isHeckeCosetSystem_mul_right {U : Subgroup G} {gv : G} {ι : Type*} {reps : ι → G}
    (hsys : IsHeckeCosetSystem U gv reps) {u : G} (hu : u ∈ U) :
    IsHeckeCosetSystem U gv (fun i => reps i * u) where
  mem_doubleCoset i := HeckePair.doubleCoset_mul_mem (hsys.mem_doubleCoset i) hu
  covers x hx := by
    obtain ⟨i, hi⟩ := hsys.covers (x * u⁻¹) (HeckePair.doubleCoset_mul_mem hx (inv_mem hu))
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    have : x⁻¹ * (reps i * u) = u⁻¹ * ((x * u⁻¹)⁻¹ * reps i) * u := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hu) hi) hu
  mk_injective i j hij := by
    apply hsys.mk_injective
    have hij' : (QuotientGroup.mk (reps i * u) : G ⧸ U) = QuotientGroup.mk (reps j * u) := hij
    show (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    rw [QuotientGroup.eq] at hij' ⊢
    have : (reps i)⁻¹ * reps j = u * ((reps i * u)⁻¹ * (reps j * u)) * u⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hu hij') (inv_mem hu)

end RS11CH

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (hUv : ∀ kv : GL (Fin 2) (v.adicCompletionIntegers K),
      placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) ∈ U)
    (reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K)
    (hsys : IsHeckeCosetSystem U (heckeGen (𝓞 K) K v) reps)
    (hpure : ∀ j, ∃ m : GL (Fin 2) (v.adicCompletion K), reps j = placeEmbed K v m)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g)
    (a : ℂ) (hφT : IsHeckeCosetEigenfunctionAt K U (heckeGen (𝓞 K) K v) v φ a)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hsupp : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 → ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K,
      z = z₁ * z₂ ∧ z₂ ∈ U ∧ ∀ xv : GL (Fin 2) (v.adicCompletion K), z₁ * placeEmbed K v xv = placeEmbed K v xv * z₁)
    (hint : ∀ g : AdelicGL2 (𝓞 K) K, Integrable (fun z => φ (g * z) * f z) (adelicGLHaar (Fin 2) (𝓞 K) K))
    {n : ℕ} (h : Fin n → AdelicGL2 (𝓞 K) K) (c : Fin n → ℂ)
    (hh : ∀ i, ∀ xv : GL (Fin 2) (v.adicCompletion K), h i * placeEmbed K v xv = placeEmbed K v xv * h i) :
    let Φ : AdelicGL2 (𝓞 K) K → ℂ := fun g => ∑ i, c i * rightConv K φ f (g * h i)
    (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
      Φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Φ g) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, heckeCosetSum K reps Φ g = a * Φ g) ∧
    IsHeckeCosetEigenfunctionAt K U (heckeGen (𝓞 K) K v) v Φ a := by
  classical
  intro Φ

  obtain ⟨reps', hsys', hT'⟩ := hφT
  have hT : ∀ g : AdelicGL2 (𝓞 K) K, ∑ j, φ (g * reps j) = a * φ g := by
    intro g
    rw [HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys' hsys hφU g]
    exact hT' g

  choose mrep hmrep using hpure

  have hkey : ∀ g z : AdelicGL2 (𝓞 K) K, f z ≠ 0 → ∑ j, φ (g * reps j * z) = a * φ (g * z) := by
    intro g z hz
    obtain ⟨z₁, z₂, rfl, hz₂, hcomm⟩ := hsupp z hz
    have h1 : ∀ j, g * reps j * (z₁ * z₂) = (g * z₁) * (reps j * z₂) := by
      intro j
      rw [hmrep j, show g * placeEmbed K v (mrep j) * (z₁ * z₂) = g * (placeEmbed K v (mrep j) * z₁) * z₂ by group,
        ← hcomm (mrep j)]
      group
    simp only [h1]
    rw [HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys (RS11CH.isHeckeCosetSystem_mul_right hsys hz₂)
      hφU (g * z₁), hT (g * z₁), ← mul_assoc, hφU _ z₂ hz₂]
  have hsph : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g z : AdelicGL2 (𝓞 K) K), f z ≠ 0 →
      φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) * z) = φ (g * z) := by
    intro kv g z hz
    obtain ⟨z₁, z₂, rfl, hz₂, hcomm⟩ := hsupp z hz
    set kk := placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv) with hkk
    calc φ (g * kk * (z₁ * z₂)) = φ (g * (kk * z₁) * z₂) := by congr 1; group
      _ = φ (g * (z₁ * kk) * z₂) := by rw [hkk, hcomm]
      _ = φ ((g * z₁) * (kk * z₂)) := by congr 1; group
      _ = φ (g * z₁) := hφU _ _ (mul_mem (hUv kv) hz₂)
      _ = φ (g * z₁ * z₂) := (hφU _ _ hz₂).symm
      _ = φ (g * (z₁ * z₂)) := by rw [mul_assoc]

  have hconvT : ∀ g : AdelicGL2 (𝓞 K) K, ∑ j, rightConv K φ f (g * reps j) = a * rightConv K φ f g := by
    intro g
    simp only [rightConv_apply]
    rw [← integral_finsetSum _ (fun j _ => hint (g * reps j)), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    by_cases hz : f z = 0
    · simp [hz]
    · rw [← Finset.sum_mul, hkey g z hz, mul_assoc]
  have hconvS : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
      rightConv K φ f (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = rightConv K φ f g := by
    intro kv g
    simp only [rightConv_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    beta_reduce
    by_cases hz : f z = 0
    · simp [hz]
    · rw [hsph kv g z hz]

  have hΦS : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
      Φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = Φ g := by
    intro kv g
    show (∑ i, c i * rightConv K φ f (g * _ * h i)) = ∑ i, c i * rightConv K φ f (g * h i)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← hh i, ← mul_assoc, hconvS]
  have hΦT : ∀ g : AdelicGL2 (𝓞 K) K, heckeCosetSum K reps Φ g = a * Φ g := by
    intro g
    show (∑ j, ∑ i, c i * rightConv K φ f (g * reps j * h i)) = a * ∑ i, c i * rightConv K φ f (g * h i)
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcomm : ∀ j, g * reps j * h i = g * h i * reps j := by
      intro j
      rw [hmrep j, mul_assoc, ← hh i (mrep j), ← mul_assoc]
    simp only [hcomm, ← Finset.mul_sum, hconvT]
    ring
  exact ⟨hΦS, hΦT, ⟨reps, hsys, hΦT⟩⟩

end S_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps
end P2MW
export P2MW.S_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps (solution)
