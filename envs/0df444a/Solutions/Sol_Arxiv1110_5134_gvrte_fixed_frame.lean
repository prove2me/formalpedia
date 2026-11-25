-- Prove2me | solution 1 for Arxiv1110_5134.gvrte_fixed_frame
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:17:42.951687+00:00
-- url     : https://prove2.me/submissions/3223eb91-465b-42ad-9fd6-119426621901

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic
import Theorems.Thm_Arxiv1110_5134_fixed_frame_rotation

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

theorem solution (n : ℝ → ℝ) (s : ℝ) (hn : 0 < n s) (hnd : DifferentiableAt ℝ n s)
    (σ φG : ℝ → ℝ) (hσ : σ s ≠ 0)
    (hM : ∀ i j, DifferentiableAt ℝ (fun t => modRot (σ t) (-φG t) i j) s)
    (IG : ℝ → Stokes) (hIG : DifferentiableAt ℝ IG s)
    (κe κa : Matrix (Fin 4) (Fin 4) ℝ) (κ : ℝ) (Ib : Stokes)
    (Z : Dir → Matrix (Fin 4) (Fin 4) ℝ) (σ' φG' : Dir → ℝ) (hσ' : ∀ ω, σ' ω ≠ 0)
    (IGin : Dir → Stokes)
    (h20 : transportOp n (fun t => modRot (σ t) (-φG t) *ᵥ IG t) s +
        (κe + rytovMatrix κ) *ᵥ (modRot (σ s) (-φG s) *ᵥ IG s) =
      κa *ᵥ Ib + scatSource Z (fun ω => modRot (σ' ω) (-φG' ω) *ᵥ IGin ω)) :
    transportOp n IG s +
        (modRot (σ s) (φG s) * matDeriv (fun t => modRot (σ t) (-φG t)) s +
          (modRot (σ s) (φG s) * κe * modRot (σ s) (-φG s) +
            modRot (σ s) (φG s) * rytovMatrix κ * modRot (σ s) (-φG s))) *ᵥ IG s =
      (modRot (σ s) (φG s) * κa * modRot (σ s) (-φG s)) *ᵥ (modRot (σ s) (φG s) *ᵥ Ib) +
        scatSource (fun ω => modRot (σ s) (φG s) * Z ω * modRot (σ' ω) (-φG' ω)) IGin := by
  let M : ℝ → Matrix (Fin 4) (Fin 4) ℝ := fun t => modRot (σ t) (-φG t)
  let A : Matrix (Fin 4) (Fin 4) ℝ := modRot (σ s) (φG s)
  let B : Matrix (Fin 4) (Fin 4) ℝ := modRot (σ s) (-φG s)
  obtain ⟨hBA, hAB⟩ := (fixed_frame_rotation (σ s) (φG s)).2.2.2.1 hσ
  change B * A = 1 at hBA
  change A * B = 1 at hAB
  have hn2 : n s ^ 2 ≠ 0 := pow_ne_zero 2 hn.ne'
  let G : ℝ → Stokes := fun t => (n t ^ 2)⁻¹ • IG t
  have hinv_diff : DifferentiableAt ℝ (fun t => (n t ^ 2)⁻¹) s :=
    (hnd.pow 2).inv hn2
  have hG : DifferentiableAt ℝ G s := hinv_diff.smul hIG
  have hGj : ∀ j : Fin 4, HasDerivAt (fun t => G t j) (deriv G s j) s :=
    fun j => hasDerivAt_pi.mp hG.hasDerivAt j
  have hMG : HasDerivAt (fun t => M t *ᵥ G t) (matDeriv M s *ᵥ G s + B *ᵥ deriv G s) s := by
    rw [hasDerivAt_pi]
    intro i
    have hsum := HasDerivAt.sum (u := (Finset.univ : Finset (Fin 4)))
      fun j _ => (hM i j).hasDerivAt.mul (hGj j)
    have hfn : (fun t => (M t *ᵥ G t) i) =
        ∑ j ∈ (Finset.univ : Finset (Fin 4)),
          (fun t => modRot (σ t) (-φG t) i j) * fun t => G t j := by
      ext t
      simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.mul_apply]
    have hval : (matDeriv M s *ᵥ G s + B *ᵥ deriv G s) i =
        ∑ j ∈ (Finset.univ : Finset (Fin 4)),
          (deriv (fun t => modRot (σ t) (-φG t) i j) s * G s j +
            modRot (σ s) (-φG s) i j * deriv G s j) := by
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, matDeriv, B, M]
      rw [Finset.sum_add_distrib]
    rw [hfn, hval]
    exact hsum
  have htr : transportOp n (fun t => M t *ᵥ IG t) s =
      matDeriv M s *ᵥ IG s + B *ᵥ transportOp n IG s := by
    have hfun : (fun t => (n t ^ 2)⁻¹ • (M t *ᵥ IG t)) = (fun t => M t *ᵥ G t) := by
      ext t i
      simp [G, Matrix.mulVec_smul]
    unfold transportOp
    rw [hfun, hMG.deriv, smul_add]
    have h1 : n s ^ 2 • (matDeriv M s *ᵥ G s) = matDeriv M s *ᵥ IG s := by
      ext i
      simp only [G, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hn2, one_mul]
    have h2 : n s ^ 2 • (B *ᵥ deriv G s) = B *ᵥ (n s ^ 2 • deriv G s) := by
      rw [Matrix.mulVec_smul]
    rw [h1, h2]
  have hscat : A *ᵥ scatSource Z (fun ω => modRot (σ' ω) (-φG' ω) *ᵥ IGin ω) =
      scatSource (fun ω => A * Z ω * modRot (σ' ω) (-φG' ω)) IGin := by
    let f : Dir → Stokes := fun ω => Z ω *ᵥ (modRot (σ' ω) (-φG' ω) *ᵥ IGin ω)
    let AL : Stokes →L[ℝ] Stokes := (Matrix.mulVecLin A).toContinuousLinearMap
    let BL : Stokes →L[ℝ] Stokes := (Matrix.mulVecLin B).toContinuousLinearMap
    have hAL : ∀ v, AL v = A *ᵥ v := fun _ => rfl
    have hBL : ∀ v, BL v = B *ᵥ v := fun _ => rfl
    have hint_comm : A *ᵥ (∫ ω, f ω ∂solidAngle) = ∫ ω, A *ᵥ f ω ∂solidAngle := by
      by_cases hint : Integrable f solidAngle
      · exact (AL.integral_comp_comm hint).symm
      · have hnot : ¬ Integrable (fun ω => AL (f ω)) solidAngle := by
          intro hAf
          apply hint
          have hBAf : (fun ω => BL (AL (f ω))) = f := by
            ext ω i
            simp [hAL, hBL, Matrix.mulVec_mulVec, hBA]
          rw [← hBAf]
          exact BL.integrable_comp hAf
        change AL (∫ ω, f ω ∂solidAngle) = ∫ ω, AL (f ω) ∂solidAngle
        rw [integral_undef hint, integral_undef hnot, map_zero]
    unfold scatSource
    rw [Matrix.mulVec_smul, hint_comm]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [f, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hmul := congrArg (fun v => A *ᵥ v) h20
  change A *ᵥ (transportOp n (fun t => M t *ᵥ IG t) s +
      (κe + rytovMatrix κ) *ᵥ (B *ᵥ IG s)) =
    A *ᵥ (κa *ᵥ Ib + scatSource Z (fun ω => modRot (σ' ω) (-φG' ω) *ᵥ IGin ω)) at hmul
  rw [htr, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, hscat] at hmul
  have hLHS :
      A *ᵥ (matDeriv M s *ᵥ IG s) + A *ᵥ (B *ᵥ transportOp n IG s) +
          A *ᵥ ((κe + rytovMatrix κ) *ᵥ (B *ᵥ IG s)) =
      transportOp n IG s +
          (A * matDeriv M s + (A * κe * B + A * rytovMatrix κ * B)) *ᵥ IG s := by
    simp only [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec, Matrix.add_mulVec,
      Matrix.mulVec_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  have hRHS :
      A *ᵥ (κa *ᵥ Ib) = (A * κa * B) *ᵥ (A *ᵥ Ib) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hBA, Matrix.mul_one]
  rw [hLHS, hRHS] at hmul
  exact hmul
