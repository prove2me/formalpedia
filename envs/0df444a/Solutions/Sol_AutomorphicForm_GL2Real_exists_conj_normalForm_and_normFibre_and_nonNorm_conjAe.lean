-- Prove2me | solution 1 for AutomorphicForm.GL2Real.exists_conj_normalForm_and_normFibre_and_nonNorm_conjAe
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/b350ddd2-252b-54a0-8a2e-32de06bcb95b

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_exists_conj_normalForm_and_normFibre_and_nonNorm_conjAe

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace ConjNormFibre

private def ridEquiv : ℂ ⊗[ℝ] ℝ ≃+* ℂ :=
  @AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _ (Algebra.TensorProduct.rid ℝ ℝ ℂ)

private def ridHom : ℂ ⊗[ℝ] ℝ →+* ℂ :=
  (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
    (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom

private def ridInv : ℂ →+* ℂ ⊗[ℝ] ℝ := ridEquiv.symm.toRingHom

private theorem ridHom_ridInv (z : ℂ) : ridHom (ridInv z) = z := ridEquiv.apply_symm_apply z

private theorem ridInv_ridHom (x : ℂ ⊗[ℝ] ℝ) : ridInv (ridHom x) = x := ridEquiv.symm_apply_apply x

private theorem ridHom_tmul (a : ℂ) (b : ℝ) : ridHom (a ⊗ₜ[ℝ] b) = (b : ℂ) * a := by
  rw [← Complex.real_smul]
  rfl

private theorem ridHom_sigma (x : ℂ ⊗[ℝ] ℝ) :
    ridHom (sigmaTensor ℝ ℂ ℝ Complex.conjAe x) = starRingEnd ℂ (ridHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
      have hσ : sigmaTensor ℝ ℂ ℝ Complex.conjAe (a ⊗ₜ[ℝ] b) = (starRingEnd ℂ a) ⊗ₜ[ℝ] b := rfl
      rw [hσ, ridHom_tmul, ridHom_tmul, map_mul, Complex.conj_ofReal]
  | add x y hx hy => simp only [map_add, hx, hy]

private def glC : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) →* GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map ridHom

private def glR : GL (Fin 2) ℂ →* GL (Fin 2) (ℂ ⊗[ℝ] ℝ) := Matrix.GeneralLinearGroup.map ridInv

private def conjGL : GL (Fin 2) ℂ →* GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.map (starRingEnd ℂ)

private def cj (M : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := M.map (starRingEnd ℂ)

private theorem cj_apply (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : cj M i j = starRingEnd ℂ (M i j) := rfl

private theorem cj_mul (M N : Matrix (Fin 2) (Fin 2) ℂ) : cj (M * N) = cj M * cj N := Matrix.map_mul

private theorem cj_cj (M : Matrix (Fin 2) (Fin 2) ℂ) : cj (cj M) = M := by
  ext i j
  simp [cj]

private theorem conjGL_val (X : GL (Fin 2) ℂ) :
    ((conjGL X : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = cj (X : Matrix (Fin 2) (Fin 2) ℂ) := rfl

private theorem glC_glR (X : GL (Fin 2) ℂ) : glC (glR X) = X :=
  Matrix.GeneralLinearGroup.ext fun i j => ridHom_ridInv ((X : Matrix (Fin 2) (Fin 2) ℂ) i j)

private theorem glR_glC (x : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : glR (glC x) = x :=
  Matrix.GeneralLinearGroup.ext fun i j => ridInv_ridHom ((x : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) i j)

private theorem glC_injective : Function.Injective glC := Function.LeftInverse.injective glR_glC

private theorem glC_sigmaGL (t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    glC (sigmaGL ℝ ℂ ℝ Complex.conjAe t) = conjGL (glC t) :=
  Matrix.GeneralLinearGroup.ext fun i j => ridHom_sigma ((t : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) i j)

private theorem glC_toTensorGL_apply (m : GL (Fin 2) ℝ) (i j : Fin 2) :
    ((glC (toTensorGL ℝ ℂ ℝ m) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j =
      (((m : Matrix (Fin 2) (Fin 2) ℝ) i j : ℝ) : ℂ) := by
  show ridHom ((1 : ℂ) ⊗ₜ[ℝ] ((m : Matrix (Fin 2) (Fin 2) ℝ) i j)) = _
  rw [ridHom_tmul, mul_one]

private theorem sigmaGL_toTensorGL (m : GL (Fin 2) ℝ) :
    sigmaGL ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ m) = toTensorGL ℝ ℂ ℝ m := by
  apply glC_injective
  rw [glC_sigmaGL]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [conjGL_val, cj_apply, glC_toTensorGL_apply, Complex.conj_ofReal]

private theorem normString_two (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) :
    normString ℝ ℂ ℝ Complex.conjAe δ = δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ := by
  simp [normString, Complex.finrank_real_complex, List.range_succ]

private theorem eq_mul_sigma_of_isNormConjugator_one {γ : GL (Fin 2) ℝ} {δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)}
    (h : IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ 1) :
    toTensorGL ℝ ℂ ℝ γ = δ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ := by
  have h' : toTensorGL ℝ ℂ ℝ γ = 1⁻¹ * normString ℝ ℂ ℝ Complex.conjAe δ * 1 := h
  rw [h', normString_two, inv_one, one_mul, mul_one]

private theorem upperTriangular_val (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((upperTriangular a₁ a₂ u h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, u; 0, a₂] := rfl

private theorem ellipticElt_val (r θ : ℝ) (hr : 0 < r) :
    ((ellipticElt r θ hr : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ] := rfl

private def cmat (α β : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![α, β; -β, α]

private theorem glC_toTensorGL_upper (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) :
    ((glC (toTensorGL ℝ ℂ ℝ (upperTriangular a₁ a₂ u h)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![(a₁ : ℂ), (u : ℂ); 0, (a₂ : ℂ)] := by
  ext i j
  rw [glC_toTensorGL_apply, upperTriangular_val]
  fin_cases i <;> fin_cases j <;> simp

private theorem glC_toTensorGL_elliptic (r θ : ℝ) (hr : 0 < r) :
    ((glC (toTensorGL ℝ ℂ ℝ (ellipticElt r θ hr)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      cmat ((r * Real.cos θ : ℝ) : ℂ) ((r * Real.sin θ : ℝ) : ℂ) := by
  ext i j
  rw [glC_toTensorGL_apply, ellipticElt_val]
  fin_cases i <;> fin_cases j <;> simp [cmat]

private theorem mul_entry (M N : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (M * N) i j = M i 0 * N 0 j + M i 1 * N 1 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]

private theorem comm_of_norm {D G : Matrix (Fin 2) (Fin 2) ℂ} (h : D * cj D = G) (hG : cj G = G) :
    D * G = G * D := by
  have h2 : cj D * D = G := by
    have := congrArg cj h
    rwa [cj_mul, cj_cj, hG] at this
  calc D * G = D * (cj D * D) := by rw [h2]
    _ = (D * cj D) * D := (Matrix.mul_assoc _ _ _).symm
    _ = G * D := by rw [h]

private theorem comm_of_twisted {D G S : Matrix (Fin 2) (Fin 2) ℂ} (h : D * cj D = G)
    (hS : S * D = D * cj S) : S * G = G * S := by
  have hS' : cj S * cj D = cj D * S := by
    have := congrArg cj hS
    rwa [cj_mul, cj_mul, cj_cj] at this
  calc S * G = S * (D * cj D) := by rw [h]
    _ = (S * D) * cj D := (Matrix.mul_assoc _ _ _).symm
    _ = (D * cj S) * cj D := by rw [hS]
    _ = D * (cj S * cj D) := Matrix.mul_assoc _ _ _
    _ = D * (cj D * S) := by rw [hS']
    _ = (D * cj D) * S := (Matrix.mul_assoc _ _ _).symm
    _ = G * S := by rw [h]

private theorem centralizer_transport {δ₁ s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)}
    (hs : s ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ₁) :
    ((glC s : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((glC δ₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((glC δ₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        cj ((glC s : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 : s * δ₁ * (sigmaGL ℝ ℂ ℝ Complex.conjAe s)⁻¹ = δ₁ := AutomorphicForm.mem_sigmaCentralizer_iff.mp hs
  have h2 : s * δ₁ = δ₁ * sigmaGL ℝ ℂ ℝ Complex.conjAe s := mul_inv_eq_iff_eq_mul.mp h1
  have h3 := congrArg (fun g => ((glC g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) h2
  simpa only [map_mul, Units.val_mul, glC_sigmaGL, conjGL_val] using h3

private theorem comm_of_glC {t s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)}
    (h : ((glC t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((glC s : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((glC s : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((glC t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) :
    t * s = s * t :=
  glC_injective (by rw [map_mul, map_mul]; exact Units.ext h)

private theorem fibre_of_glC {δ₁ t δ₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)}
    (h : ((glC t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * ((glC δ₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((glC δ₀ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * cj ((glC t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) :
    δ₁ = t⁻¹ * δ₀ * sigmaGL ℝ ℂ ℝ Complex.conjAe t := by
  apply glC_injective
  rw [map_mul, map_mul, map_inv, glC_sigmaGL, mul_assoc, eq_inv_mul_iff_mul_eq]
  exact Units.ext h

private theorem exists_twist (z : ℂ) (s : ℝ) (hz : Complex.normSq z = s ^ 2) :
    ∃ u : ℂ, u ≠ 0 ∧ u * z = s * starRingEnd ℂ u := by
  by_cases h : z = -s
  · refine ⟨Complex.I, Complex.I_ne_zero, ?_⟩
    rw [h, Complex.conj_I]
    ring
  · refine ⟨s + starRingEnd ℂ z, ?_, ?_⟩
    · intro h0
      apply h
      have h1 : starRingEnd ℂ z = -s := by linear_combination h0
      have h2 := congrArg (starRingEnd ℂ) h1
      simpa [Complex.conj_ofReal] using h2
    · have hzz : starRingEnd ℂ z * z = ((s ^ 2 : ℝ) : ℂ) := by rw [← Complex.normSq_eq_conj_mul_self, hz]
      simp only [map_add, Complex.conj_ofReal, Complex.conj_conj]
      push_cast at hzz
      linear_combination hzz

private theorem split_core {a₁ a₂ : ℝ} (hne : a₁ ≠ a₂) {D : Matrix (Fin 2) (Fin 2) ℂ}
    (hD : D * cj D = !![(a₁ : ℂ), ((0 : ℝ) : ℂ); 0, (a₂ : ℂ)]) :
    D 0 1 = 0 ∧ D 1 0 = 0 ∧ Complex.normSq (D 0 0) = a₁ ∧ Complex.normSq (D 1 1) = a₂ := by
  set G : Matrix (Fin 2) (Fin 2) ℂ := !![(a₁ : ℂ), ((0 : ℝ) : ℂ); 0, (a₂ : ℂ)] with hGdef
  have g00 : G 0 0 = a₁ := rfl
  have g01 : G 0 1 = ((0 : ℝ) : ℂ) := rfl
  have g10 : G 1 0 = 0 := rfl
  have g11 : G 1 1 = a₂ := rfl
  have hGr : cj G = G := by
    rw [hGdef]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cj]
  have hc := comm_of_norm hD hGr
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  rw [mul_entry, mul_entry, g01, g11, g00] at e01
  rw [mul_entry, mul_entry, g00, g10, g11] at e10
  push_cast at e01 e10
  have hne' : (a₁ : ℂ) - a₂ ≠ 0 := sub_ne_zero.mpr (fun h => hne (Complex.ofReal_inj.mp h))
  have D01 : D 0 1 = 0 := by
    have : D 0 1 * ((a₁ : ℂ) - a₂) = 0 := by linear_combination -e01
    exact (mul_eq_zero.mp this).resolve_right hne'
  have D10 : D 1 0 = 0 := by
    have : D 1 0 * ((a₁ : ℂ) - a₂) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hne'
  have e00 := congrFun (congrFun hD 0) 0
  have e11 := congrFun (congrFun hD 1) 1
  rw [mul_entry, cj_apply, cj_apply, D01, g00] at e00
  rw [mul_entry, cj_apply, cj_apply, D10, g11] at e11
  refine ⟨D01, D10, ?_, ?_⟩
  · apply Complex.ofReal_inj.mp
    rw [← Complex.mul_conj]
    linear_combination e00
  · apply Complex.ofReal_inj.mp
    rw [← Complex.mul_conj]
    linear_combination e11

private theorem split_fibre (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) (hne : a₁ ≠ a₂) (δ₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hN : toTensorGL ℝ ℂ ℝ (upperTriangular a₁ a₂ 0 h) = δ₁ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ₁) :
    (0 < a₁ ∧ 0 < a₂) ∧
          ∃ t δ₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
            ((Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
              (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
              δ₀ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
              !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)] ∧
            δ₁ = t⁻¹ * δ₀ * sigmaGL ℝ ℂ ℝ Complex.conjAe t ∧
            ∀ s ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ₁, t * s = s * t := by
  set D : Matrix (Fin 2) (Fin 2) ℂ := ((glC δ₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hDdef

  have hD : D * cj D = !![(a₁ : ℂ), ((0 : ℝ) : ℂ); 0, (a₂ : ℂ)] := by
    have e1 : glC (toTensorGL ℝ ℂ ℝ (upperTriangular a₁ a₂ 0 h)) = glC δ₁ * conjGL (glC δ₁) := by
      rw [hN, map_mul, glC_sigmaGL]
    have e2 := congrArg (fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ)) e1
    simp only [Units.val_mul, conjGL_val, glC_toTensorGL_upper] at e2
    rw [hDdef]
    exact e2.symm
  obtain ⟨D01, D10, n1, n2⟩ := split_core hne hD

  have ha₁ : 0 < a₁ :=
    lt_of_le_of_ne (by rw [← n1]; exact Complex.normSq_nonneg _) (Ne.symm (left_ne_zero_of_mul h))
  have ha₂ : 0 < a₂ :=
    lt_of_le_of_ne (by rw [← n2]; exact Complex.normSq_nonneg _) (Ne.symm (right_ne_zero_of_mul h))
  refine ⟨⟨ha₁, ha₂⟩, ?_⟩
  have hs₁ : 0 < Real.sqrt a₁ := Real.sqrt_pos.mpr ha₁
  have hs₂ : 0 < Real.sqrt a₂ := Real.sqrt_pos.mpr ha₂
  obtain ⟨u₁, hu₁, hu₁z⟩ := exists_twist (D 0 0) (Real.sqrt a₁) (by rw [n1, Real.sq_sqrt ha₁.le])
  obtain ⟨u₂, hu₂, hu₂z⟩ := exists_twist (D 1 1) (Real.sqrt a₂) (by rw [n2, Real.sq_sqrt ha₂.le])

  have hdet₀ : Matrix.det !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)] ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simp [hs₁.ne', hs₂.ne']
  have hdetT : Matrix.det !![u₁, 0; 0, u₂] ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simp [hu₁, hu₂]
  let dC : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet₀
  let tC : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetT
  have hdCval : ((dC : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)] := rfl
  have htCval : ((tC : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = !![u₁, 0; 0, u₂] := rfl
  refine ⟨glR tC, glR dC, ?_, ?_, ?_⟩
  ·
    show ((glC (glR dC) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [glC_glR]
    exact hdCval
  ·
    apply fibre_of_glC
    rw [glC_glR, glC_glR, htCval, hdCval, ← hDdef]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, cj_apply, D01, D10, hu₁z, hu₂z]
  ·
    intro s hs
    apply comm_of_glC
    rw [glC_glR, htCval]
    set S : Matrix (Fin 2) (Fin 2) ℂ := ((glC s : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
    have hS : S * D = D * cj S := centralizer_transport hs
    have e01 := congrFun (congrFun hS 0) 1
    have e10 := congrFun (congrFun hS 1) 0
    rw [mul_entry, mul_entry, cj_apply, cj_apply, D01] at e01
    rw [mul_entry, mul_entry, cj_apply, cj_apply, D10] at e10
    simp only [mul_zero, zero_add, zero_mul, add_zero] at e01 e10

    have hne' : a₂ - a₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have S01 : S 0 1 = 0 := by
      have h1 := congrArg Complex.normSq e01
      rw [map_mul, map_mul, Complex.normSq_conj, n1, n2] at h1
      have h2 : Complex.normSq (S 0 1) * (a₂ - a₁) = 0 := by linear_combination h1
      exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hne')
    have S10 : S 1 0 = 0 := by
      have h1 := congrArg Complex.normSq e10
      rw [map_mul, map_mul, Complex.normSq_conj, n1, n2] at h1
      have h2 : Complex.normSq (S 1 0) * (a₂ - a₁) = 0 := by linear_combination -h1
      exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hne')
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, S01, S10, mul_comm]

private theorem cmat_mul (α β α' β' : ℂ) :
    cmat α β * cmat α' β' = cmat (α * α' - β * β') (α * β' + β * α') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cmat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem cj_cmat (α β : ℂ) : cj (cmat α β) = cmat (starRingEnd ℂ α) (starRingEnd ℂ β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cmat, cj]

private theorem cmat_comm (α β α' β' : ℂ) : cmat α β * cmat α' β' = cmat α' β' * cmat α β := by
  rw [cmat_mul, cmat_mul]
  congr 1 <;> ring

private def pco (α β : ℂ) : ℂ := α + Complex.I * β

private def qco (α β : ℂ) : ℂ := α - Complex.I * β

private theorem pco_mul (α β α' β' : ℂ) : pco (α * α' - β * β') (α * β' + β * α') = pco α β * pco α' β' := by
  unfold pco
  linear_combination (-(β * β')) * Complex.I_sq

private theorem qco_mul (α β α' β' : ℂ) : qco (α * α' - β * β') (α * β' + β * α') = qco α β * qco α' β' := by
  unfold qco
  linear_combination (-(β * β')) * Complex.I_sq

private theorem pco_conj (α β : ℂ) : pco (starRingEnd ℂ α) (starRingEnd ℂ β) = starRingEnd ℂ (qco α β) := by
  unfold pco qco
  simp only [map_sub, map_mul, Complex.conj_I]
  ring

private theorem qco_conj (α β : ℂ) : qco (starRingEnd ℂ α) (starRingEnd ℂ β) = starRingEnd ℂ (pco α β) := by
  unfold pco qco
  simp only [map_add, map_mul, Complex.conj_I]
  ring

private theorem cmat_eq_of_co {α β α' β' : ℂ} (hp : pco α β = pco α' β') (hq : qco α β = qco α' β') :
    cmat α β = cmat α' β' := by
  unfold pco at hp
  unfold qco at hq
  have ha : α = α' := by linear_combination (hp + hq) / 2
  have hb : β = β' := by
    have h2 : (2 * Complex.I) * (β - β') = 0 := by linear_combination hp - hq
    have hI : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hI)
  rw [ha, hb]

private theorem det_cmat (α β : ℂ) : Matrix.det (cmat α β) = pco α β * qco α β := by
  unfold cmat pco qco
  rw [Matrix.det_fin_two_of]
  linear_combination (β ^ 2) * Complex.I_sq

private theorem eq_cmat_of_comm {a b : ℂ} (hb : b ≠ 0) {D : Matrix (Fin 2) (Fin 2) ℂ}
    (h : D * cmat a b = cmat a b * D) : D = cmat (D 0 0) (D 0 1) := by
  have c00 : cmat a b 0 0 = a := rfl
  have c01 : cmat a b 0 1 = b := rfl
  have c10 : cmat a b 1 0 = -b := rfl
  have c11 : cmat a b 1 1 = a := rfl
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  rw [mul_entry, mul_entry, c00, c10, c01] at h00
  rw [mul_entry, mul_entry, c01, c11, c00] at h01
  have h10 : D 1 0 = -D 0 1 := by
    have : b * (D 1 0 + D 0 1) = 0 := by linear_combination -h00
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_left hb)
  have h11 : D 1 1 = D 0 0 := by
    have : b * (D 0 0 - D 1 1) = 0 := by linear_combination h01
    exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hb)).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cmat, h10, h11]

private theorem elliptic_fibre (r θ : ℝ) (hr : 0 < r) (hθ : Real.sin θ ≠ 0) (δ₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hN : toTensorGL ℝ ℂ ℝ (ellipticElt r θ hr) = δ₁ * sigmaGL ℝ ℂ ℝ Complex.conjAe δ₁) :
    ∃ t δ₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
            ((Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
              (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
              δ₀ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
              !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
                ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)] ∧
            δ₁ = t⁻¹ * δ₀ * sigmaGL ℝ ℂ ℝ Complex.conjAe t ∧
            ∀ s ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ₁, t * s = s * t := by
  set D : Matrix (Fin 2) (Fin 2) ℂ := ((glC δ₁ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) with hDdef

  set A : ℂ := ((r * Real.cos θ : ℝ) : ℂ) with hA
  set B : ℂ := ((r * Real.sin θ : ℝ) : ℂ) with hB
  set a₀ : ℂ := ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ) with ha₀
  set b₀ : ℂ := ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ) with hb₀
  have hBne : B ≠ 0 := by
    rw [hB]
    exact_mod_cast mul_ne_zero hr.ne' hθ

  have hD : D * cj D = cmat A B := by
    have e1 : glC (toTensorGL ℝ ℂ ℝ (ellipticElt r θ hr)) = glC δ₁ * conjGL (glC δ₁) := by
      rw [hN, map_mul, glC_sigmaGL]
    have e2 := congrArg (fun g : GL (Fin 2) ℂ => (g : Matrix (Fin 2) (Fin 2) ℂ)) e1
    simp only [Units.val_mul, conjGL_val, glC_toTensorGL_elliptic] at e2
    rw [hDdef, hA, hB]
    exact e2.symm
  have hGr : cj (cmat A B) = cmat A B := by rw [cj_cmat, hA, hB, Complex.conj_ofReal, Complex.conj_ofReal]

  have hc : D * cmat A B = cmat A B * D := comm_of_norm hD hGr
  set α : ℂ := D 0 0
  set β : ℂ := D 0 1
  have hDc : D = cmat α β := eq_cmat_of_comm hBne hc

  have hE : cmat (α * starRingEnd ℂ α - β * starRingEnd ℂ β) (α * starRingEnd ℂ β + β * starRingEnd ℂ α) =
      cmat A B := by
    rw [← cmat_mul, ← cj_cmat, ← hDc, hD]
  have E1 : α * starRingEnd ℂ α - β * starRingEnd ℂ β = A := congrFun (congrFun hE 0) 0
  have E2 : α * starRingEnd ℂ β + β * starRingEnd ℂ α = B := congrFun (congrFun hE 0) 1
  set P : ℂ := pco α β with hP
  set Qc : ℂ := starRingEnd ℂ α + Complex.I * starRingEnd ℂ β with hQc
  set P₀ : ℂ := pco a₀ b₀ with hP₀
  have hPQ : P * Qc = A + Complex.I * B := by
    rw [hP, hQc]
    unfold pco
    linear_combination E1 + Complex.I * E2 + β * starRingEnd ℂ β * Complex.I_sq

  have hc2 : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_sq_add_sin_sq (θ / 2)
    conv_lhs => rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
    linear_combination h
  have hs2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    conv_lhs => rw [show θ = 2 * (θ / 2) by ring]
    exact Real.sin_two_mul (θ / 2)
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hP₀sq : P₀ ^ 2 = A + Complex.I * B := by
    have hre : Real.sqrt r ^ 2 * (Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) = r * Real.cos θ := by
      rw [hsq, hc2]
    have him : 2 * (Real.sqrt r ^ 2 * Real.sin (θ / 2) * Real.cos (θ / 2)) = r * Real.sin θ := by
      rw [hsq, hs2]; ring
    have hreC : (Real.sqrt r : ℂ) ^ 2 * ((Real.cos (θ / 2) : ℂ) ^ 2 - (Real.sin (θ / 2) : ℂ) ^ 2) = A := by
      rw [hA]; exact_mod_cast hre
    have himC : 2 * ((Real.sqrt r : ℂ) ^ 2 * (Real.sin (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ)) = B := by
      rw [hB]; exact_mod_cast him
    rw [hP₀, ha₀, hb₀]
    unfold pco
    simp only [Complex.ofReal_mul]
    linear_combination hreC + Complex.I * himC +
      ((Real.sqrt r : ℂ) ^ 2 * (Real.sin (θ / 2) : ℂ) ^ 2) * Complex.I_sq
  have hP₀ne : P₀ ≠ 0 := by
    intro h0
    have h1 : A + Complex.I * B = 0 := by rw [← hP₀sq, h0]; ring
    have h2 := congrArg Complex.im h1
    simp only [hA, hB, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.zero_im, zero_mul, one_mul, zero_add] at h2
    exact (mul_ne_zero hr.ne' hθ) h2
  have hPQ' : P * Qc = P₀ ^ 2 := hPQ.trans hP₀sq.symm
  have hPne : P ≠ 0 := by
    intro h0
    apply pow_ne_zero 2 hP₀ne
    rw [← hPQ', h0, zero_mul]
  have hYne : starRingEnd ℂ P ≠ 0 := fun h0 => hPne (by simpa using congrArg (starRingEnd ℂ) h0)

  set τ₁ : ℂ := (P₀ + starRingEnd ℂ P) / 2 with hτ₁
  set τ₂ : ℂ := (starRingEnd ℂ P - P₀) * Complex.I / 2 with hτ₂
  have hτp : pco τ₁ τ₂ = P₀ := by
    rw [hτ₁, hτ₂]; unfold pco
    linear_combination ((starRingEnd ℂ P - P₀) / 2) * Complex.I_sq
  have hτq : qco τ₁ τ₂ = starRingEnd ℂ P := by
    rw [hτ₁, hτ₂]; unfold qco
    linear_combination (-((starRingEnd ℂ P - P₀) / 2)) * Complex.I_sq
  have hdetT : Matrix.det (cmat τ₁ τ₂) ≠ 0 := by
    rw [det_cmat, hτp, hτq]
    exact mul_ne_zero hP₀ne hYne
  have hdet₀R : Real.sqrt r * Real.cos (θ / 2) * (Real.sqrt r * Real.cos (θ / 2)) -
      Real.sqrt r * Real.sin (θ / 2) * (-(Real.sqrt r * Real.sin (θ / 2))) = r := by
    have h := Real.cos_sq_add_sin_sq (θ / 2)
    have h2 : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
    linear_combination (Real.sqrt r * Real.sqrt r) * h + h2
  have hdet₀ : Matrix.det !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
      ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)] ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    have : ((Real.sqrt r * Real.cos (θ / 2) * (Real.sqrt r * Real.cos (θ / 2)) -
        Real.sqrt r * Real.sin (θ / 2) * (-(Real.sqrt r * Real.sin (θ / 2))) : ℝ) : ℂ) ≠ 0 := by
      rw [hdet₀R]; exact_mod_cast hr.ne'
    exact_mod_cast this
  let dC : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet₀
  let tC : GL (Fin 2) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetT
  have hdCval : ((dC : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = cmat a₀ b₀ := by
    show !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
      ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)] = cmat a₀ b₀
    rw [ha₀, hb₀]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cmat]
  have htCval : ((tC : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = cmat τ₁ τ₂ := rfl

  have hq₀ : qco a₀ b₀ = starRingEnd ℂ P₀ := by
    rw [hP₀, ha₀, hb₀]
    unfold pco qco
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  refine ⟨glR tC, glR dC, ?_, ?_, ?_⟩
  · show ((glC (glR dC) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = _
    rw [glC_glR, hdCval, ha₀, hb₀]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cmat]
  ·
    apply fibre_of_glC
    rw [glC_glR, glC_glR, htCval, hdCval, ← hDdef, hDc, cj_cmat, cmat_mul, cmat_mul]
    apply cmat_eq_of_co
    · rw [pco_mul, pco_mul, hτp, pco_conj, hτq, Complex.conj_conj, ← hP₀, ← hP]
    · rw [qco_mul, qco_mul, hτq, qco_conj, hτp, hq₀]

      have hQ : qco α β = starRingEnd ℂ Qc := by
        rw [hQc]; unfold qco
        simp only [map_add, map_mul, Complex.conj_conj, Complex.conj_I]
        ring
      have h := congrArg (starRingEnd ℂ) hPQ'
      rw [map_mul, map_pow] at h
      rw [hQ, h]
      ring
  ·
    intro s hs
    apply comm_of_glC
    rw [glC_glR, htCval]
    set S : Matrix (Fin 2) (Fin 2) ℂ := ((glC s : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)
    have hS : S * D = D * cj S := centralizer_transport hs
    have hSG : S * cmat A B = cmat A B * S := comm_of_twisted hD hS
    have hSc : S = cmat (S 0 0) (S 0 1) := eq_cmat_of_comm hBne hSG
    rw [hSc]
    exact cmat_comm _ _ _ _

private def companion (τ d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -d; 1, τ]

private def cyc (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![v 0, M 0 0 * v 0 + M 0 1 * v 1; v 1, M 1 0 * v 0 + M 1 1 * v 1]

private theorem mul_cyc (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    M * cyc M v = cyc M v * companion (M 0 0 + M 1 1) (Matrix.det M) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyc, companion, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private theorem det_cyc (M : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    Matrix.det (cyc M v) = v 0 * (M 1 0 * v 0 + M 1 1 * v 1) - (M 0 0 * v 0 + M 0 1 * v 1) * v 1 := by
  unfold cyc
  rw [Matrix.det_fin_two_of]

private theorem exists_det_cyc_ne_zero (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : ¬ (M 1 0 = 0 ∧ M 0 1 = 0 ∧ M 0 0 = M 1 1)) : ∃ v : Fin 2 → ℝ, Matrix.det (cyc M v) ≠ 0 := by
  by_cases h10 : M 1 0 = 0
  · by_cases h01 : M 0 1 = 0
    · have hd : M 0 0 ≠ M 1 1 := fun h => hM ⟨h10, h01, h⟩
      refine ⟨![1, 1], ?_⟩
      rw [det_cyc]
      simp [h10, h01, sub_eq_zero, Ne.symm hd]
    · refine ⟨![0, 1], ?_⟩
      rw [det_cyc]
      simp [h01]
  · refine ⟨![1, 0], ?_⟩
    rw [det_cyc]
    simp [h10]

private theorem exists_conj_of_trace_det (M N : GL (Fin 2) ℝ)
    (hM : ¬ ((M : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 ∧ (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 ∧
      (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1))
    (hN : ¬ ((N : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 ∧ (N : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 ∧
      (N : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (N : Matrix (Fin 2) (Fin 2) ℝ) 1 1))
    (htr : (M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1 =
      (N : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (N : Matrix (Fin 2) (Fin 2) ℝ) 1 1)
    (hdet : Matrix.det (M : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.det (N : Matrix (Fin 2) (Fin 2) ℝ)) :
    ∃ x : GL (Fin 2) ℝ, x⁻¹ * M * x = N := by
  obtain ⟨v, hv⟩ := exists_det_cyc_ne_zero _ hM
  obtain ⟨w, hw⟩ := exists_det_cyc_ne_zero _ hN
  have hdM : Matrix.det (M : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero M
  have hC : Matrix.det (companion ((M : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (M : Matrix (Fin 2) (Fin 2) ℝ) 1 1)
      (Matrix.det (M : Matrix (Fin 2) (Fin 2) ℝ))) ≠ 0 := by
    unfold companion
    rw [Matrix.det_fin_two_of]
    simpa using hdM
  let C : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hC
  let xM : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hv
  let xN : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hw
  have h1 : M * xM = xM * C := Units.ext (mul_cyc (M : Matrix (Fin 2) (Fin 2) ℝ) v)
  have h2 : N * xN = xN * C := Units.ext (by
    have h := mul_cyc (N : Matrix (Fin 2) (Fin 2) ℝ) w
    rw [← htr, ← hdet] at h
    exact h)
  have h1' : xM⁻¹ * (M * xM) = C := inv_mul_eq_iff_eq_mul.mpr h1
  have h2' : xN⁻¹ * (N * xN) = C := inv_mul_eq_iff_eq_mul.mpr h2
  refine ⟨xM * xN⁻¹, ?_⟩
  calc (xM * xN⁻¹)⁻¹ * M * (xM * xN⁻¹) = xN * (xM⁻¹ * (M * xM)) * xN⁻¹ := by group
    _ = xN * C * xN⁻¹ := by rw [h1']
    _ = xN * (xN⁻¹ * (N * xN)) * xN⁻¹ := by rw [h2']
    _ = N := by group

private theorem normal_form (γ : GL (Fin 2) ℝ) (hγ : IsRegularSemisimple γ) :
    ∃ x : GL (Fin 2) ℝ,
        (∃ (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0), a₁ ≠ a₂ ∧ x⁻¹ * γ * x = upperTriangular a₁ a₂ 0 h) ∨
        (∃ (r θ : ℝ) (hr : 0 < r), 0 < θ ∧ θ < Real.pi ∧ x⁻¹ * γ * x = ellipticElt r θ hr) := by
  set M : Matrix (Fin 2) (Fin 2) ℝ := (γ : Matrix (Fin 2) (Fin 2) ℝ)
  have hu : IsUnit (Matrix.trace M ^ 2 - 4 * Matrix.det M) := hγ
  have hdisc : Matrix.trace M ^ 2 - 4 * Matrix.det M ≠ 0 := hu.ne_zero
  rw [Matrix.trace_fin_two] at hdisc
  set τ : ℝ := M 0 0 + M 1 1 with hτ
  set d : ℝ := Matrix.det M with hd
  have hdM : d ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero γ
  have hns : ¬ (M 1 0 = 0 ∧ M 0 1 = 0 ∧ M 0 0 = M 1 1) := by
    rintro ⟨h10, -, h00⟩
    apply hdisc
    rw [hτ, hd, Matrix.det_fin_two, h10, h00]
    ring
  rcases lt_or_gt_of_ne hdisc with hneg | hpos
  ·
    have hdpos : 0 < d := by nlinarith [sq_nonneg τ]
    set r : ℝ := Real.sqrt d
    have hrpos : 0 < r := Real.sqrt_pos.mpr hdpos
    have hr2 : r ^ 2 = d := Real.sq_sqrt hdpos.le
    have h2r : 0 < 2 * r := by positivity
    have hτ2 : τ ^ 2 < (2 * r) ^ 2 := by nlinarith [hneg, hr2]
    obtain ⟨hlo, hhi⟩ := abs_lt_of_sq_lt_sq' hτ2 h2r.le
    set c : ℝ := τ / (2 * r) with hc
    have hc1 : -1 < c := by rw [hc, lt_div_iff₀ h2r]; linarith
    have hc2 : c < 1 := by rw [hc, div_lt_one h2r]; exact hhi
    set θ : ℝ := Real.arccos c
    have hθ0 : 0 < θ := Real.arccos_pos.mpr hc2
    have hθπ : θ < Real.pi := Real.arccos_lt_pi.mpr hc1
    have hcos : Real.cos θ = c := Real.cos_arccos hc1.le hc2.le
    have hsin : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ).ne'
    set N : GL (Fin 2) ℝ := ellipticElt r θ hrpos
    have hNval : (N : Matrix (Fin 2) (Fin 2) ℝ) =
        !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ] := ellipticElt_val r θ hrpos
    have n00 : (N : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = r * Real.cos θ := by rw [hNval]; rfl
    have n01 : (N : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = r * Real.sin θ := by rw [hNval]; rfl
    have n10 : (N : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -(r * Real.sin θ) := by rw [hNval]; rfl
    have n11 : (N : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = r * Real.cos θ := by rw [hNval]; rfl
    have hNns : ¬ ((N : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 ∧ (N : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 ∧
        (N : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (N : Matrix (Fin 2) (Fin 2) ℝ) 1 1) := by
      rintro ⟨-, h01, -⟩
      rw [n01] at h01
      exact mul_ne_zero hrpos.ne' hsin h01
    have htr : M 0 0 + M 1 1 = (N : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (N : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
      have hr0 : r ≠ 0 := hrpos.ne'
      rw [n00, n11, hcos, hc, hτ]
      field_simp
      ring
    have hdet : Matrix.det M = Matrix.det (N : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [hNval, Matrix.det_fin_two_of, ← hd, ← hr2]
      have h := Real.cos_sq_add_sin_sq θ
      linear_combination (-(r ^ 2)) * h
    obtain ⟨x, hx⟩ := exists_conj_of_trace_det γ N hns hNns htr hdet
    exact ⟨x, Or.inr ⟨r, θ, hrpos, hθ0, hθπ, hx⟩⟩
  ·
    set s : ℝ := Real.sqrt (τ ^ 2 - 4 * d)
    have hspos : 0 < s := Real.sqrt_pos.mpr hpos
    have hs2 : s ^ 2 = τ ^ 2 - 4 * d := Real.sq_sqrt hpos.le
    set a₁ : ℝ := (τ + s) / 2 with ha₁
    set a₂ : ℝ := (τ - s) / 2 with ha₂
    have hne : a₁ ≠ a₂ := by
      intro h
      rw [ha₁, ha₂] at h
      have : s = 0 := by linear_combination h
      exact hspos.ne' this
    have hprod : a₁ * a₂ = d := by
      rw [ha₁, ha₂]
      linear_combination (-1 / 4 : ℝ) * hs2
    have h : a₁ * a₂ ≠ 0 := by rw [hprod]; exact hdM
    set N : GL (Fin 2) ℝ := upperTriangular a₁ a₂ 0 h
    have hNval : (N : Matrix (Fin 2) (Fin 2) ℝ) = !![a₁, 0; 0, a₂] := upperTriangular_val a₁ a₂ 0 h
    have n00 : (N : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = a₁ := by rw [hNval]; rfl
    have n11 : (N : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = a₂ := by rw [hNval]; rfl
    have hNns : ¬ ((N : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 ∧ (N : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 ∧
        (N : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = (N : Matrix (Fin 2) (Fin 2) ℝ) 1 1) := by
      rintro ⟨-, -, h00⟩
      rw [n00, n11] at h00
      exact hne h00
    have htr : M 0 0 + M 1 1 = (N : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (N : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
      rw [n00, n11, ha₁, ha₂, hτ]
      ring
    have hdet : Matrix.det M = Matrix.det (N : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [hNval, Matrix.det_fin_two_of, ← hd, ← hprod]
      ring
    obtain ⟨x, hx⟩ := exists_conj_of_trace_det γ N hns hNns htr hdet
    exact ⟨x, Or.inl ⟨a₁, a₂, h, hne, hx⟩⟩

private theorem isNormOf_of_sq (m n : GL (Fin 2) ℝ) (h : n * n = m) :
    IsNormOf ℝ ℂ ℝ Complex.conjAe m (toTensorGL ℝ ℂ ℝ n) := by
  refine ⟨1, ?_⟩
  show toTensorGL ℝ ℂ ℝ m = 1⁻¹ * normString ℝ ℂ ℝ Complex.conjAe (toTensorGL ℝ ℂ ℝ n) * 1
  rw [normString_two, sigmaGL_toTensorGL, ← map_mul, h, inv_one, one_mul, mul_one]

private theorem isNormOf_of_conj (γ x : GL (Fin 2) ℝ) (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (h : IsNormOf ℝ ℂ ℝ Complex.conjAe (x⁻¹ * γ * x) δ) : IsNormOf ℝ ℂ ℝ Complex.conjAe γ δ := by
  obtain ⟨y, hy⟩ := h
  have hy' : toTensorGL ℝ ℂ ℝ (x⁻¹ * γ * x) = y⁻¹ * normString ℝ ℂ ℝ Complex.conjAe δ * y := hy
  rw [map_mul, map_mul, map_inv] at hy'
  refine ⟨y * toTensorGL ℝ ℂ ℝ x⁻¹, ?_⟩
  show toTensorGL ℝ ℂ ℝ γ = (y * toTensorGL ℝ ℂ ℝ x⁻¹)⁻¹ * normString ℝ ℂ ℝ Complex.conjAe δ *
    (y * toTensorGL ℝ ℂ ℝ x⁻¹)
  rw [map_inv]
  have h1 : toTensorGL ℝ ℂ ℝ γ =
      toTensorGL ℝ ℂ ℝ x * (y⁻¹ * normString ℝ ℂ ℝ Complex.conjAe δ * y) * (toTensorGL ℝ ℂ ℝ x)⁻¹ := by
    rw [← hy']
    group
  rw [h1]
  group

private theorem upperTriangular_sqrt_sq {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (h : a₁ * a₂ ≠ 0)
    (h' : Real.sqrt a₁ * Real.sqrt a₂ ≠ 0) :
    upperTriangular (Real.sqrt a₁) (Real.sqrt a₂) 0 h' * upperTriangular (Real.sqrt a₁) (Real.sqrt a₂) 0 h' =
      upperTriangular a₁ a₂ 0 h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, upperTriangular_val, upperTriangular_val]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Real.mul_self_sqrt ha₁.le, Real.mul_self_sqrt ha₂.le]

private theorem ellipticElt_sqrt_sq {r : ℝ} (θ : ℝ) (hr : 0 < r) (hr' : 0 < Real.sqrt r) :
    ellipticElt (Real.sqrt r) (θ / 2) hr' * ellipticElt (Real.sqrt r) (θ / 2) hr' = ellipticElt r θ hr := by
  have hc2 : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_sq_add_sin_sq (θ / 2)
    conv_lhs => rw [show θ = 2 * (θ / 2) by ring, Real.cos_two_mul]
    linear_combination h
  have hs2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    conv_lhs => rw [show θ = 2 * (θ / 2) by ring]
    exact Real.sin_two_mul (θ / 2)
  have hrr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, ellipticElt_val, ellipticElt_val]
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hc2]
    linear_combination (Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * hrr
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hs2]
    linear_combination (2 * Real.sin (θ / 2) * Real.cos (θ / 2)) * hrr
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hs2]
    linear_combination (-(2 * Real.sin (θ / 2) * Real.cos (θ / 2))) * hrr
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [hc2]
    linear_combination (Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2) * hrr

private theorem non_norm (γ : GL (Fin 2) ℝ) (hγ : IsRegularSemisimple γ)
    (hnot : ¬ ∃ δ, IsNormOf ℝ ℂ ℝ Complex.conjAe γ δ) :
    ∃ (x : GL (Fin 2) ℝ) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0),
        a₁ ≠ a₂ ∧ (a₁ < 0 ∨ a₂ < 0) ∧ x⁻¹ * γ * x = upperTriangular a₁ a₂ 0 h := by
  obtain ⟨x, hx⟩ := normal_form γ hγ
  rcases hx with ⟨a₁, a₂, h, hne, hx⟩ | ⟨r, θ, hr, -, -, hx⟩
  · refine ⟨x, a₁, a₂, h, hne, ?_, hx⟩
    by_contra hcon
    have ha₁ : 0 < a₁ :=
      lt_of_le_of_ne (not_lt.mp (fun h' => hcon (Or.inl h'))) (Ne.symm (left_ne_zero_of_mul h))
    have ha₂ : 0 < a₂ :=
      lt_of_le_of_ne (not_lt.mp (fun h' => hcon (Or.inr h'))) (Ne.symm (right_ne_zero_of_mul h))
    apply hnot
    have h' : Real.sqrt a₁ * Real.sqrt a₂ ≠ 0 :=
      mul_ne_zero (Real.sqrt_pos.mpr ha₁).ne' (Real.sqrt_pos.mpr ha₂).ne'
    refine ⟨toTensorGL ℝ ℂ ℝ (upperTriangular (Real.sqrt a₁) (Real.sqrt a₂) 0 h'), ?_⟩
    apply isNormOf_of_conj γ x
    rw [hx]
    exact isNormOf_of_sq _ _ (upperTriangular_sqrt_sq ha₁ ha₂ h h')
  · exfalso
    apply hnot
    have hr' : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    refine ⟨toTensorGL ℝ ℂ ℝ (ellipticElt (Real.sqrt r) (θ / 2) hr'), ?_⟩
    apply isNormOf_of_conj γ x
    rw [hx]
    exact isNormOf_of_sq _ _ (ellipticElt_sqrt_sq θ hr hr')

end ConjNormFibre

theorem solution :
    (∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ →
      ∃ x : GL (Fin 2) ℝ,
        (∃ (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0), a₁ ≠ a₂ ∧ x⁻¹ * γ * x = upperTriangular a₁ a₂ 0 h) ∨
        (∃ (r θ : ℝ) (hr : 0 < r), 0 < θ ∧ θ < Real.pi ∧ x⁻¹ * γ * x = ellipticElt r θ hr)) ∧
    (∀ (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0), a₁ ≠ a₂ →
      ∀ δ₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (upperTriangular a₁ a₂ 0 h) δ₁ 1 →
          (0 < a₁ ∧ 0 < a₂) ∧
          ∃ t δ₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
            ((Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
              (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
              δ₀ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
              !![((Real.sqrt a₁ : ℝ) : ℂ), 0; 0, ((Real.sqrt a₂ : ℝ) : ℂ)] ∧
            δ₁ = t⁻¹ * δ₀ * sigmaGL ℝ ℂ ℝ Complex.conjAe t ∧
            ∀ s ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ₁, t * s = s * t) ∧
    (∀ (r θ : ℝ) (hr : 0 < r), Real.sin θ ≠ 0 →
      ∀ δ₁ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (ellipticElt r θ hr) δ₁ 1 →
          ∃ t δ₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
            ((Matrix.GeneralLinearGroup.map
              (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
              (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom
              δ₀ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
              !![((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ), ((Real.sqrt r * Real.sin (θ / 2) : ℝ) : ℂ);
                ((-(Real.sqrt r * Real.sin (θ / 2)) : ℝ) : ℂ), ((Real.sqrt r * Real.cos (θ / 2) : ℝ) : ℂ)] ∧
            δ₁ = t⁻¹ * δ₀ * sigmaGL ℝ ℂ ℝ Complex.conjAe t ∧
            ∀ s ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ₁, t * s = s * t) ∧
    (∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ → (¬ ∃ δ, IsNormOf ℝ ℂ ℝ Complex.conjAe γ δ) →
      ∃ (x : GL (Fin 2) ℝ) (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0),
        a₁ ≠ a₂ ∧ (a₁ < 0 ∨ a₂ < 0) ∧ x⁻¹ * γ * x = upperTriangular a₁ a₂ 0 h) := by
  refine ⟨fun γ hγ => ConjNormFibre.normal_form γ hγ, fun a₁ a₂ h hne δ₁ hδ => ?_,
    fun r θ hr hθ δ₁ hδ => ?_, fun γ hγ hnot => ConjNormFibre.non_norm γ hγ hnot⟩
  · exact ConjNormFibre.split_fibre a₁ a₂ h hne δ₁ (ConjNormFibre.eq_mul_sigma_of_isNormConjugator_one hδ)
  · exact ConjNormFibre.elliptic_fibre r θ hr hθ δ₁ (ConjNormFibre.eq_mul_sigma_of_isNormConjugator_one hδ)

end
end S_AutomorphicForm_GL2Real_exists_conj_normalForm_and_normFibre_and_nonNorm_conjAe
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_exists_conj_normalForm_and_normFibre_and_nonNorm_conjAe (solution)
