-- Prove2me | solution 1 for AutomorphicForm.exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2a552266-9792-5510-8662-fbf13231d0d5

import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isComplex

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel Matrix
open scoped ComplexConjugate

namespace R4ArchPolyC

def Mcd (c d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![conj d, -conj c; c, d]

def pt (v : Fin 2 → ℂ) : Fin 2 ⊕ Fin 2 → ℂ := Sum.elim v (fun i => conj (v i))

def IsPolyOnMcd (G : Matrix (Fin 2) (Fin 2) ℂ → ℂ) : Prop :=
  ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ, ∀ v : Fin 2 → ℂ, G (Mcd (v 0) (v 1)) = MvPolynomial.eval (pt v) P

theorem isPolyOnMcd_zero : IsPolyOnMcd 0 := ⟨0, fun v => by simp⟩

theorem IsPolyOnMcd.add {G H : Matrix (Fin 2) (Fin 2) ℂ → ℂ} (hG : IsPolyOnMcd G) (hH : IsPolyOnMcd H) :
    IsPolyOnMcd (G + H) := by
  obtain ⟨P, hP⟩ := hG
  obtain ⟨Q, hQ⟩ := hH
  exact ⟨P + Q, fun v => by rw [Pi.add_apply, hP, hQ, map_add]⟩

theorem IsPolyOnMcd.smul {G : Matrix (Fin 2) (Fin 2) ℂ → ℂ} (a : ℂ) (hG : IsPolyOnMcd G) :
    IsPolyOnMcd (a • G) := by
  obtain ⟨P, hP⟩ := hG
  exact ⟨MvPolynomial.C a * P, fun v => by rw [Pi.smul_apply, hP, map_mul, MvPolynomial.eval_C, smul_eq_mul]⟩

theorem IsPolyOnMcd.mul {G H : Matrix (Fin 2) (Fin 2) ℂ → ℂ} (hG : IsPolyOnMcd G) (hH : IsPolyOnMcd H) :
    IsPolyOnMcd (G * H) := by
  obtain ⟨P, hP⟩ := hG
  obtain ⟨Q, hQ⟩ := hH
  exact ⟨P * Q, fun v => by rw [Pi.mul_apply, hP, hQ, map_mul]⟩

theorem isPolyOnMcd_one : IsPolyOnMcd (fun _ => 1) := ⟨1, fun v => by simp⟩

theorem Mcd_eq_smul (c d : ℂ) :
    Mcd c d = (c.re : ℝ) • Mcd 1 0 + (c.im : ℝ) • Mcd Complex.I 0 + (d.re : ℝ) • Mcd 0 1
      + (d.im : ℝ) • Mcd 0 Complex.I := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    { simp only [Mcd, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, Matrix.of_apply, Matrix.cons_val',
        Matrix.empty_val', Matrix.cons_val_fin_one]
      apply Complex.ext <;> simp }

theorem lin_identity (g g' c : ℂ) :
    (g - Complex.I * g') / 2 * c + (g + Complex.I * g') / 2 * conj c = (c.re : ℂ) * g + (c.im : ℂ) * g' := by
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im]
    ring
  · simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im]
    ring

theorem isPolyOnMcd_functional (φ : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ) : IsPolyOnMcd φ := by
  refine ⟨MvPolynomial.C ((φ (Mcd 1 0) - Complex.I * φ (Mcd Complex.I 0)) / 2) * MvPolynomial.X (Sum.inl 0)
      + MvPolynomial.C ((φ (Mcd 1 0) + Complex.I * φ (Mcd Complex.I 0)) / 2) * MvPolynomial.X (Sum.inr 0)
      + MvPolynomial.C ((φ (Mcd 0 1) - Complex.I * φ (Mcd 0 Complex.I)) / 2) * MvPolynomial.X (Sum.inl 1)
      + MvPolynomial.C ((φ (Mcd 0 1) + Complex.I * φ (Mcd 0 Complex.I)) / 2) * MvPolynomial.X (Sum.inr 1),
    fun v => ?_⟩
  simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, pt, Sum.elim_inl, Sum.elim_inr]
  rw [Mcd_eq_smul (v 0) (v 1), map_add, map_add, map_add, φ.map_smul, φ.map_smul, φ.map_smul, φ.map_smul,
    Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul]
  have h0 := lin_identity (φ (Mcd 1 0)) (φ (Mcd Complex.I 0)) (v 0)
  have h1 := lin_identity (φ (Mcd 0 1)) (φ (Mcd 0 Complex.I)) (v 1)
  linear_combination -(h0 + h1)

theorem isPolyOnMcd_list_prod (l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ)) :
    IsPolyOnMcd (fun m => (l.map (fun φ => φ m)).prod) := by
  induction l with
  | nil => simpa using isPolyOnMcd_one
  | cons φ l ih =>
    have h : (fun m => ((φ :: l).map (fun ψ => ψ m)).prod)
        = (fun m => φ m) * (fun m => (l.map (fun ψ => ψ m)).prod) := by
      funext m
      simp [List.map_cons, List.prod_cons]
    rw [h]
    exact (isPolyOnMcd_functional φ).mul ih

theorem isPolyOnMcd_of_mem_span {G : Matrix (Fin 2) (Fin 2) ℂ → ℂ}
    (hG : G ∈ Submodule.span ℂ
        {F : Matrix (Fin 2) (Fin 2) ℂ → ℂ |
          ∃ l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod}) :
    IsPolyOnMcd G := by
  induction hG using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, rfl⟩ := hx
    exact isPolyOnMcd_list_prod l
  | zero => exact isPolyOnMcd_zero
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact hx.smul a

theorem entries_of_unitary_det_one {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hdet : A.det = 1) : A 0 0 = conj (A 1 1) ∧ A 0 1 = -conj (A 1 0) := by
  have h1 : star A * A = 1 := Matrix.mem_unitaryGroup_iff'.mp hA
  have h2 : A * A.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
  have hadj : star A = A.adjugate := by
    calc star A = star A * (A * A.adjugate) := by rw [h2, mul_one]
      _ = (star A * A) * A.adjugate := by rw [mul_assoc]
      _ = A.adjugate := by rw [h1, one_mul]
  rw [Matrix.adjugate_fin_two] at hadj
  have e00 := congrFun (congrFun hadj 0) 0
  have e10 := congrFun (congrFun hadj 1) 0
  simp only [Matrix.star_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e10
  have hstar : ∀ z : ℂ, star z = conj z := fun _ => rfl
  rw [hstar] at e00 e10
  refine ⟨?_, ?_⟩
  · rw [← e00, RCLike.conj_conj]
  · have := congrArg conj e10
    rw [RCLike.conj_conj, map_neg] at this
    exact this

theorem eq_Mcd_of_unitary_det_one {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hdet : A.det = 1) : A = Mcd (A 1 0) (A 1 1) := by
  obtain ⟨h00, h01⟩ := entries_of_unitary_det_one hA hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mcd, h00, h01, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]

section Diag

variable {L : Type*} [NormedField L]

def diagGL (u : Lˣ) : GL (Fin 2) L where
  val := !![(u : L), 0; 0, 1]
  inv := !![((u⁻¹ : Lˣ) : L), 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagGL_apply_00 (u : Lˣ) : ((diagGL u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = u := rfl
theorem diagGL_apply_01 (u : Lˣ) : ((diagGL u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := rfl
theorem diagGL_apply_10 (u : Lˣ) : ((diagGL u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := rfl
theorem diagGL_apply_11 (u : Lˣ) : ((diagGL u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := rfl
theorem diagGL_inv_apply_10 (u : Lˣ) :
    (((diagGL u)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := rfl
theorem diagGL_inv_apply_11 (u : Lˣ) :
    (((diagGL u)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := rfl
theorem diagGL_inv_apply_00 (u : Lˣ) :
    (((diagGL u)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = ((u⁻¹ : Lˣ) : L) := rfl
theorem diagGL_inv_apply_01 (u : Lˣ) :
    (((diagGL u)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := rfl

theorem diagGL_mem_borelSubgroup (u : Lˣ) : diagGL u ∈ borelSubgroup L := rfl

theorem det_diagGL (u : Lˣ) : ((diagGL u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = u := by
  rw [Matrix.det_fin_two, diagGL_apply_00, diagGL_apply_01, diagGL_apply_10, diagGL_apply_11]
  ring

theorem isRowIsometry_diagGL {u : Lˣ} (hu : ‖(u : L)‖ = 1) : IsRowIsometry (diagGL u) := by
  refine ⟨by rw [det_diagGL, hu], fun x y => ?_⟩
  rw [diagGL_apply_00, diagGL_apply_01, diagGL_apply_10, diagGL_apply_11, mul_zero, add_zero, mul_zero,
    zero_add, mul_one, norm_mul, hu, mul_one]

theorem borelDiagFst_diagGL (u : Lˣ) :
    borelDiagFst (⟨diagGL u, diagGL_mem_borelSubgroup u⟩ : ↥(borelSubgroup L)) = u := by
  apply Units.ext
  rfl

theorem borelDiagSnd_diagGL (u : Lˣ) :
    borelDiagSnd (⟨diagGL u, diagGL_mem_borelSubgroup u⟩ : ↥(borelSubgroup L)) = 1 := by
  apply Units.ext
  rfl

theorem diagGL_inv_mul_apply_one (u : Lˣ) (k : GL (Fin 2) L) (j : Fin 2) :
    ((((diagGL u)⁻¹ * k : GL (Fin 2) L)) : Matrix (Fin 2) (Fin 2) L) 1 j = (k : Matrix (Fin 2) (Fin 2) L) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, diagGL_inv_apply_10,
    diagGL_inv_apply_11, zero_mul, zero_add, one_mul]

theorem det_diagGL_det_inv_mul (k : GL (Fin 2) L) :
    ((((diagGL (Matrix.GeneralLinearGroup.det k))⁻¹ * k : GL (Fin 2) L)) : Matrix (Fin 2) (Fin 2) L).det = 1 := by
  have h : (Matrix.GeneralLinearGroup.det ((diagGL (Matrix.GeneralLinearGroup.det k))⁻¹ * k) : Lˣ) = 1 := by
    rw [map_mul, map_inv]
    have hd : Matrix.GeneralLinearGroup.det (diagGL (Matrix.GeneralLinearGroup.det k)) =
        Matrix.GeneralLinearGroup.det k := by
      apply Units.ext
      exact det_diagGL _
    rw [hd, inv_mul_cancel]
  have := congrArg Units.val h
  simpa using this

end Diag

section Main

variable {F : Type} [Field F] {w : InfinitePlace F}

def polyGen : Set (Matrix (Fin 2) (Fin 2) ℂ → ℂ) :=
  {F : Matrix (Fin 2) (Fin 2) ℂ → ℂ | ∃ l : List (Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] ℂ), F = fun m => (l.map (fun φ => φ m)).prod}

theorem main (hw : w.IsComplex)
    (η₁ η₂ : (w.Completion)ˣ →* ℂˣ)
    (f : GL (Fin 2) w.Completion → ℂ) (hfc : Continuous f)
    (hfK : RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) f)
    (hfB : ∀ (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion), IsRowIsometry b →
        ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
          f (b * g) = ((η₁ (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * ((η₂ (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ) * f g) :
    ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ,
      ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
        f k = ((η₁ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
          * MvPolynomial.eval
              (Sum.elim (fun i => extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                (fun i => starRingEnd ℂ
                  (extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i)))) P := by
  classical
  set L := w.Completion
  obtain ⟨e, he⟩ :=
    AutomorphicForm.exists_continuousMulEquiv_rowIsometrySubgroup_unitaryGroup_of_isComplex F w hw

  set Φ : ↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ := fun A => f ((e.symm A : ↥(rowIsometrySubgroup L)) : GL (Fin 2) L)
    with hΦ_def
  have hΦc : Continuous Φ := hfc.comp (continuous_subtype_val.comp (map_continuous e.symm))

  have hΦfin : ∃ s : Finset (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ),
      ∀ A' : ↥(Matrix.unitaryGroup (Fin 2) ℂ),
        (fun A => Φ (A * A')) ∈ Submodule.span ℂ (s : Set (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ)) := by
    obtain ⟨s, hs⟩ := hfK
    let r : (GL (Fin 2) L → ℂ) →ₗ[ℂ] (↥(Matrix.unitaryGroup (Fin 2) ℂ) → ℂ) :=
      { toFun := fun g A => g ((e.symm A : ↥(rowIsometrySubgroup L)) : GL (Fin 2) L)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine ⟨s.image r, fun A' => ?_⟩
    set k' : GL (Fin 2) L := ((e.symm A' : ↥(rowIsometrySubgroup L)) : GL (Fin 2) L) with hk'
    have hk'mem : k' ∈ rowIsometrySubgroup L := (e.symm A').2
    have hmem := hs k' hk'mem
    have heq : (fun A => Φ (A * A')) = r (fun x => f (x * k')) := by
      funext A
      simp only [hΦ_def, r, LinearMap.coe_mk, AddHom.coe_mk, map_mul, Subgroup.coe_mul, hk']
    rw [heq, Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hmem
  obtain ⟨G, hGmem, hG⟩ :=
    Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite Φ hΦc hΦfin
  obtain ⟨P, hP⟩ := isPolyOnMcd_of_mem_span hGmem
  refine ⟨P, fun k hk => ?_⟩

  set δ : Lˣ := Matrix.GeneralLinearGroup.det k with hδ
  have hδnorm : ‖(δ : L)‖ = 1 := hk.1
  set b : GL (Fin 2) L := diagGL δ with hb_def
  have hb : b ∈ borelSubgroup L := diagGL_mem_borelSubgroup δ
  have hbiso : IsRowIsometry b := isRowIsometry_diagGL hδnorm
  set k₀ : GL (Fin 2) L := b⁻¹ * k with hk₀_def
  have hk₀ : IsRowIsometry k₀ := hbiso.inv.mul hk
  have hkfac : k = b * k₀ := by rw [hk₀_def, mul_inv_cancel_left]
  have hfk : f k = ((η₁ δ : ℂˣ) : ℂ) * f k₀ := by
    rw [hkfac, hfB b hb hbiso k₀ hk₀]
    have h1 : borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup L)) = δ := borelDiagFst_diagGL δ
    have h2 : borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup L)) = 1 := borelDiagSnd_diagGL δ
    rw [h1, h2, map_one, Units.val_one, mul_one]

  set A₀ : ↥(Matrix.unitaryGroup (Fin 2) ℂ) := e ⟨k₀, hk₀⟩ with hA₀
  have hA₀ent : ∀ i j, ((A₀ : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) i j
      = extensionEmbedding w ((k₀ : Matrix (Fin 2) (Fin 2) L) i j) := fun i j => he ⟨k₀, hk₀⟩ i j
  have hA₀map : ((A₀ : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)
      = (extensionEmbedding w).mapMatrix (k₀ : Matrix (Fin 2) (Fin 2) L) := by
    ext i j
    rw [hA₀ent]
    rfl
  have hdetk₀ : ((k₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = 1 := det_diagGL_det_inv_mul k
  have hrow : ∀ j : Fin 2, ((k₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 j = (k : Matrix (Fin 2) (Fin 2) L) 1 j :=
    fun j => diagGL_inv_mul_apply_one δ k j
  have hA₀det : ((A₀ : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
    rw [hA₀map, ← RingHom.map_det, hdetk₀, map_one]
  have hA₀eq : ((A₀ : ↥(Matrix.unitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)
      = Mcd (extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) L) 1 0))
          (extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) L) 1 1)) := by
    rw [eq_Mcd_of_unitary_det_one A₀.2 hA₀det, hA₀ent, hA₀ent, hrow, hrow]

  have hfk₀ : f k₀ = Φ A₀ := by
    simp only [hΦ_def, hA₀, ContinuousMulEquiv.symm_apply_apply]
  rw [hfk, hfk₀, hG A₀, hA₀eq]
  congr 1
  exact hP (fun i => extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) L) 1 i))

end Main

end R4ArchPolyC

end

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem solution
    (F : Type) [Field F] (w : InfinitePlace F) (_hw : w.IsComplex)
    (η₁ η₂ : (w.Completion)ˣ →* ℂˣ)
    (f : GL (Fin 2) w.Completion → ℂ) (_hfc : Continuous f)
    (_hfK : RightTranslatesSpanFinite (rowIsometrySubgroup w.Completion) f)
    (_hfB : ∀ (b : GL (Fin 2) w.Completion) (hb : b ∈ borelSubgroup w.Completion), IsRowIsometry b →
        ∀ g : GL (Fin 2) w.Completion, IsRowIsometry g →
          f (b * g) = ((η₁ (borelDiagFst (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ)
            * ((η₂ (borelDiagSnd (⟨b, hb⟩ : ↥(borelSubgroup w.Completion))) : ℂˣ) : ℂ) * f g) :
    ∃ P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ,
      ∀ k : GL (Fin 2) w.Completion, IsRowIsometry k →
        f k = ((η₁ (Matrix.GeneralLinearGroup.det k) : ℂˣ) : ℂ)
          * MvPolynomial.eval
              (Sum.elim (fun i => extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i))
                (fun i => starRingEnd ℂ
                  (extensionEmbedding w ((k : Matrix (Fin 2) (Fin 2) w.Completion) 1 i)))) P :=
  R4ArchPolyC.main _hw η₁ η₂ f _hfc _hfK _hfB

end S_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isComplex
end P2MW
export P2MW.S_AutomorphicForm_exists_mvPolynomial_apply_eq_mul_eval_bottomRow_of_rightTranslatesSpanFinite_of_isComplex (solution)
