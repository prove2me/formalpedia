-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6afa62e1-559c-5b05-9c77-be0177ab366c

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section
open MeasureTheory Complex
open scoped Real

namespace EvalCoords

variable {X : Type*}

def vanishingOn (E : Submodule ℂ (X → ℂ)) (s : Finset X) : Submodule ℂ E where
  carrier := {e | ∀ x ∈ s, (e : X → ℂ) x = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb x hx => by
    simp only [Submodule.coe_add, Pi.add_apply, ha x hx, hb x hx, add_zero]
  smul_mem' := fun c {a} ha x hx => by
    simp only [Submodule.coe_smul, Pi.smul_apply, ha x hx, smul_zero]

theorem vanishingOn_mono (E : Submodule ℂ (X → ℂ)) {s t : Finset X} (h : s ⊆ t) :
    vanishingOn E t ≤ vanishingOn E s := fun _ he x hx => he x (h hx)

theorem exists_finset_separating (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ s : Finset X, ∀ e ∈ E, (∀ x ∈ s, e x = 0) → e = 0 := by
  classical

  have key : ∀ k : ℕ, k ≤ Module.finrank ℂ E →
      ∃ s : Finset X, Module.finrank ℂ (vanishingOn E s) ≤ Module.finrank ℂ E - k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨∅, (Submodule.finrank_le _).trans le_rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨s, hs⟩ := ih (Nat.le_of_succ_le hk)
      by_cases hbot : vanishingOn E s = ⊥
      · refine ⟨s, ?_⟩
        rw [hbot, finrank_bot]
        exact Nat.zero_le _
      · obtain ⟨e, he, hne⟩ := (Submodule.ne_bot_iff _).mp hbot
        have hne' : (e : X → ℂ) ≠ 0 := fun h => hne (Subtype.ext h)
        obtain ⟨x, hx⟩ := Function.ne_iff.mp hne'
        refine ⟨insert x s, ?_⟩
        have hlt : vanishingOn E (insert x s) < vanishingOn E s := by
          refine lt_of_le_of_ne (vanishingOn_mono E (Finset.subset_insert x s)) fun h => ?_
          have : e ∈ vanishingOn E (insert x s) := h ▸ he
          exact hx (this x (Finset.mem_insert_self x s))
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
  obtain ⟨s, hs⟩ := key (Module.finrank ℂ E) le_rfl
  rw [Nat.sub_self, Nat.le_zero] at hs
  refine ⟨s, fun e he h0 => ?_⟩
  have hmem : (⟨e, he⟩ : E) ∈ vanishingOn E s := h0
  rw [Submodule.finrank_eq_zero.mp hs, Submodule.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem exists_eval_coords (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ (s : Finset X) (b : X → X → ℂ), (∀ x, b x ∈ E) ∧ ∀ e ∈ E, e = ∑ x ∈ s, e x • b x := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_separating E

  let res : E →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun e x => (e : X → ℂ) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker res = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun e he => ?_
    rw [LinearMap.mem_ker] at he
    apply Subtype.ext
    exact hs e e.2 fun x hx => congrFun he ⟨x, hx⟩
  obtain ⟨g, hg⟩ := res.exists_leftInverse_of_injective hker
  let b : X → X → ℂ := fun x => if hx : x ∈ s then ((g (Pi.single (⟨x, hx⟩ : s) 1) : E) : X → ℂ) else 0
  refine ⟨s, b, fun x => ?_, fun e he => ?_⟩
  · simp only [b]
    split_ifs
    · exact Submodule.coe_mem _
    · exact E.zero_mem
  · have h1 : (⟨e, he⟩ : E) = g (res ⟨e, he⟩) := (LinearMap.congr_fun hg ⟨e, he⟩).symm
    have h2 : res ⟨e, he⟩ = ∑ x : s, e x • (Pi.single x (1 : ℂ) : s → ℂ) := by
      ext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single y]
      · simp [res]
      · intro z _ hzy; simp [Ne.symm hzy]
      · intro hy; exact absurd (Finset.mem_univ y) hy
    have h3 : e = ((g (res ⟨e, he⟩) : E) : X → ℂ) := congrArg Subtype.val h1
    conv_lhs => rw [h3, h2, map_sum]
    rw [Submodule.coe_sum, Finset.univ_eq_attach, ← Finset.sum_attach s (fun x => e x • b x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, Submodule.coe_smul]
    simp only [b, dif_pos x.2]

end EvalCoords

end

noncomputable section

namespace KUNIFPlace

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

variable {L : Type*} [NormedField L]

theorem diagOne_coe (t : Lˣ) :
    ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = Matrix.diagonal ![(t : L), 1] := rfl

theorem isRowIsometry_diagOne (t : Lˣ) (ht : ‖(t : L)‖ = 1) : IsRowIsometry (diagOne t) := by
  have h00 : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = t := by simp [diagOne_coe]
  have h01 : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by simp [diagOne_coe]
  have h10 : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by simp [diagOne_coe]
  have h11 : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by simp [diagOne_coe]
  refine ⟨?_, fun x y => ?_⟩
  · rw [diagOne_coe, Matrix.det_diagonal]
    simp [ht]
  · rw [h00, h01, h10, h11, mul_zero, add_zero, mul_zero, zero_add, mul_one, norm_mul, ht, mul_one]

theorem scalar_coe (u : Lˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      Matrix.diagonal fun _ => (u : L) := by
  show Matrix.scalar (Fin 2) (u : L) = _
  exact Matrix.scalar_apply _

theorem isRowIsometry_scalar (u : Lˣ) (hu : ‖(u : L)‖ = 1) :
    IsRowIsometry (Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
  have h00 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = u := by
    simp
  have h01 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
    simp
  have h10 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    simp
  have h11 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = u := by
    simp
  refine ⟨?_, fun x y => ?_⟩
  · rw [scalar_coe, Matrix.det_diagonal]
    simp [hu]
  · rw [h00, h01, h10, h11, mul_zero, add_zero, mul_zero, zero_add, norm_mul, norm_mul, hu, mul_one, mul_one]

theorem det_scalar_two (u : Lˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = (u : L) * u := by
  rw [scalar_coe, Matrix.det_diagonal, Fin.prod_univ_two]

theorem det_diagOne (t : Lˣ) : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = t := by
  rw [diagOne_coe, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

variable {K : Type*} [Field K] [NumberField K]

theorem exists_sq_eq_of_norm_eq_one (c : ℂ) (hc : ‖c‖ = 1) : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ζ * ζ = c := by
  refine ⟨Complex.exp (((Complex.arg c / 2 : ℝ) : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I _, ?_⟩
  rw [← Complex.exp_add]
  have : ((Complex.arg c / 2 : ℝ) : ℂ) * Complex.I + ((Complex.arg c / 2 : ℝ) : ℂ) * Complex.I = Complex.arg c * Complex.I := by
    push_cast; ring
  rw [this]
  have h := Complex.norm_mul_exp_arg_mul_I c
  rwa [hc, Complex.ofReal_one, one_mul] at h

omit [NumberField K] in
theorem norm_extensionEmbedding (w : InfinitePlace K) (x : w.Completion) : ‖extensionEmbedding w x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

omit [NumberField K] in

theorem sq_eq_one_or_exists_sqrt (w : InfinitePlace K) (δ : w.Completion) (hδ : ‖δ‖ = 1) :
    δ * δ = 1 ∨ ∃ ζ : w.Completion, ‖ζ‖ = 1 ∧ ζ * ζ = δ := by
  by_cases hw : w.IsReal
  · left
    set e := ringEquivRealOfIsReal hw
    have hr : ‖e δ‖ = 1 := by
      rw [ringEquivRealOfIsReal_apply]
      rw [← hδ]
      exact (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) δ
    have hsq : e δ * e δ = 1 := by
      rcases (abs_eq (zero_le_one : (0 : ℝ) ≤ 1)).mp (by rw [← Real.norm_eq_abs]; exact hr) with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
    apply e.injective
    rw [map_mul, map_one, hsq]
  · right
    have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    set e := ringEquivComplexOfIsComplex hw'
    have hc : ‖e δ‖ = 1 := by rw [ringEquivComplexOfIsComplex_apply, norm_extensionEmbedding, hδ]
    obtain ⟨ζ, hζ, hζζ⟩ := exists_sq_eq_of_norm_eq_one (e δ) hc
    refine ⟨e.symm ζ, ?_, ?_⟩
    · have := norm_extensionEmbedding w (e.symm ζ)
      rw [← ringEquivComplexOfIsComplex_apply hw', RingEquiv.apply_symm_apply] at this
      rw [← this, hζ]
    · apply e.injective
      rw [map_mul, RingEquiv.apply_symm_apply, hζζ]

omit [NumberField K] in

private theorem _root_.KUNIFPlace.exists_factor (w : InfinitePlace K) (κ : GL (Fin 2) w.Completion) (hκ : IsRowIsometry κ) :
    ∃ (s ζ : (w.Completion)ˣ) (κ' : rowIsometrySubgroup₀ w.Completion),
      ‖(s : w.Completion)‖ = 1 ∧ ‖(ζ : w.Completion)‖ = 1 ∧
      κ = diagOne s * (κ' : GL (Fin 2) w.Completion) * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ := by
  set δ := ((κ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det with hδ
  have hδ1 : ‖δ‖ = 1 := hκ.1
  have hδ0 : δ ≠ 0 := fun h => by rw [h, norm_zero] at hδ1; exact zero_ne_one hδ1
  rcases sq_eq_one_or_exists_sqrt w δ hδ1 with hsq | ⟨ζ, hζ1, hζζ⟩
  ·
    let s : (w.Completion)ˣ := ⟨δ, δ, hsq, hsq⟩
    have hs : ‖(s : w.Completion)‖ = 1 := hδ1
    have hiso : IsRowIsometry ((diagOne s)⁻¹ * κ) := (isRowIsometry_diagOne s hs).inv.mul hκ
    have hdet : ((((diagOne s)⁻¹ * κ : GL (Fin 2) w.Completion)) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, ← map_inv, det_diagOne, ← hδ]
      show ((s⁻¹ : (w.Completion)ˣ) : w.Completion) * δ = 1
      rw [Units.val_inv_eq_inv_val]
      exact inv_mul_cancel₀ hδ0
    refine ⟨s, 1, ⟨(diagOne s)⁻¹ * κ, (mem_rowIsometrySubgroup₀_iff _).mpr ⟨hdet, hiso⟩⟩, hs, by simp, ?_⟩
    rw [map_one, mul_one]
    show κ = diagOne s * ((diagOne s)⁻¹ * κ)
    rw [mul_inv_cancel_left]
  ·
    have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1
    let u : (w.Completion)ˣ := Units.mk0 ζ hζ0
    have hu : ‖(u : w.Completion)‖ = 1 := hζ1
    have hiso : IsRowIsometry (κ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹) :=
      hκ.mul (isRowIsometry_scalar u hu).inv
    have hdet : (((κ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ : GL (Fin 2) w.Completion)) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, ← map_inv, det_scalar_two, ← hδ, ← hζζ]
      show ζ * ζ * (((u⁻¹ : (w.Completion)ˣ) : w.Completion) * ((u⁻¹ : (w.Completion)ˣ) : w.Completion)) = 1
      rw [Units.val_inv_eq_inv_val]
      show ζ * ζ * (ζ⁻¹ * ζ⁻¹) = 1
      field_simp
    refine ⟨1, u, ⟨κ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹, (mem_rowIsometrySubgroup₀_iff _).mpr ⟨hdet, hiso⟩⟩,
      by simp, hu, ?_⟩
    rw [map_one, one_mul]
    show κ = κ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u
    rw [inv_mul_cancel_right]

p2m_export "KUNIFPlace" "exists_factor"
end KUNIFPlace

end

noncomputable section

namespace KUNIFAdelic

open scoped Classical
open NumberField NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

variable (K : Type) [Field K] [NumberField K]

noncomputable def archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := ((fun w => ((t w : (w.Completion)ˣ) : w.Completion)), 1)
  inv := ((fun w => (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion)), 1)
  val_inv := by
    refine Prod.ext ?_ ?_
    · funext w
      change ((t w : (w.Completion)ˣ) : w.Completion) * (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion) = 1
      exact Units.mul_inv _
    · change (1 : FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul 1
  inv_val := by
    refine Prod.ext ?_ ?_
    · funext w
      change (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion) * ((t w : (w.Completion)ˣ) : w.Completion) = 1
      exact Units.inv_mul _
    · change (1 : FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul 1

theorem archIdele_fst (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    ((archIdele K t : (AdeleRing (𝓞 K) K))).1 w = t w := rfl

theorem archIdele_snd (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    ((archIdele K t : (AdeleRing (𝓞 K) K))).2 = 1 := rfl

theorem gl_ext {g h : AdelicGL2 (𝓞 K) K} (h₁ : glFin (𝓞 K) K g = glFin (𝓞 K) K h)
    (h₂ : ∀ w : InfinitePlace K, archComponent K w (glArch (𝓞 K) K g) = archComponent K w (glArch (𝓞 K) K h)) :
    g = h := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  apply Prod.ext
  · funext w
    exact congrArg (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h₂ w)
  · exact congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h₁

theorem glFin_diagOne_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    glFin (𝓞 K) K (diagOne (archIdele K t)) = 1 := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show (((diagOne (archIdele K t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 =
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem archComponent_diagOne_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    archComponent K w (glArch (𝓞 K) K (diagOne (archIdele K t))) = diagOne (t w) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show (((diagOne (archIdele K t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w =
    ((diagOne (t w) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
  rw [diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_centralScalar_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    glFin (𝓞 K) K (centralScalar (𝓞 K) K (archIdele K t)) = 1 := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show ((Matrix.scalar (Fin 2) ((archIdele K t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) i j).2 =
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
  rw [Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem archComponent_centralScalar_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K (archIdele K t))) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (t w) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show ((Matrix.scalar (Fin 2) ((archIdele K t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) i j).1 w =
    (Matrix.scalar (Fin 2) ((t w : (w.Completion)ˣ) : w.Completion)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_adelicArchGLInclAt (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) :
    glFin (𝓞 K) K (adelicArchGLInclAt K w k) = 1 :=
  glFin_adelicArchGLIncl K _

theorem archComponent_adelicArchGLInclAt_self (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) :
    archComponent K w (glArch (𝓞 K) K (adelicArchGLInclAt K w k)) = k := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_self]

theorem archComponent_adelicArchGLInclAt_of_ne {v w : InfinitePlace K} (hvw : v ≠ w) (k : GL (Fin 2) w.Completion) :
    archComponent K v (glArch (𝓞 K) K (adelicArchGLInclAt K w k)) = 1 := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_of_ne K hvw]

def archProd (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) : AdelicGL2 (𝓞 K) K :=
  (Finset.univ : Finset (InfinitePlace K)).noncommProd (fun w => adelicArchGLInclAt K w (κ w))
    fun _ _ _ _ hvw => commute_adelicArchGLInclAt_of_ne K hvw _ _

theorem glFin_archProd (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) : glFin (𝓞 K) K (archProd K κ) = 1 := by
  rw [archProd, Finset.map_noncommProd]
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 fun w _ => ?_]
  · exact one_pow _
  · exact glFin_adelicArchGLInclAt K w (κ w)

theorem archComponent_archProd (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) (w : InfinitePlace K) :
    archComponent K w (glArch (𝓞 K) K (archProd K κ)) = κ w := by
  let A : AdelicGL2 (𝓞 K) K →* GL (Fin 2) w.Completion := (archComponent K w).comp (glArch (𝓞 K) K)
  show A (archProd K κ) = κ w
  rw [archProd, Finset.map_noncommProd]
  rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ w)]
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 fun v hv => ?_]
  · rw [one_pow, mul_one]
    exact archComponent_adelicArchGLInclAt_self K w (κ w)
  · exact archComponent_adelicArchGLInclAt_of_ne K (Finset.ne_of_mem_erase hv).symm (κ v)

theorem archProd_induction (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) (p : AdelicGL2 (𝓞 K) K → Prop)
    (hone : p 1) (hmul : ∀ a b, p a → p b → p (a * b)) (hbase : ∀ w, p (adelicArchGLInclAt K w (κ w))) :
    p (archProd K κ) :=
  Finset.noncommProd_induction _ _ _ p hmul hone fun w _ => hbase w

theorem adelicArchGLInclAt_mem_adelicMaximalCompact (w : InfinitePlace K) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) : adelicArchGLInclAt K w k ∈ adelicMaximalCompact K := by
  refine mem_adelicMaximalCompact_iff.mpr ⟨?_, fun v => ?_⟩
  · rw [glFin_adelicArchGLInclAt]; exact Subgroup.one_mem _
  · by_cases hvw : v = w
    · subst hvw; rw [archComponent_adelicArchGLInclAt_self]; exact hk
    · rw [archComponent_adelicArchGLInclAt_of_ne K hvw]; exact isRowIsometry_one

theorem archProd_mem_adelicMaximalCompact (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion)
    (hκ : ∀ w, IsRowIsometry (κ w)) : archProd K κ ∈ adelicMaximalCompact K :=
  archProd_induction K κ (fun g => g ∈ adelicMaximalCompact K) (Subgroup.one_mem _)
    (fun _ _ ha hb => Subgroup.mul_mem _ ha hb) fun w => adelicArchGLInclAt_mem_adelicMaximalCompact K w _ (hκ w)

theorem ideleNorm_archIdele_eq_one (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (ht : ∀ w, ‖((t w : (w.Completion)ˣ) : w.Completion)‖ = 1) :
    NumberField.TateGlobal.ideleNorm K (archIdele K t) = 1 := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _ (archIdele_snd K t)]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [archIdele_fst, ht w, one_pow]

theorem mul_centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    g * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * g := by
  apply Units.ext
  show (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) =
    Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) * g
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 K) K) (fun _ => Commute.all _ _) _).symm.eq

private theorem _root_.KUNIFAdelic.exists_factor (k : AdelicGL2 (𝓞 K) K) (hk1 : glFin (𝓞 K) K k = 1)
    (hk2 : ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) :
    ∃ (s ζ : ∀ w : InfinitePlace K, (w.Completion)ˣ) (κ' : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion),
      (∀ w, ‖((s w : (w.Completion)ˣ) : w.Completion)‖ = 1) ∧ (∀ w, ‖((ζ w : (w.Completion)ˣ) : w.Completion)‖ = 1) ∧
      k = diagOne (archIdele K s) * archProd K (fun w => (κ' w : GL (Fin 2) w.Completion)) *
        centralScalar (𝓞 K) K (archIdele K ζ) := by
  choose s ζ κ' hs hζ hfac using fun w => KUNIFPlace.exists_factor w _ (hk2 w)
  refine ⟨s, ζ, κ', hs, hζ, gl_ext K ?_ fun w => ?_⟩
  · rw [hk1, map_mul, map_mul, glFin_diagOne_archIdele, glFin_archProd, glFin_centralScalar_archIdele, one_mul, one_mul]
  · rw [map_mul, map_mul, map_mul, map_mul, archComponent_diagOne_archIdele, archComponent_archProd,
      archComponent_centralScalar_archIdele]
    exact hfac w

p2m_export "KUNIFAdelic" "exists_factor"
end KUNIFAdelic

end

noncomputable section

namespace KUNIFCut

open scoped Classical
open NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent NumberField.InfinitePlace IsDedekindDomain NumberField.AdelicLevel MeasureTheory

variable (K : Type) [Field K] [NumberField K]

theorem continuous_of_mem_cuspKFiniteSubmodule {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : φ ∈ cuspKFiniteSubmodule K pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ h
  · rintro φ ⟨_, hc, _⟩; exact hc
  · exact continuous_const
  · intro _ _ _ _ hu hv; exact hu.add hv
  · intro c _ _ hu; exact hu.const_smul c

theorem central_of_mem_cuspKFiniteSubmodule {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : φ ∈ cuspKFiniteSubmodule K pins ξ) (z : pins.Z) (g : AdelicGL2 (𝓞 K) K) :
    φ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g := by
  revert g
  refine Submodule.span_induction (p := fun φ _ => ∀ g, φ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) =
    ((ξ z : ℂˣ) : ℂ) * φ g) ?_ ?_ ?_ ?_ h
  · rintro φ ⟨hsat, -, -⟩ g
    letI := pins.mS
    have h1 : IsAutomorphicFnAt K pins ξ (rightTranslate K 1 φ) := (hsat 1).1.1
    have h2 := ((lsXiMemberAt_iff (𝓞 K) K pins.μ pins.Z ξ pins.D (rightTranslate K 1 φ)).mp h1).1.central_transform z g
    simpa [rightTranslate] using h2
  · intro g; simp
  · intro u v _ _ hu hv g
    simp only [Pi.add_apply, hu g, hv g, mul_add]
  · intro c u _ hu g
    simp only [Pi.smul_apply, hu g, smul_eq_mul]
    ring

theorem exists_finiteDimensional_of_mem_archCutSubmodule (tys : ArchTypeFamily K) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ archCutSubmodule K tys) (w : InfinitePlace K) :
    ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W := by
  have hw := (mem_archCutSubmodule_iff K tys φ).mp hφ w
  refine Submodule.iSup_induction _
    (motive := fun φ => ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W) hw ?_ ?_ ?_
  · intro i φ hφi
    refine Submodule.span_induction (p := fun φ _ => ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ),
      FiniteDimensional ℂ W ∧ ∀ k : rowIsometrySubgroup₀ w.Completion,
        rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W) ?_ ?_ ?_ ?_ hφi
    · rintro _ ⟨T, hT, v, rfl⟩
      refine ⟨LinearMap.range T, inferInstance, fun k => ?_⟩
      have : rightTranslate K (rowIsometryInclAt₀ K w k) (T v) = T ((tys.rep w i).ρ k v) := by
        funext x; exact (hT k v x).symm
      rw [this]; exact LinearMap.mem_range_self T _
    · exact ⟨⊥, inferInstance, fun k => by rw [rightTranslate_zero]; exact Submodule.zero_mem _⟩
    · rintro φ ψ - - ⟨W₁, hW₁, h₁⟩ ⟨W₂, hW₂, h₂⟩
      haveI := hW₁; haveI := hW₂
      exact ⟨W₁ ⊔ W₂, inferInstance, fun k => by
        rw [rightTranslate_add]; exact Submodule.add_mem_sup (h₁ k) (h₂ k)⟩
    · rintro c φ - ⟨W, hW, h⟩
      exact ⟨W, hW, fun k => by rw [rightTranslate_smul]; exact W.smul_mem c (h k)⟩
  · exact ⟨⊥, inferInstance, fun k => by rw [rightTranslate_zero]; exact Submodule.zero_mem _⟩
  · rintro φ ψ ⟨W₁, hW₁, h₁⟩ ⟨W₂, hW₂, h₂⟩
    haveI := hW₁; haveI := hW₂
    exact ⟨W₁ ⊔ W₂, inferInstance, fun k => by
      rw [rightTranslate_add]; exact Submodule.add_mem_sup (h₁ k) (h₂ k)⟩

variable {K}

theorem map_map_rightRegular (a b : AdelicGL2 (𝓞 K) K) (p : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) :
    (p.map (rightRegular K a)).map (rightRegular K b) = p.map (rightRegular K (b * a)) := by
  rw [← Submodule.map_comp, map_mul, Module.End.mul_eq_comp]

theorem exists_fd_stable (C : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hC_stab : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ C,
      rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ C)
    (hC_fd : ∀ φ ∈ C, ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W)
    {x : AdelicGL2 (𝓞 K) K → ℂ} (hx : x ∈ C) :
    ∃ E : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ E ∧ E ≤ C ∧ x ∈ E ∧
      ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ E,
        rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ E := by
  suffices H : ∀ P : Finset (InfinitePlace K), ∃ E : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ),
      FiniteDimensional ℂ E ∧ E ≤ C ∧ x ∈ E ∧
      ∀ w ∈ P, ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ E, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ E by
    obtain ⟨E, h1, h2, h3, h4⟩ := H Finset.univ
    exact ⟨E, h1, h2, h3, fun w k φ hφ => h4 w (Finset.mem_univ w) k φ hφ⟩
  intro P
  induction P using Finset.induction_on with
  | empty =>
    exact ⟨ℂ ∙ x, inferInstance, (Submodule.span_singleton_le_iff_mem _ _).mpr hx, Submodule.mem_span_singleton_self x,
      fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert w P hwP ih =>
    obtain ⟨E, hEfd, hEC, hxE, hEstab⟩ := ih
    haveI := hEfd
    let R : rowIsometrySubgroup₀ w.Completion → (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun k => rightRegular K (rowIsometryInclAt₀ K w k)
    let E' : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := ⨆ k, E.map (R k)
    have hEE' : E ≤ E' := by
      have h1 : E.map (R 1) = E := by
        simp only [R, map_one, Module.End.one_eq_id, Submodule.map_id]
      calc E = E.map (R 1) := h1.symm
        _ ≤ E' := le_iSup (fun k => E.map (R k)) 1

    obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional E).mpr hEfd
    have hSE : ∀ s ∈ S, (s : AdelicGL2 (𝓞 K) K → ℂ) ∈ E := fun s hs => hS ▸ Submodule.subset_span hs
    choose W hWfd hW using fun s : S => hC_fd s (hEC (hSE s s.2)) w
    haveI : ∀ s : S, FiniteDimensional ℂ (W s) := hWfd
    have hE'le : E' ≤ ⨆ s : S, W s := by
      refine iSup_le fun k => ?_
      rw [← hS, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨s, hs⟩ (hW ⟨s, hs⟩ k)
    refine ⟨E', Submodule.finiteDimensional_of_le hE'le, ?_, hEE' hxE, ?_⟩
    · exact iSup_le fun k => Submodule.map_le_iff_le_comap.mpr fun φ hφ => hC_stab w k φ (hEC hφ)
    · intro v hv k φ hφ
      rcases Finset.mem_insert.mp hv with rfl | hvP
      ·
        have hle : E'.map (R k) ≤ E' := by
          rw [Submodule.map_iSup]
          refine iSup_le fun k' => ?_
          rw [show (E.map (R k')).map (R k) = E.map (R (k * k')) by
            simp only [R, map_map_rightRegular, ← map_mul]]
          exact le_iSup (fun k => E.map (R k)) (k * k')
        exact hle (Submodule.mem_map_of_mem hφ)
      ·
        have hvw : v ≠ w := fun h => hwP (h ▸ hvP)
        have hle : E'.map (rightRegular K (rowIsometryInclAt₀ K v k)) ≤ E' := by
          rw [Submodule.map_iSup]
          refine iSup_le fun k' => ?_
          have hcomm : rowIsometryInclAt₀ K v k * rowIsometryInclAt₀ K w k' =
              rowIsometryInclAt₀ K w k' * rowIsometryInclAt₀ K v k := by
            rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply]
            exact (commute_adelicArchGLInclAt_of_ne K hvw _ _).eq
          rw [show (E.map (R k')).map (rightRegular K (rowIsometryInclAt₀ K v k)) =
              (E.map (rightRegular K (rowIsometryInclAt₀ K v k))).map (R k') by
            simp only [R, map_map_rightRegular, hcomm]]
          refine (Submodule.map_mono ?_).trans (le_iSup (fun k => E.map (R k)) k')
          exact Submodule.map_le_iff_le_comap.mpr fun ψ hψ => hEstab v hvP k ψ hψ
        exact hle (Submodule.mem_map_of_mem hφ)

variable (K)

theorem whittakerCoefficient_mul (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (g k : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * k) = whittakerCoefficient K pins ψ (rightTranslate K k φ) α g := by
  simp only [whittakerCoefficient, rightTranslate, mul_assoc]

theorem exists_bound {x : AdelicGL2 (𝓞 K) K → ℂ} (hx : Continuous x) (g : AdelicGL2 (𝓞 K) K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ adelicMaximalCompact K, ‖x (g * k)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_adelicMaximalCompact K).exists_bound_of_continuousOn
    (f := fun k => x (g * k)) ((hx.comp (continuous_const.mul continuous_id)).continuousOn)
  exact ⟨max B 0, le_max_right _ _, fun k hk => (hB k hk).trans (le_max_left _ _)⟩

end KUNIFCut

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

set_option linter.unusedVariables false in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀) :
    ∃ (m : ℕ) (ys : Fin m → (AdelicGL2 (𝓞 K) K → ℂ)) (M : ℝ),
      (∀ i, ys i ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) ∧
      ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        ∃ (cs : Fin m → ℂ) (ε : (AdeleRing (𝓞 K) K)ˣ),
          ((ε : AdeleRing (𝓞 K) K)).2 = 1 ∧ NumberField.TateGlobal.ideleNorm K ε = 1 ∧
          (∀ i, ‖cs i‖ ≤ M) ∧
          ∀ g : AdelicGL2 (𝓞 K) K,
            whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (g * k) =
              ∑ i, cs i * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys i) 1
              (g * diagOne ε) := by
  classical
  set C : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys with hC

  have hC_cont : ∀ φ ∈ C, Continuous φ := fun φ hφ =>
    KUNIFCut.continuous_of_mem_cuspKFiniteSubmodule K (hV.1.le hφ.1.1)
  have hU : ∀ u' ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, AdelicLevel.glArch (𝓞 K) K u' = 1 :=
    fun u' hu' => hu'.2
  have hC_stab : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ C,
      rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ C := by
    intro w k φ hφ
    refine ⟨⟨hV.1.rightTranslate_arch_mem w k φ hφ.1.1, ?_⟩,
      rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule K tys hφ.2 w k⟩
    intro g u' hu'
    show φ (g * u' * rowIsometryInclAt₀ K w k) = φ (g * rowIsometryInclAt₀ K w k)
    have hcomm : u' * rowIsometryInclAt₀ K w k = rowIsometryInclAt₀ K w k * u' := by
      rw [rowIsometryInclAt₀_apply]
      refine KUNIFAdelic.gl_ext K ?_ fun v => ?_
      · rw [map_mul, map_mul, KUNIFAdelic.glFin_adelicArchGLInclAt, mul_one, one_mul]
      · rw [map_mul, map_mul, map_mul, map_mul, hU u' hu', map_one, mul_one, one_mul]
    rw [mul_assoc, hcomm, ← mul_assoc]
    exact hφ.1.2 _ u' hu'
  have hC_fd : ∀ φ ∈ C, ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ),
      FiniteDimensional ℂ W ∧ ∀ k : rowIsometrySubgroup₀ w.Completion,
        rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W := fun φ hφ w =>
    KUNIFCut.exists_finiteDimensional_of_mem_archCutSubmodule K tys hφ.2 w

  obtain ⟨E, hEfd, hEC, hxE, hEstab⟩ := KUNIFCut.exists_fd_stable C hC_stab hC_fd hx
  haveI := hEfd

  obtain ⟨S, b, hb, hcoord⟩ := EvalCoords.exists_eval_coords E
  let eS : S ≃ Fin S.card := S.equivFin
  let pt : Fin S.card → AdelicGL2 (𝓞 K) K := fun i => ((eS.symm i : S) : AdelicGL2 (𝓞 K) K)
  let ys : Fin S.card → AdelicGL2 (𝓞 K) K → ℂ := fun i => b (pt i)

  have hxcont : Continuous x := hC_cont x hx
  choose B hB0 hB using fun g : AdelicGL2 (𝓞 K) K => KUNIFCut.exists_bound K hxcont g
  refine ⟨S.card, ys, ∑ i, B (pt i), fun i => hEC (hb _), ?_⟩
  intro k hk1 hk2

  obtain ⟨s, ζ, κ', hs, hζ, hfac⟩ := KUNIFAdelic.exists_factor K k hk1 hk2
  set ε := KUNIFAdelic.archIdele K s with hε
  set z := KUNIFAdelic.archIdele K ζ with hz
  set k₁ := KUNIFAdelic.archProd K (fun w => (κ' w : GL (Fin 2) w.Completion)) with hk₁
  have hk₁K : k₁ ∈ adelicMaximalCompact K :=
    KUNIFAdelic.archProd_mem_adelicMaximalCompact K _ fun w => ((mem_rowIsometrySubgroup₀_iff _).mp (κ' w).2).2
  have hk₁E : ∀ φ ∈ E, rightTranslate K k₁ φ ∈ E := by
    refine KUNIFAdelic.archProd_induction K _ (fun h => ∀ φ ∈ E, rightTranslate K h φ ∈ E) ?_ ?_ ?_
    · intro φ hφ
      have : rightTranslate K 1 φ = φ := by funext y; simp [rightTranslate]
      rw [this]; exact hφ
    · intro a a' ha ha' φ hφ
      rw [← rightTranslate_rightTranslate]
      exact ha _ (ha' φ hφ)
    · intro w φ hφ
      exact hEstab w (κ' w) φ hφ

  have hξz : ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1 := by
    rw [hξ, KUNIFAdelic.ideleNorm_archIdele_eq_one K ζ hζ, Real.one_rpow]

  let cs : Fin S.card → ℂ := fun i => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x (pt i * k₁)
  refine ⟨cs, ε, KUNIFAdelic.archIdele_snd K s, KUNIFAdelic.ideleNorm_archIdele_eq_one K s hs, fun i => ?_, fun g => ?_⟩
  · calc ‖cs i‖ = ‖x (pt i * k₁)‖ := by
          show ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x (pt i * k₁)‖ = _
          rw [norm_mul, hξz, one_mul]
      _ ≤ B (pt i) := hB _ k₁ hk₁K
      _ ≤ ∑ j, B (pt j) := Finset.single_le_sum (fun j _ => hB0 _) (Finset.mem_univ i)
  ·
    have hcentral : ∀ y, x (centralScalar (𝓞 K) K z * y) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x y :=
      fun y => KUNIFCut.central_of_mem_cuspKFiniteSubmodule K (hV.1.le hx.1.1) ⟨z, Subgroup.mem_top z⟩ y
    have hpt : ∀ y, x (y * k) = ∑ i, cs i * ys i (y * diagOne ε) := by
      intro y
      have e1 : x (y * k) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x (y * diagOne ε * k₁) := by
        rw [hfac, ← mul_assoc, ← mul_assoc, KUNIFAdelic.mul_centralScalar_comm, hcentral]
      have e2 : x (y * diagOne ε * k₁) = ∑ g' ∈ S, x (g' * k₁) * b g' (y * diagOne ε) := by
        have h := congrFun (hcoord _ (hk₁E x hxE)) (y * diagOne ε)
        simpa only [rightTranslate, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
      rw [e1, e2, Finset.mul_sum, ← Finset.sum_coe_sort S, ← eS.symm.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [cs, ys, pt]
      ring

    have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
      (NumberField.StandardAddChar.adelicTraceData K).continuous_psiK
    have hcontys : ∀ i, Continuous (rightTranslate K (diagOne ε) (ys i)) := fun i =>
      continuous_rightTranslate K (hC_cont _ (hEC (hb _))) _
    have hfun : rightTranslate K k x = fun y => ∑ i, cs i * rightTranslate K (diagOne ε) (ys i) y := by
      funext y
      exact hpt y
    rw [KUNIFCut.whittakerCoefficient_mul, hfun]
    have hW := AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (NumberField.StandardAddChar.stdAddChar K) hψ S.card (fun i => rightTranslate K (diagOne ε) (ys i)) hcontys cs 1 g
    rw [hW]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [KUNIFCut.whittakerCoefficient_mul]

end S_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent (solution)
