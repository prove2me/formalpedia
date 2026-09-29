-- Prove2me | solution 1 for AutomorphicForm.foldr_archDeriv_comm_of_ne_place
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9efb202d-3fdf-5ec2-bd10-58dba845a8c1

import Mathlib
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_foldr_archDeriv_comm_of_ne_place

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm
open IsDedekindDomain
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix Complex
open scoped Topology

noncomputable section

namespace KcCommNePlace

variable {K : Type} [Field K] [NumberField K]

abbrev Letter (K : Type) [Field K] [NumberField K] : Type :=
  (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)

def place : Letter K → InfinitePlace K := Sum.elim (fun e => e.1) (fun e => e.1)

def D (δ : Letter K) (ψ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  Sum.elim (fun d => archDerivAt d.2.1 d.2.2 ψ) (fun d => archDerivAtComplex d.2.1 d.2.2 ψ) δ

def fl : Letter K → ℝ → AdelicGL2 (𝓞 K) K
  | Sum.inl e => fun t => archFlowAt e.2.1 e.2.2 t
  | Sum.inr e => fun t => archFlowAtComplex e.2.1 e.2.2 t

def mat : (δ : Letter K) → ℝ → GL (Fin 2) (place δ).Completion
  | Sum.inl e => fun t => glEquivOfRingEquiv (ringEquivRealOfIsReal e.2.1).symm (archFlowMatrix e.2.2 t)
  | Sum.inr e => fun t => glEquivOfRingEquiv (ringEquivComplexOfIsComplex e.2.1).symm (archFlowMatrixComplex e.2.2 t)

theorem D_apply (δ : Letter K) (ψ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) :
    D δ ψ g = deriv (fun t : ℝ => ψ (g * fl δ t)) 0 := by
  rcases δ with e | e <;> rfl

theorem fl_zero (δ : Letter K) : fl δ 0 = 1 := by
  rcases δ with e | e
  · exact archFlowAt_zero e.2.1 e.2.2
  · exact archFlowAtComplex_zero e.2.1 e.2.2

theorem fl_add (δ : Letter K) (s t : ℝ) : fl δ (s + t) = fl δ s * fl δ t := by
  rcases δ with e | e
  · exact archFlowAt_add e.2.1 e.2.2 s t
  · exact archFlowAtComplex_add e.2.1 e.2.2 s t

theorem fl_eq_incl (δ : Letter K) (t : ℝ) : fl δ t = adelicArchGLInclAt K (place δ) (mat δ t) := by
  rcases δ with e | e <;> rfl

theorem commute_fl {δ δ' : Letter K} (h : place δ ≠ place δ') (s t : ℝ) : Commute (fl δ s) (fl δ' t) := by
  rw [fl_eq_incl, fl_eq_incl]
  exact AutomorphicForm.commute_adelicArchGLInclAt_of_ne K h _ _

theorem continuous_archGLIncl (w : InfinitePlace K) : Continuous (archGLIncl K w) := by
  have hval : ∀ {f : GL (Fin 2) w.Completion → Matrix (Fin 2) (Fin 2) w.Completion}, Continuous f →
      Continuous fun k => archMatrixUpdate K w (f k) := by
    intro f hf
    refine continuous_matrix fun i j => continuous_pi fun v => ?_
    by_cases hv : v = w
    · subst hv
      simp only [archMatrixUpdate_apply_self]
      exact hf.matrix_elem i j
    · simp only [archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]
      exact continuous_const
  rw [Units.continuous_iff]
  exact ⟨hval Units.continuous_val, hval Units.continuous_coe_inv⟩

theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl K) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      ((adelicArchGLIncl K g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun g : GL (Fin 2) (InfiniteAdeleRing K) =>
      (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) :
          InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem continuous_adelicArchGLInclAt (w : InfinitePlace K) : Continuous (adelicArchGLInclAt K w) := by
  show Continuous fun k => adelicArchGLIncl K (archGLIncl K w k)
  exact continuous_adelicArchGLIncl.comp (continuous_archGLIncl w)

theorem continuous_glEquivOfRingEquiv {L : Type*} [NormedField L] (e : L ≃+* ℝ) (he : Continuous e.symm) :
    Continuous (glEquivOfRingEquiv e.symm) :=
  Continuous.units_map _ (continuous_id.matrix_map he)

theorem continuous_glEquivOfRingEquiv' {L : Type*} [NormedField L] (e : L ≃+* ℂ) (he : Continuous e.symm) :
    Continuous (glEquivOfRingEquiv e.symm) :=
  Continuous.units_map _ (continuous_id.matrix_map he)

theorem differentiable_archFlowMatrix_coe (d : ArchDir) :
    Differentiable ℝ (fun t : ℝ => ((archFlowMatrix d t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have h1 : Differentiable ℝ (fun t : ℝ => Real.exp t) := Real.differentiable_exp
  have h2 : Differentiable ℝ (fun t : ℝ => Real.exp (-t)) := Real.differentiable_exp.comp differentiable_neg
  refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp only [archFlowMatrix, splitTorusGL2_coe, unipotentGL2_coe, lowerUnipotentGL2_coe,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first
      | exact differentiable_const _
      | exact differentiable_id
      | exact h1
      | exact h2

theorem differentiable_archFlowMatrixComplex_coe (d : ArchDirComplex) :
    Differentiable ℝ (fun t : ℝ => ((archFlowMatrixComplex d t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hoR : Differentiable ℝ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.differentiable
  have hoI : Differentiable ℝ (fun t : ℝ => (t : ℂ) * I) := hoR.mul_const I
  have h1 : Differentiable ℝ (fun t : ℝ => Complex.exp (t : ℂ)) := Complex.differentiable_exp.comp hoR
  have h2 : Differentiable ℝ (fun t : ℝ => Complex.exp (-(t : ℂ))) := Complex.differentiable_exp.comp hoR.neg
  have h3 : Differentiable ℝ (fun t : ℝ => Complex.exp ((t : ℂ) * I)) := Complex.differentiable_exp.comp hoI
  have h4 : Differentiable ℝ (fun t : ℝ => Complex.exp (-((t : ℂ) * I))) :=
    Complex.differentiable_exp.comp hoI.neg
  refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp only [archFlowMatrixComplex, splitTorusGL2Complex, unipotentGL2_coe, lowerUnipotentGL2_coe,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first
      | exact differentiable_const _
      | exact hoR
      | exact hoI
      | exact h1
      | exact h2
      | exact h3
      | exact h4

theorem archFlowMatrix_inv (d : ArchDir) (t : ℝ) : (archFlowMatrix d t)⁻¹ = archFlowMatrix d (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← archFlowMatrix_add, add_neg_cancel, archFlowMatrix_zero])

theorem archFlowMatrixComplex_inv (d : ArchDirComplex) (t : ℝ) :
    (archFlowMatrixComplex d t)⁻¹ = archFlowMatrixComplex d (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← archFlowMatrixComplex_add, add_neg_cancel, archFlowMatrixComplex_zero])

theorem continuous_archFlowMatrix (d : ArchDir) : Continuous (archFlowMatrix d) := by
  rw [Units.continuous_iff]
  refine ⟨(differentiable_archFlowMatrix_coe d).continuous, ?_⟩
  simp only [archFlowMatrix_inv]
  exact (differentiable_archFlowMatrix_coe d).continuous.comp continuous_neg

theorem continuous_archFlowMatrixComplex (d : ArchDirComplex) : Continuous (archFlowMatrixComplex d) := by
  rw [Units.continuous_iff]
  refine ⟨(differentiable_archFlowMatrixComplex_coe d).continuous, ?_⟩
  simp only [archFlowMatrixComplex_inv]
  exact (differentiable_archFlowMatrixComplex_coe d).continuous.comp continuous_neg

theorem continuous_mat (δ : Letter K) : Continuous (mat δ) := by
  rcases δ with e | e
  · exact (continuous_glEquivOfRingEquiv (ringEquivRealOfIsReal e.2.1)
      (isometryEquivRealOfIsReal e.2.1).symm.continuous).comp (continuous_archFlowMatrix e.2.2)
  · exact (continuous_glEquivOfRingEquiv' (ringEquivComplexOfIsComplex e.2.1)
      (isometryEquivComplexOfIsComplex e.2.1).symm.continuous).comp (continuous_archFlowMatrixComplex e.2.2)

theorem continuous_fl (δ : Letter K) : Continuous (fl δ) := by
  have : fl δ = fun t => adelicArchGLInclAt K (place δ) (mat δ t) := funext (fl_eq_incl δ)
  rw [this]
  exact (continuous_adelicArchGLInclAt (place δ)).comp (continuous_mat δ)

def Sm : Letter K → (AdelicGL2 (𝓞 K) K → ℂ) → Prop
  | Sum.inl e => fun ψ => IsArchSmoothAt e.2.1 ψ
  | Sum.inr e => fun ψ => IsArchSmoothAtComplex e.2.1 ψ

def flowEntriesC (d : ArchDirComplex) (t : ℝ) : Fin 2 → Fin 2 → ℂ :=
  fun i j => (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) i j

theorem det_of_flowEntriesC_ne_zero (d : ArchDirComplex) (t : ℝ) :
    (Matrix.of (flowEntriesC d t)).det ≠ 0 := by
  have : Matrix.of (flowEntriesC d t) = (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; rfl
  rw [this]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (archFlowMatrixComplex d t).isUnit).ne_zero

theorem archComplexLiftAt_flowEntriesC {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex) (t : ℝ) :
    archComplexLiftAt hw (flowEntriesC d t) = archFlowAtComplex hw d t := by
  rw [archComplexLiftAt_of_det_ne_zero hw (det_of_flowEntriesC_ne_zero d t), archFlowAtComplex]
  congr 1
  ext i j
  rfl

theorem differentiableAt_flowC {w : InfinitePlace K} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex) (g : AdelicGL2 (𝓞 K) K) (t₀ : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) t₀ := by
  have hfun : (fun t : ℝ => φ (g * archFlowAtComplex hw d t)) =
      (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e)) ∘ flowEntriesC d := by
    funext t
    simp only [Function.comp_apply, archComplexLiftAt_flowEntriesC]
  rw [hfun]
  have hmem : flowEntriesC d t₀ ∈ {e : Fin 2 → Fin 2 → ℂ | (Matrix.of e).det ≠ 0} :=
    det_of_flowEntriesC_ne_zero d t₀
  have hdiff : DifferentiableAt ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
      (flowEntriesC d t₀) :=
    ((hφ g).contDiffAt (isOpen_setOf_det_ne_zero_complex.mem_nhds hmem)).differentiableAt (by simp)
  exact hdiff.comp t₀ ((differentiable_archFlowMatrixComplex_coe d) t₀)

theorem Sm.differentiableAt_flow {δ : Letter K} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : Sm δ ψ)
    (g : AdelicGL2 (𝓞 K) K) : DifferentiableAt ℝ (fun t : ℝ => ψ (g * fl δ t)) 0 := by
  rcases δ with e | e
  · exact IsArchSmoothAt.differentiableAt_flow h e.2.2 g
  · exact differentiableAt_flowC h e.2.2 g 0

theorem hasDerivAt_flow {δ : Letter K} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : Sm δ ψ)
    (g : AdelicGL2 (𝓞 K) K) (s : ℝ) :
    HasDerivAt (fun s' : ℝ => ψ (g * fl δ s')) (D δ ψ (g * fl δ s)) s := by
  have h0 : HasDerivAt (fun τ : ℝ => ψ (g * fl δ s * fl δ τ)) (D δ ψ (g * fl δ s)) 0 := by
    rw [D_apply]
    exact (h.differentiableAt_flow (g * fl δ s)).hasDerivAt
  have hfun : (fun s' : ℝ => ψ (g * fl δ s')) = fun s' => ψ (g * fl δ s * fl δ (s' - s)) := by
    funext s'
    rw [mul_assoc, ← fl_add, add_sub_cancel]
  rw [hfun]
  have h0' : HasDerivAt (fun τ : ℝ => ψ (g * fl δ s * fl δ τ)) (D δ ψ (g * fl δ s)) (s - s) := by
    rw [sub_self]; exact h0
  exact h0'.comp_sub_const s s

section Core

open ContinuousLinearMap

variable (φ : AdelicGL2 (𝓞 K) K → ℂ) (X Y : Letter K)

theorem D_comm_of_place_ne (hne : place X ≠ place Y)
    (hX : Sm X φ) (hY : Sm Y φ)
    (hXX : Sm X (D X φ)) (hYX : Sm Y (D X φ)) (hXY : Sm X (D Y φ)) (hYY : Sm Y (D Y φ))
    (cX : Continuous (D X φ)) (cY : Continuous (D Y φ))
    (cXX : Continuous (D X (D X φ))) (cYX : Continuous (D Y (D X φ)))
    (cXY : Continuous (D X (D Y φ))) (cYY : Continuous (D Y (D Y φ))) :
    D X (D Y φ) = D Y (D X φ) := by
  funext g

  set base : ℝ × ℝ → AdelicGL2 (𝓞 K) K := fun p => g * fl X p.1 * fl Y p.2 with hbase
  have hbase_cont : Continuous base :=
    (continuous_const.mul ((continuous_fl X).comp continuous_fst)).mul ((continuous_fl Y).comp continuous_snd)
  have hswap : ∀ s t : ℝ, g * fl X s * fl Y t = g * fl Y t * fl X s := by
    intro s t
    rw [mul_assoc, (commute_fl hne s t).eq, ← mul_assoc]
  set G : ℝ → ℝ → ℂ := fun s t => φ (base (s, t)) with hG
  set G₁ : ℝ → ℝ → ℂ := fun s t => D X φ (base (s, t)) with hG₁
  set G₂ : ℝ → ℝ → ℂ := fun s t => D Y φ (base (s, t)) with hG₂
  set G₁₁ : ℝ → ℝ → ℂ := fun s t => D X (D X φ) (base (s, t)) with hG₁₁
  set G₂₁ : ℝ → ℝ → ℂ := fun s t => D Y (D X φ) (base (s, t)) with hG₂₁
  set G₁₂ : ℝ → ℝ → ℂ := fun s t => D X (D Y φ) (base (s, t)) with hG₁₂
  set G₂₂ : ℝ → ℝ → ℂ := fun s t => D Y (D Y φ) (base (s, t)) with hG₂₂

  have dS : ∀ (ψ : AdelicGL2 (𝓞 K) K → ℂ), Sm X ψ → ∀ s t : ℝ,
      HasDerivAt (fun s' => ψ (base (s', t))) (D X ψ (base (s, t))) s := by
    intro ψ hψ s t
    have hfun : (fun s' : ℝ => ψ (base (s', t))) = fun s' => ψ (g * fl Y t * fl X s') := by
      funext s'; simp only [hbase, hswap]
    rw [hfun]
    have := hasDerivAt_flow hψ (g * fl Y t) s
    simpa only [hbase, hswap] using this

  have dT : ∀ (ψ : AdelicGL2 (𝓞 K) K → ℂ), Sm Y ψ → ∀ s t : ℝ,
      HasDerivAt (fun t' => ψ (base (s, t'))) (D Y ψ (base (s, t))) t := by
    intro ψ hψ s t
    exact hasDerivAt_flow hψ (g * fl X s) t

  have cG₁ : Continuous ↿G₁ := cX.comp hbase_cont
  have cG₂ : Continuous ↿G₂ := cY.comp hbase_cont
  have cG₁₁ : Continuous ↿G₁₁ := cXX.comp hbase_cont
  have cG₂₁ : Continuous ↿G₂₁ := cYX.comp hbase_cont
  have cG₁₂ : Continuous ↿G₁₂ := cXY.comp hbase_cont
  have cG₂₂ : Continuous ↿G₂₂ := cYY.comp hbase_cont

  have key : ∀ (F F₁ F₂ : ℝ → ℝ → ℂ),
      (∀ s t, HasDerivAt (fun s' => F s' t) (F₁ s t) s) → (∀ s t, HasDerivAt (fun t' => F s t') (F₂ s t) t) →
      Continuous ↿F₁ → Continuous ↿F₂ → ∀ p : ℝ × ℝ,
        HasFDerivAt ↿F (smulRightL ℝ (ℝ × ℝ) ℂ (fst ℝ ℝ ℝ) (F₁ p.1 p.2) +
          smulRightL ℝ (ℝ × ℝ) ℂ (snd ℝ ℝ ℝ) (F₂ p.1 p.2)) p := by
    intro F F₁ F₂ h₁ h₂ c₁ c₂ p
    have hst := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := p) (f := F)
      (f₁ := fun s t => toSpanSingleton ℝ (F₁ s t)) (f₂ := fun s t => toSpanSingleton ℝ (F₂ s t))
      (Filter.Eventually.of_forall fun v => (h₁ v.1 v.2).hasFDerivAt)
      (Filter.Eventually.of_forall fun v => (h₂ v.1 v.2).hasFDerivAt)
      (((toSpanSingletonLIE ℝ ℂ).continuous.comp c₁).continuousAt)
      (((toSpanSingletonLIE ℝ ℂ).continuous.comp c₂).continuousAt)
    refine hst.hasFDerivAt.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun q => ?_
    obtain ⟨x, y⟩ := q
    simp [Function.HasUncurry.uncurry, ContinuousLinearMap.toSpanSingleton_apply]

  have hG' : ∀ p : ℝ × ℝ, HasFDerivAt ↿G
      (smulRightL ℝ (ℝ × ℝ) ℂ (fst ℝ ℝ ℝ) (↿G₁ p) + smulRightL ℝ (ℝ × ℝ) ℂ (snd ℝ ℝ ℝ) (↿G₂ p)) p :=
    key G G₁ G₂ (dS φ hX) (dT φ hY) cG₁ cG₂

  have hG₁' : HasFDerivAt ↿G₁
      (smulRightL ℝ (ℝ × ℝ) ℂ (fst ℝ ℝ ℝ) (G₁₁ 0 0) + smulRightL ℝ (ℝ × ℝ) ℂ (snd ℝ ℝ ℝ) (G₂₁ 0 0)) (0, 0) :=
    key G₁ G₁₁ G₂₁ (dS (D X φ) hXX) (dT (D X φ) hYX) cG₁₁ cG₂₁ (0, 0)
  have hG₂' : HasFDerivAt ↿G₂
      (smulRightL ℝ (ℝ × ℝ) ℂ (fst ℝ ℝ ℝ) (G₁₂ 0 0) + smulRightL ℝ (ℝ × ℝ) ℂ (snd ℝ ℝ ℝ) (G₂₂ 0 0)) (0, 0) :=
    key G₂ G₁₂ G₂₂ (dS (D Y φ) hXY) (dT (D Y φ) hYY) cG₁₂ cG₂₂ (0, 0)

  set A₁ : ℝ × ℝ →L[ℝ] ℂ :=
    smulRightL ℝ (ℝ × ℝ) ℂ (fst ℝ ℝ ℝ) (G₁₁ 0 0) + smulRightL ℝ (ℝ × ℝ) ℂ (snd ℝ ℝ ℝ) (G₂₁ 0 0) with hA₁
  set A₂ : ℝ × ℝ →L[ℝ] ℂ :=
    smulRightL ℝ (ℝ × ℝ) ℂ (fst ℝ ℝ ℝ) (G₁₂ 0 0) + smulRightL ℝ (ℝ × ℝ) ℂ (snd ℝ ℝ ℝ) (G₂₂ 0 0) with hA₂
  have hf'' : HasFDerivAt
      (fun p : ℝ × ℝ => smulRightL ℝ (ℝ × ℝ) ℂ (fst ℝ ℝ ℝ) (↿G₁ p) + smulRightL ℝ (ℝ × ℝ) ℂ (snd ℝ ℝ ℝ) (↿G₂ p))
      ((smulRightL ℝ (ℝ × ℝ) ℂ (fst ℝ ℝ ℝ)).comp A₁ + (smulRightL ℝ (ℝ × ℝ) ℂ (snd ℝ ℝ ℝ)).comp A₂) (0, 0) :=
    (((smulRightL ℝ (ℝ × ℝ) ℂ (fst ℝ ℝ ℝ)).hasFDerivAt.comp (0, 0) hG₁')).add
      (((smulRightL ℝ (ℝ × ℝ) ℂ (snd ℝ ℝ ℝ)).hasFDerivAt.comp (0, 0) hG₂'))
  have hsymm := second_derivative_symmetric_of_eventually_of_real (x := ((0 : ℝ), (0 : ℝ)))
    (Filter.Eventually.of_forall hG') hf'' (1, 0) (0, 1)

  have h12 : G₁₂ 0 0 = D X (D Y φ) g := by
    simp only [hG₁₂, hbase, fl_zero, mul_one]
  have h21 : G₂₁ 0 0 = D Y (D X φ) g := by
    simp only [hG₂₁, hbase, fl_zero, mul_one]
  have : G₁₂ 0 0 = G₂₁ 0 0 := by
    simpa [hA₁, hA₂] using hsymm
  rw [← h12, ← h21, this]

end Core

theorem sm_of_reg {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (h : (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw φ) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw φ)) (δ : Letter K) : Sm δ φ := by
  rcases δ with e | e
  · exact h.1 e.1 e.2.1
  · exact h.2 e.1 e.2.1

end KcCommNePlace

end

open KcCommNePlace in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    (∀ l, l.length ≤ 2 →
      Continuous (W l φ) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l φ)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l φ))) →
    ∀ d d' : (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex),
      Sum.elim (fun e => e.1) (fun e => e.1) d ≠ Sum.elim (fun e => e.1) (fun e => e.1) d' →
      W [d, d'] φ = W [d', d] φ := by
  intro W hreg d d' hne

  have h0 := hreg [] (by simp)
  have h1 : ∀ δ : Letter K, Continuous (D δ φ) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (D δ φ)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (D δ φ)) :=
    fun δ => hreg [δ] (by simp)
  have h2 : ∀ δ δ' : Letter K, Continuous (D δ (D δ' φ)) :=
    fun δ δ' => (hreg [δ, δ'] (by simp)).1
  show D d (D d' φ) = D d' (D d φ)
  exact D_comm_of_place_ne φ d d' hne
    (sm_of_reg h0.2 d) (sm_of_reg h0.2 d')
    (sm_of_reg (h1 d).2 d) (sm_of_reg (h1 d).2 d') (sm_of_reg (h1 d').2 d) (sm_of_reg (h1 d').2 d')
    (h1 d).1 (h1 d').1 (h2 d d) (h2 d' d) (h2 d d') (h2 d' d')

end S_AutomorphicForm_foldr_archDeriv_comm_of_ne_place
end P2MW
export P2MW.S_AutomorphicForm_foldr_archDeriv_comm_of_ne_place (solution)
