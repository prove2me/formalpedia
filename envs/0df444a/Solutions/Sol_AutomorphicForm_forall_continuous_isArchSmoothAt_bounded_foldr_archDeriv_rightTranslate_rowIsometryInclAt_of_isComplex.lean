-- Prove2me | solution 1 for AutomorphicForm.forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt_of_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f5e488bb-fd8b-5857-84a0-ffe07d93dbfd

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul
import Theorems.Thm_AutomorphicForm_isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt_of_isComplex
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain
open NumberField.InfinitePlace.Completion
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace TrC

variable {K : Type} [Field K] [NumberField K]

abbrev Dir (K : Type) [Field K] [NumberField K] : Type :=
  (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)

abbrev D1 (d : Dir K) (φ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ) (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d

abbrev Wd (l : List (Dir K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ) (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b

abbrev R {w : InfinitePlace K} (hw : w.IsReal) (x : ArchDir) : Dir K := Sum.inl ⟨w, hw, x⟩

abbrev place (d : Dir K) : InfinitePlace K := Sum.elim (fun e => e.1) (fun e => e.1) d

abbrev slab (K : Type) [Field K] [NumberField K] (a b : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

theorem Wd_nil (b : AdelicGL2 (𝓞 K) K → ℂ) : Wd [] b = b := rfl

theorem Wd_cons (d : Dir K) (l : List (Dir K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : Wd (d :: l) b = D1 d (Wd l b) := rfl

theorem Wd_append (l l' : List (Dir K)) (b : AdelicGL2 (𝓞 K) K → ℂ) : Wd (l ++ l') b = Wd l (Wd l' b) :=
  List.foldr_append

theorem archDerivAtComplex_comp_mul_left {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (h : AdelicGL2 (𝓞 K) K) :
    archDerivAtComplex hw d (fun g => φ (h * g)) = fun g => archDerivAtComplex hw d φ (h * g) := by
  funext g
  show deriv (fun t : ℝ => φ (h * (g * archFlowAtComplex hw d t))) 0 =
    deriv (fun t : ℝ => φ (h * g * archFlowAtComplex hw d t)) 0
  simp only [mul_assoc]

theorem D1_comp_mul_left (d : Dir K) (φ : AdelicGL2 (𝓞 K) K → ℂ) (h : AdelicGL2 (𝓞 K) K) :
    D1 d (fun g => φ (h * g)) = fun g => D1 d φ (h * g) := by
  rcases d with ⟨w, hw, d⟩ | ⟨w, hw, d⟩
  · exact archDerivAt_comp_mul_left hw d φ h
  · exact archDerivAtComplex_comp_mul_left hw d φ h

theorem IsArchSmoothAtComplex.add' {w : InfinitePlace K} {hw : w.IsComplex} {φ ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) : IsArchSmoothAtComplex hw (φ + ψ) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => φ (g * archComplexLiftAt hw e) + ψ (g * archComplexLiftAt hw e)) _
  exact (hφ g).add (hψ g)

def SmoothFor (d : Dir K) (φ : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  Sum.elim (fun e => IsArchSmoothAt e.2.1 φ) (fun e => IsArchSmoothAtComplex e.2.1 φ) d

theorem D1_add (d : Dir K) {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : SmoothFor d φ) (hψ : SmoothFor d ψ) :
    D1 d (φ + ψ) = D1 d φ + D1 d ψ := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact archDerivAt_add hφ hψ x
  · exact (AutomorphicForm.isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm K w hw).2.1 φ ψ hφ hψ x

theorem D1_smul (d : Dir K) (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) : D1 d (c • φ) = c • D1 d φ := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact archDerivAt_smul hw x c φ
  · exact (AutomorphicForm.isArchSmoothAtComplex_archDerivAtComplex_and_add_and_smul_and_comm K w hw).2.2.1 c φ x

theorem D1_zero (d : Dir K) : D1 d (0 : AdelicGL2 (𝓞 K) K → ℂ) = 0 := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact archDerivAt_const hw x 0
  · exact archDerivAtComplex_const hw x 0

theorem Wd_smul (l : List (Dir K)) (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) : Wd l (c • φ) = c • Wd l φ := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [Wd_cons, Wd_cons, ih, D1_smul]

theorem Wd_zero (l : List (Dir K)) : Wd l (0 : AdelicGL2 (𝓞 K) K → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [Wd_cons, ih, D1_zero]

def RegL (α β : ℝ) (j : ℕ) (ψ : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), ψ (globalPoints (𝓞 K) K γ * g) = ψ g) ∧
  ∀ l : List (Dir K), l.length ≤ j →
    Continuous (Wd l ψ) ∧
    (∀ (v : InfinitePlace K) (hv : v.IsReal), IsArchSmoothAt hv (Wd l ψ)) ∧
    (∀ (v : InfinitePlace K) (hv : v.IsComplex), IsArchSmoothAtComplex hv (Wd l ψ)) ∧
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K, g ∈ slab K α β → ‖Wd l ψ g‖ ≤ B

variable {α β : ℝ}

theorem RegL.smoothFor {j : ℕ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : RegL α β j ψ) (d : Dir K)
    (l : List (Dir K)) (hl : l.length ≤ j) : SmoothFor d (Wd l ψ) := by
  rcases d with ⟨w, hw, x⟩ | ⟨w, hw, x⟩
  · exact (h.2 l hl).2.1 w hw
  · exact (h.2 l hl).2.2.1 w hw

theorem RegL.smoothFor0 {j : ℕ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : RegL α β j ψ) (d : Dir K) :
    SmoothFor d ψ :=
  h.smoothFor d [] (Nat.zero_le _)

theorem RegL.mono {j j' : ℕ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : RegL α β j ψ) (hj : j' ≤ j) : RegL α β j' ψ :=
  ⟨h.1, fun l hl => h.2 l (hl.trans hj)⟩

theorem RegL.zero (j : ℕ) : RegL α β j (0 : AdelicGL2 (𝓞 K) K → ℂ) := by
  refine ⟨fun _ _ => rfl, fun l _ => ?_⟩
  rw [Wd_zero]
  exact ⟨continuous_const, fun v hv => isArchSmoothAt_const hv 0, fun v hv => isArchSmoothAtComplex_const hv 0,
    ⟨0, fun g _ => by simp⟩⟩

theorem RegL.smul {j : ℕ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : RegL α β j ψ) (c : ℂ) : RegL α β j (c • ψ) := by
  refine ⟨fun γ g => by simp only [Pi.smul_apply, h.1 γ g], fun l hl => ?_⟩
  obtain ⟨hc, hsR, hsC, B, hB⟩ := h.2 l hl
  rw [Wd_smul]
  refine ⟨hc.const_smul c, fun v hv => (hsR v hv).smul c, fun v hv => ?_, ⟨‖c‖ * B, fun g hg => ?_⟩⟩
  · intro g
    show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => c * Wd l ψ (g * archComplexLiftAt hv e)) _
    exact contDiffOn_const.mul (hsC v hv g)
  · rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hB g hg) (norm_nonneg _)

theorem Wd_add_of_regL {j : ℕ} {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : RegL α β j φ) (hψ : RegL α β j ψ) :
    ∀ l : List (Dir K), l.length ≤ j + 1 → Wd l (φ + ψ) = Wd l φ + Wd l ψ
  | [], _ => rfl
  | d :: l, hl => by
    rw [List.length_cons] at hl
    rw [Wd_cons, Wd_cons, Wd_cons, Wd_add_of_regL hφ hψ l (by omega),
      D1_add d (hφ.smoothFor d l (by omega)) (hψ.smoothFor d l (by omega))]

theorem RegL.add {j : ℕ} {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : RegL α β j φ) (hψ : RegL α β j ψ) :
    RegL α β j (φ + ψ) := by
  refine ⟨fun γ g => by simp only [Pi.add_apply, hφ.1 γ g, hψ.1 γ g], fun l hl => ?_⟩
  obtain ⟨hc, hsR, hsC, B, hB⟩ := hφ.2 l hl
  obtain ⟨hc', hsR', hsC', B', hB'⟩ := hψ.2 l hl
  rw [Wd_add_of_regL hφ hψ l (by omega)]
  exact ⟨hc.add hc', fun v hv => (hsR v hv).add (hsR' v hv), fun v hv => IsArchSmoothAtComplex.add' (hsC v hv) (hsC' v hv),
    ⟨B + B', fun g hg => (norm_add_le _ _).trans (add_le_add (hB g hg) (hB' g hg))⟩⟩

theorem RegL.sum {j : ℕ} {ι : Type} (s : Finset ι) {p : ι → AdelicGL2 (𝓞 K) K → ℂ}
    (h : ∀ i ∈ s, RegL α β j (p i)) : RegL α β j (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact RegL.zero j
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem D1_sum_of_regL {j : ℕ} {ι : Type} (s : Finset ι) {p : ι → AdelicGL2 (𝓞 K) K → ℂ}
    (h : ∀ i ∈ s, RegL α β j (p i)) (d : Dir K) : D1 d (∑ i ∈ s, p i) = ∑ i ∈ s, D1 d (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, D1_zero]
  | insert a s ha ih =>
    have h' : ∀ i ∈ s, RegL α β j (p i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      D1_add d ((h a (Finset.mem_insert_self a s)).smoothFor0 d) ((RegL.sum s h').smoothFor0 d), ih h']

theorem RegL.letter {j : ℕ} {ψ : AdelicGL2 (𝓞 K) K → ℂ} (h : RegL α β (j + 1) ψ) (d : Dir K) :
    RegL α β j (D1 d ψ) := by
  refine ⟨fun γ g => ?_, fun l hl => ?_⟩
  · have e := D1_comp_mul_left d ψ (globalPoints (𝓞 K) K γ)
    have hψ' : (fun g => ψ (globalPoints (𝓞 K) K γ * g)) = ψ := funext fun g => h.1 γ g
    rw [hψ'] at e
    exact (congrFun e g).symm
  · have e : Wd l (D1 d ψ) = Wd (l ++ [d]) ψ := by rw [Wd_append]; rfl
    rw [e]
    exact h.2 (l ++ [d]) (by rw [List.length_append, List.length_singleton]; omega)

theorem RegL.of_mem_span {j : ℕ} {ι : Type} {f : ι → AdelicGL2 (𝓞 K) K → ℂ} (hf : ∀ i, RegL α β j (f i))
    {c : AdelicGL2 (𝓞 K) K → ℂ} (hc : c ∈ Submodule.span ℂ (Set.range f)) : RegL α β j c := by
  refine Submodule.span_induction (p := fun c _ => RegL α β j c) ?_ (RegL.zero j) (fun _ _ _ _ h₁ h₂ => h₁.add h₂)
    (fun a _ _ h₁ => h₁.smul a) hc
  rintro _ ⟨i, rfl⟩
  exact hf i

section Translate

open scoped Classical

variable {w : InfinitePlace K}

abbrev incl (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) : AdelicGL2 (𝓞 K) K :=
  adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion)

abbrev mC (hw : w.IsComplex) (k : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) ℂ :=
  glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) (k : GL (Fin 2) w.Completion)

theorem incl_eq (hw : w.IsComplex) (k : rowIsometrySubgroup₀ w.Completion) : incl w k = archComplexGLAt hw (mC hw k) := by
  show adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion) =
    adelicArchGLInclAt K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm
      (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) (k : GL (Fin 2) w.Completion)))
  congr 1
  apply Units.ext
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact ((ringEquivComplexOfIsComplex hw).symm_apply_apply _).symm

abbrev Rk (k : rowIsometrySubgroup₀ w.Completion) (f : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun x => f (x * incl w k)

theorem ideleNorm_det_incl (k : rowIsometrySubgroup₀ w.Completion) :
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (incl w k)) = 1 := by
  have hfin : glFin (𝓞 K) K (incl w k) ∈ finiteIntegralGL2 (𝓞 K) K := by
    have : glFin (𝓞 K) K (incl w k) = 1 := glFin_adelicArchGLIncl K _
    rw [this]
    exact Subgroup.one_mem _
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult K (incl w k) hfin]
  refine Finset.prod_eq_one fun v _ => ?_
  have hglArch : glArch (𝓞 K) K (incl w k) = archGLIncl K w (k : GL (Fin 2) w.Completion) :=
    glArch_adelicArchGLIncl K _
  have h1 : NumberField.AdelicVolume.archDetNorm v (incl w k) = 1 := by
    unfold NumberField.AdelicVolume.archDetNorm
    rw [hglArch]
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archGLIncl_self]
      obtain ⟨hd, -⟩ := (mem_rowIsometrySubgroup₀_iff _).1 k.2
      rw [hd, norm_one]
    · rw [archComponent_archGLIncl_of_ne K hv, Units.val_one, Matrix.det_one, norm_one]
  rw [h1, one_pow]

theorem mul_incl_mem_slab {α β : ℝ} (k : rowIsometrySubgroup₀ w.Completion) {g : AdelicGL2 (𝓞 K) K}
    (hg : g ∈ slab K α β) : g * incl w k ∈ slab K α β := by
  show NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (g * incl w k)) ∈ Set.Icc α β
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_incl, mul_one]
  exact hg

theorem archComplexLiftAt_mul_archComplexGLAt (hw : w.IsComplex) {e : Fin 2 → Fin 2 → ℂ}
    (h : (Matrix.of e).det ≠ 0) (m : GL (Fin 2) ℂ) :
    archComplexLiftAt hw e * archComplexGLAt hw m =
      archComplexLiftAt hw (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℂ))) := by
  have hm : ((m : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero
  have h' : (Matrix.of (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℂ)))).det ≠ 0 := by
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero h hm
  rw [archComplexLiftAt_of_det_ne_zero hw h, archComplexLiftAt_of_det_ne_zero hw h', ← map_mul]
  congr 1
  ext i j
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem contDiff_of_symm_mul_const_complex (A : Matrix (Fin 2) (Fin 2) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 2 → Fin 2 → ℂ => (Matrix.of.symm (Matrix.of e * A) : Fin 2 → Fin 2 → ℂ) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun k _ =>
    ((contDiff_apply ℝ ℂ k).comp (contDiff_apply ℝ (Fin 2 → ℂ) i)).mul contDiff_const

theorem isArchSmoothAtComplex_Rk_self (hw : w.IsComplex) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : IsArchSmoothAtComplex hw f)
    (k : rowIsometrySubgroup₀ w.Completion) : IsArchSmoothAtComplex hw (Rk k f) := by
  intro g
  set m : GL (Fin 2) ℂ := mC hw k with hm
  have hmdet : ((m : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 m.isUnit).ne_zero
  have hmaps : Set.MapsTo (fun e : Fin 2 → Fin 2 → ℂ => (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℂ)) : Fin 2 → Fin 2 → ℂ))
      {e | (Matrix.of e).det ≠ 0} {e | (Matrix.of e).det ≠ 0} := by
    intro e he
    show (Matrix.of (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℂ)))).det ≠ 0
    rw [Equiv.apply_symm_apply, Matrix.det_mul]
    exact mul_ne_zero he hmdet
  have hcomp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun e : Fin 2 → Fin 2 → ℂ => f (g * archComplexLiftAt hw (Matrix.of.symm (Matrix.of e * (m : Matrix (Fin 2) (Fin 2) ℂ)))))
      {e | (Matrix.of e).det ≠ 0} :=
    (hf g).comp (contDiff_of_symm_mul_const_complex (m : Matrix (Fin 2) (Fin 2) ℂ)).contDiffOn hmaps
  refine hcomp.congr fun e he => ?_
  show f (g * archComplexLiftAt hw e * incl w k) = _
  rw [incl_eq hw k, mul_assoc, archComplexLiftAt_mul_archComplexGLAt hw he]

theorem archRealLiftAt_mul_incl_comm {v : InfinitePlace K} (hv : v.IsReal) (hvw : v ≠ w) (e : Fin 2 → Fin 2 → ℝ)
    (k : rowIsometrySubgroup₀ w.Completion) :
    archRealLiftAt hv e * incl w k = incl w k * archRealLiftAt hv e := by
  unfold archRealLiftAt
  split_ifs with h
  · exact (commute_adelicArchGLInclAt_of_ne K hvw _ _).eq
  · rw [one_mul, mul_one]

theorem archComplexLiftAt_mul_incl_comm {v : InfinitePlace K} (hv : v.IsComplex) (hvw : v ≠ w) (e : Fin 2 → Fin 2 → ℂ)
    (k : rowIsometrySubgroup₀ w.Completion) :
    archComplexLiftAt hv e * incl w k = incl w k * archComplexLiftAt hv e := by
  unfold archComplexLiftAt
  split_ifs with h
  · exact (commute_adelicArchGLInclAt_of_ne K hvw _ _).eq
  · rw [one_mul, mul_one]

theorem isArchSmoothAt_Rk {v : InfinitePlace K} (hv : v.IsReal) (hw : w.IsComplex) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : IsArchSmoothAt hv f) (k : rowIsometrySubgroup₀ w.Completion) : IsArchSmoothAt hv (Rk k f) := by
  have hvw : v ≠ w := fun h => by
    subst h; exact absurd hv (NumberField.InfinitePlace.not_isReal_iff_isComplex.2 hw)
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => f (g * archRealLiftAt hv e * incl w k)) _
  have : (fun e : Fin 2 → Fin 2 → ℝ => f (g * archRealLiftAt hv e * incl w k)) =
      fun e => f (g * incl w k * archRealLiftAt hv e) := by
    funext e; rw [mul_assoc, archRealLiftAt_mul_incl_comm hv hvw, ← mul_assoc]
  rw [this]
  exact hf (g * incl w k)

theorem isArchSmoothAtComplex_Rk_of_ne {v : InfinitePlace K} (hv : v.IsComplex) (hvw : v ≠ w)
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : IsArchSmoothAtComplex hv f) (k : rowIsometrySubgroup₀ w.Completion) :
    IsArchSmoothAtComplex hv (Rk k f) := by
  intro g
  show ContDiffOn ℝ (⊤ : ℕ∞) (fun e => f (g * archComplexLiftAt hv e * incl w k)) _
  have : (fun e : Fin 2 → Fin 2 → ℂ => f (g * archComplexLiftAt hv e * incl w k)) =
      fun e => f (g * incl w k * archComplexLiftAt hv e) := by
    funext e; rw [mul_assoc, archComplexLiftAt_mul_incl_comm hv hvw, ← mul_assoc]
  rw [this]
  exact hf (g * incl w k)

theorem RegL.translate0 (hw : w.IsComplex) {α β : ℝ} {f : AdelicGL2 (𝓞 K) K → ℂ} (h : RegL α β 0 f)
    (k : rowIsometrySubgroup₀ w.Completion) : RegL α β 0 (Rk k f) := by
  obtain ⟨hinv, hreg⟩ := h
  obtain ⟨hc, hsR, hsC, B, hB⟩ := hreg [] (le_refl 0)
  refine ⟨fun γ g => ?_, fun l hl => ?_⟩
  · show f (globalPoints (𝓞 K) K γ * g * incl w k) = f (g * incl w k)
    rw [mul_assoc, hinv]
  · obtain rfl : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hl)
    refine ⟨hc.comp (continuous_mul_const _), fun v hv => isArchSmoothAt_Rk hv hw (hsR v hv) k, fun v hv => ?_,
      ⟨B, fun g hg => hB _ (mul_incl_mem_slab k hg)⟩⟩
    by_cases hvw : v = w
    · subst hvw; exact isArchSmoothAtComplex_Rk_self hw (hsC _ _) k
    · exact isArchSmoothAtComplex_Rk_of_ne hv hvw (hsC v hv) k

private abbrev _root_.TrC.comb6 (hw : w.IsComplex) (c : ArchDirComplex → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  c .H • archDerivAtComplex hw .H f + c .iH • archDerivAtComplex hw .iH f + c .E • archDerivAtComplex hw .E f +
    c .iE • archDerivAtComplex hw .iE f + c .Fm • archDerivAtComplex hw .Fm f + c .iFm • archDerivAtComplex hw .iFm f

p2m_export "TrC" "comb6"

theorem D1_Rk (hw : w.IsComplex) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : IsArchSmoothAtComplex hw f)
    (k : rowIsometrySubgroup₀ w.Completion) (d : Dir K) :
    ∃ c : ArchDirComplex → ℂ, D1 d (Rk k f) = Rk k (if place d = w then comb6 hw c f else D1 d f) := by
  by_cases hd : place d = w
  · simp only [if_pos hd]
    rcases d with ⟨w', hw', x⟩ | ⟨w', hw', x⟩
    · have hd' : w' = w := hd
      subst hd'
      exact absurd hw' (NumberField.InfinitePlace.not_isReal_iff_isComplex.2 hw)
    · have hd' : w' = w := hd
      subst hd'
      set m : GL (Fin 2) ℂ := mC hw k with hm
      set X : Matrix (Fin 2) (Fin 2) ℂ := (match x with
        | .H => !![1, 0; 0, -1] | .E => !![0, 1; 0, 0] | .Fm => !![0, 0; 1, 0]
        | .iH => !![Complex.I, 0; 0, -Complex.I] | .iE => !![0, Complex.I; 0, 0] | .iFm => !![0, 0; Complex.I, 0]) with hX
      set Y : Matrix (Fin 2) (Fin 2) ℂ := ((m⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * X * (m : Matrix (Fin 2) (Fin 2) ℂ)
        with hY
      refine ⟨fun y => match y with
        | .H => (((Y 0 0 - Y 1 1) / 2).re : ℂ) | .iH => (((Y 0 0 - Y 1 1) / 2).im : ℂ)
        | .E => ((Y 0 1).re : ℂ) | .iE => ((Y 0 1).im : ℂ) | .Fm => ((Y 1 0).re : ℂ) | .iFm => ((Y 1 0).im : ℂ), ?_⟩
      funext g
      have hD := AutomorphicForm.hasDerivAt_apply_mul_archComplexGLAt_inv_mul_archFlowMatrixComplex_mul K hw f hf
        (g * incl w' k) m x
      have hfun : (fun s : ℝ => Rk k f (g * archFlowAtComplex hw x s)) =
          fun s => f (g * incl w' k * archComplexGLAt hw (m⁻¹ * archFlowMatrixComplex x s * m)) := by
        funext s
        show f (g * archFlowAtComplex hw x s * incl w' k) = _
        rw [incl_eq hw k, archFlowAtComplex, mul_assoc, mul_assoc, ← map_mul, ← map_mul, ← mul_assoc, ← mul_assoc,
          mul_inv_cancel, one_mul]
      show deriv (fun s : ℝ => Rk k f (g * archFlowAtComplex hw' x s)) 0 = _
      rw [hfun, hD.deriv]
      simp only [comb6, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      cases x <;> rfl
  · refine ⟨fun _ => 0, ?_⟩
    rw [if_neg hd]
    rcases d with ⟨w', hw', x⟩ | ⟨w', hw', x⟩
    · change w' ≠ w at hd
      funext g
      show deriv (fun t : ℝ => f (g * archFlowAt hw' x t * incl w k)) 0 = deriv (fun t : ℝ => f (g * incl w k * archFlowAt hw' x t)) 0
      congr 1
      funext t
      rw [mul_assoc, mul_assoc]
      congr 2
      exact (commute_adelicArchGLInclAt_of_ne K hd _ _).eq
    · change w' ≠ w at hd
      funext g
      show deriv (fun t : ℝ => f (g * archFlowAtComplex hw' x t * incl w k)) 0 =
        deriv (fun t : ℝ => f (g * incl w k * archFlowAtComplex hw' x t)) 0
      congr 1
      funext t
      rw [mul_assoc, mul_assoc]
      congr 2
      exact (commute_adelicArchGLInclAt_of_ne K hd _ _).eq

abbrev RC (hw : w.IsComplex) (x : ArchDirComplex) : Dir K := Sum.inr ⟨w, hw, x⟩

theorem RegL.comb6 (hw : w.IsComplex) {α β : ℝ} {i : ℕ} {Φ : AdelicGL2 (𝓞 K) K → ℂ} (hΦ : RegL α β (i + 1) Φ)
    (c : ArchDirComplex → ℂ) : RegL α β i (comb6 hw c Φ) :=
  ((((((hΦ.letter (RC hw .H)).smul (c .H)).add ((hΦ.letter (RC hw .iH)).smul (c .iH))).add
    ((hΦ.letter (RC hw .E)).smul (c .E))).add ((hΦ.letter (RC hw .iE)).smul (c .iE))).add
    ((hΦ.letter (RC hw .Fm)).smul (c .Fm))).add ((hΦ.letter (RC hw .iFm)).smul (c .iFm))

theorem exists_Wd_Rk (hw : w.IsComplex) {α β : ℝ} (k : rowIsometrySubgroup₀ w.Completion) :
    ∀ (l : List (Dir K)) (i : ℕ) (f : AdelicGL2 (𝓞 K) K → ℂ), RegL α β (l.length + i) f →
      ∃ Φ : AdelicGL2 (𝓞 K) K → ℂ, RegL α β i Φ ∧ Wd l (Rk k f) = Rk k Φ
  | [], i, f, hf => ⟨f, by simpa using hf, rfl⟩
  | d :: l, i, f, hf => by
    rw [List.length_cons] at hf
    have hf' : RegL α β (l.length + (i + 1)) f := by
      have : l.length + 1 + i = l.length + (i + 1) := by omega
      rw [this] at hf; exact hf
    obtain ⟨Φ, hΦ, hW⟩ := exists_Wd_Rk hw k l (i + 1) f hf'
    have hΦs : IsArchSmoothAtComplex hw Φ := (hΦ.2 [] (Nat.zero_le _)).2.2.1 w hw
    obtain ⟨c, hc⟩ := D1_Rk hw hΦs k d
    rw [Wd_cons, hW, hc]
    by_cases hd : place d = w
    · rw [if_pos hd]
      exact ⟨_, hΦ.comb6 hw c, rfl⟩
    · rw [if_neg hd]
      exact ⟨_, hΦ.letter d, rfl⟩

theorem RegL.translate (hw : w.IsComplex) {α β : ℝ} {j : ℕ} {f : AdelicGL2 (𝓞 K) K → ℂ} (h : RegL α β j f)
    (k : rowIsometrySubgroup₀ w.Completion) : RegL α β j (Rk k f) := by
  refine ⟨(RegL.translate0 hw (h.mono (Nat.zero_le _)) k).1, fun l hl => ?_⟩
  have hf : RegL α β (l.length + (j - l.length)) f := by
    have : l.length + (j - l.length) = j := by omega
    rw [this]; exact h
  obtain ⟨Φ, hΦ, hW⟩ := exists_Wd_Rk hw k l (j - l.length) f hf
  rw [hW]
  have h0 := RegL.translate0 hw (hΦ.mono (Nat.zero_le _)) k
  exact h0.2 [] (le_refl 0)

end Translate

end TrC

open TrC in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (j : ℕ)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), ψ (globalPoints (𝓞 K) K γ * g) = ψ g) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    (∀ l, l.length ≤ j →
      Continuous (W l ψ) ∧
      (∀ (v : InfinitePlace K) (hv : v.IsReal), IsArchSmoothAt hv (W l ψ)) ∧
      (∀ (v : InfinitePlace K) (hv : v.IsComplex), IsArchSmoothAtComplex hv (W l ψ)) ∧
      ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖W l ψ g‖ ≤ B) →
    ∀ (w : InfinitePlace K) (hw : w.IsComplex) (k : rowIsometrySubgroup₀ w.Completion),
      (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        rightTranslate K (rowIsometryInclAt₀ K w k) ψ (globalPoints (𝓞 K) K γ * g) =
          rightTranslate K (rowIsometryInclAt₀ K w k) ψ g) ∧
      ∀ l, l.length ≤ j →
        Continuous (W l (rightTranslate K (rowIsometryInclAt₀ K w k) ψ)) ∧
        (∀ (v : InfinitePlace K) (hv : v.IsReal), IsArchSmoothAt hv (W l (rightTranslate K (rowIsometryInclAt₀ K w k) ψ))) ∧
        (∀ (v : InfinitePlace K) (hv : v.IsComplex),
          IsArchSmoothAtComplex hv (W l (rightTranslate K (rowIsometryInclAt₀ K w k) ψ))) ∧
        ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β →
            ‖W l (rightTranslate K (rowIsometryInclAt₀ K w k) ψ) g‖ ≤ B := by
  intro W hreg w hw k
  have hR : RegL α β j ψ := ⟨hinv, hreg⟩
  have hT : RegL α β j (Rk k ψ) := RegL.translate hw hR k
  exact hT

end

end S_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt_of_isComplex
end P2MW
export P2MW.S_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt_of_isComplex (solution)
