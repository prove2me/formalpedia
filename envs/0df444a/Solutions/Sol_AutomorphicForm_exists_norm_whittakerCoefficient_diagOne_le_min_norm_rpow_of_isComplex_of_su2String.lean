-- Prove2me | solution 1 for AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/318268d3-5b79-5ae9-91d0-1b058b762527

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex
import Theorems.Thm_AutomorphicForm_gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isComplex
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Group.Even
import Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq
import Theorems.Thm_LanglandsTunnell_exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos
import Theorems.Thm_LanglandsTunnell_exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded
import Theorems.Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

noncomputable section

open scoped Classical

namespace E40DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

abbrev eC {w : InfinitePlace K} (hw : w.IsComplex) : w.Completion ≃+* ℂ := ringEquivComplexOfIsComplex hw

def iotaW {w : InfinitePlace K} (hw : w.IsComplex) : ℂˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (archUnitHom w).comp (Units.map (eC hw).symm.toRingHom.toMonoidHom)

def bprime (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  b * (archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹

def g0 (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) : AdelicGL2 (𝓞 K) K := diagOne (bprime w b)

abbrev W (D : Set (AdelicGL2 (𝓞 K) K)) (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  whittakerCoefficient K (productionPinsOf K D
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
    (NumberField.StandardAddChar.stdAddChar K) φ 1 g

def Fstr (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (p : Fin (n + 1)) (h : GL (Fin 2) ℂ) : ℂ :=
  W D (x p) (g0 w b * archComplexGLAt hw h)

def DFstr (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ) : ℂ :=
  W D (archDerivAtComplex hw d (x p)) (g0 w b * archComplexGLAt hw h)

def DDstr (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (p : Fin (n + 1)) (d' d : ArchDirComplex) (h : GL (Fin 2) ℂ) : ℂ :=
  W D (archDerivAtComplex hw d' (archDerivAtComplex hw d (x p))) (g0 w b * archComplexGLAt hw h)

def fstr (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (m : ℕ) (y : ℝ) : ℂ :=
  if hm : m < n + 1 then Fstr D hw b x ⟨m, hm⟩ (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ)) else 0

theorem bprime_fst_self (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) :
    ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 := by
  classical
  have hne : ((b : AdeleRing (𝓞 K) K)).1 w ≠ 0 := by
    intro h
    have h1 : (((b * b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 := by rw [mul_inv_cancel]; rfl
    have : (((b * b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w =
        ((b : AdeleRing (𝓞 K) K)).1 w * (((b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w := rfl
    rw [this, h, zero_mul] at h1; exact zero_ne_one h1
  rw [bprime]
  show ((b : AdeleRing (𝓞 K) K)).1 w * ((((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K)).1 w = 1
  rw [← map_inv, archUnitHom_apply]
  show ((b : AdeleRing (𝓞 K) K)).1 w * Function.update (1 : InfiniteAdeleRing K) w _ w = 1
  rw [Function.update_self]
  show ((b : AdeleRing (𝓞 K) K)).1 w * (((infiniteUnitsComponent (𝓞 K) K w b)⁻¹ : (w.Completion)ˣ) : w.Completion) = 1
  rw [← map_inv]
  show ((b : AdeleRing (𝓞 K) K)).1 w * (((b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1
  have : (((b * b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 := by rw [mul_inv_cancel]; rfl
  exact this

theorem bprime_fst_of_ne {w w' : InfinitePlace K} (hne : w' ≠ w) (b : (AdeleRing (𝓞 K) K)ˣ) :
    ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w' := by
  classical
  rw [bprime]
  show ((b : AdeleRing (𝓞 K) K)).1 w' * ((((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K)).1 w' = _
  rw [← map_inv, archUnitHom_apply]
  show ((b : AdeleRing (𝓞 K) K)).1 w' * Function.update (1 : InfiniteAdeleRing K) w _ w' = _
  rw [Function.update_of_ne hne]
  show ((b : AdeleRing (𝓞 K) K)).1 w' * 1 = _
  rw [mul_one]

theorem bprime_snd (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) :
    ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = ((b : AdeleRing (𝓞 K) K)).2 := by
  rw [bprime]
  show ((b : AdeleRing (𝓞 K) K)).2 * ((((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K)).2 = _
  rw [← map_inv, archUnitHom_apply]
  show ((b : AdeleRing (𝓞 K) K)).2 * 1 = _
  rw [mul_one]

theorem hasDerivAt_W_string (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex)
    (b : (AdeleRing (𝓞 K) K)ˣ) {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxc : ∀ p, Continuous (x p))
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p))) :
    (∀ (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (h * archFlowMatrixComplex d t)))
        (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (x p)) 1 (g0 w b * archComplexGLAt hw h)) 0) ∧
    (∀ (p : Fin (n + 1)) (d d' : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d' (x p)) 1 (g0 w b * archComplexGLAt hw (h * archFlowMatrixComplex d t)))
        (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (archDerivAtComplex hw d' (x p))) 1 (g0 w b * archComplexGLAt hw h)) 0) := by
  have hs : ∀ p, IsArchSmoothAtComplex hw (x p) := fun p => by simpa only [List.foldr] using (hreg p []).1
  have h1 : ∀ p (d : ArchDirComplex), Continuous (archDerivAtComplex hw d (x p)) := fun p d => by
    simpa only [List.foldr] using (hreg p [d]).2
  have h2 : ∀ p (d d' : ArchDirComplex), Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (x p))) := fun p d d' => by
    simpa only [List.foldr] using (hreg p [d, d']).2
  exact ⟨fun p => (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex K D w hw (x p)
      (hxc p) (hs p) (h1 p) (h2 p) (g0 w b)).1,
    fun p => (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex K D w hw (x p)
      (hxc p) (hs p) (h1 p) (h2 p) (g0 w b)).2⟩

section Casimir

variable {w : InfinitePlace K} (hw : w.IsComplex)

theorem archDelAt_apply' {ψ : AdelicGL2 (𝓞 K) K → ℂ} (d : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    archDelAt hw d ψ g = (1 / 2 : ℂ) * (archDerivAtComplex hw d.toComplex ψ g - Complex.I * archDerivAtComplex hw d.toComplexI ψ g) := by
  simp only [archDelAt, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

theorem archDelBarAt_apply' {ψ : AdelicGL2 (𝓞 K) K → ℂ} (d : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    archDelBarAt hw d ψ g = (1 / 2 : ℂ) * (archDerivAtComplex hw d.toComplex ψ g + Complex.I * archDerivAtComplex hw d.toComplexI ψ g) := by
  simp only [archDelBarAt, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem archDerivAtComplex_sub'' {φ ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) (d : ArchDirComplex) :
    archDerivAtComplex hw d (φ - ψ) = archDerivAtComplex hw d φ - archDerivAtComplex hw d ψ := by
  rw [sub_eq_add_neg, archDerivAtComplex_add hφ hψ.neg, ← neg_one_smul ℂ ψ, archDerivAtComplex_smul, neg_one_smul,
    ← sub_eq_add_neg]

theorem archDerivAtComplex_archDelAt' {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAtComplex hw ψ)
    (d : ArchDirComplex) (d' : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    archDerivAtComplex hw d (archDelAt hw d' ψ) g =
      (1 / 2 : ℂ) * (archDerivAtComplex hw d (archDerivAtComplex hw d'.toComplex ψ) g -
        Complex.I * archDerivAtComplex hw d (archDerivAtComplex hw d'.toComplexI ψ) g) := by
  unfold AutomorphicForm.archDelAt
  rw [archDerivAtComplex_smul, archDerivAtComplex_sub'' hw (hψ.archDerivAtComplex _) ((hψ.archDerivAtComplex _).smul _),
    archDerivAtComplex_smul]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

theorem archDerivAtComplex_archDelBarAt' {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAtComplex hw ψ)
    (d : ArchDirComplex) (d' : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    archDerivAtComplex hw d (archDelBarAt hw d' ψ) g =
      (1 / 2 : ℂ) * (archDerivAtComplex hw d (archDerivAtComplex hw d'.toComplex ψ) g +
        Complex.I * archDerivAtComplex hw d (archDerivAtComplex hw d'.toComplexI ψ) g) := by
  unfold AutomorphicForm.archDelBarAt
  rw [archDerivAtComplex_smul, archDerivAtComplex_add (hψ.archDerivAtComplex _) ((hψ.archDerivAtComplex _).smul _),
    archDerivAtComplex_smul]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]

def casWords (φ : AdelicGL2 (𝓞 K) K → ℂ) : Fin 10 → (AdelicGL2 (𝓞 K) K → ℂ) :=
  ![archDerivAtComplex hw .H (archDerivAtComplex hw .H φ), archDerivAtComplex hw .H (archDerivAtComplex hw .iH φ),
    archDerivAtComplex hw .iH (archDerivAtComplex hw .H φ), archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ),
    archDerivAtComplex hw .H φ, archDerivAtComplex hw .iH φ,
    archDerivAtComplex hw .E (archDerivAtComplex hw .Fm φ), archDerivAtComplex hw .E (archDerivAtComplex hw .iFm φ),
    archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm φ), archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ)]

def casCoeff : Fin 10 → ℂ :=
  ![-(1 / 16 : ℂ), Complex.I / 16, Complex.I / 16, 1 / 16, 1 / 4, -(Complex.I / 4), -(1 / 4 : ℂ), Complex.I / 4, Complex.I / 4, 1 / 4]

def casBarCoeff : Fin 10 → ℂ :=
  ![-(1 / 16 : ℂ), -(Complex.I / 16), -(Complex.I / 16), 1 / 16, 1 / 4, Complex.I / 4, -(1 / 4 : ℂ), -(Complex.I / 4),
    -(Complex.I / 4), 1 / 4]

theorem archCasimirAtComplex_eq_sum {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirAtComplex hw φ = fun g => ∑ j : Fin 10, casCoeff j * casWords hw φ j g := by
  funext g
  simp only [archCasimirAtComplex, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [archDelAt_apply' hw .H (ψ := archDelAt hw .H φ), archDerivAtComplex_archDelAt' hw hφ, archDerivAtComplex_archDelAt' hw hφ,
    archDelAt_apply' hw .H (ψ := φ), archDelAt_apply' hw .E (ψ := archDelAt hw .Fm φ), archDerivAtComplex_archDelAt' hw hφ,
    archDerivAtComplex_archDelAt' hw hφ]
  simp only [casCoeff, casWords, ArchDir.toComplex, ArchDir.toComplexI, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  linear_combination (-(1 / 16 : ℂ) * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) g -
    (1 / 4 : ℂ) * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g) * Complex.I_sq

theorem archCasimirBarAtComplex_eq_sum {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirBarAtComplex hw φ = fun g => ∑ j : Fin 10, casBarCoeff j * casWords hw φ j g := by
  funext g
  simp only [archCasimirBarAtComplex, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [archDelBarAt_apply' hw .H (ψ := archDelBarAt hw .H φ), archDerivAtComplex_archDelBarAt' hw hφ, archDerivAtComplex_archDelBarAt' hw hφ,
    archDelBarAt_apply' hw .H (ψ := φ), archDelBarAt_apply' hw .E (ψ := archDelBarAt hw .Fm φ), archDerivAtComplex_archDelBarAt' hw hφ,
    archDerivAtComplex_archDelBarAt' hw hφ]
  simp only [casBarCoeff, casWords, ArchDir.toComplex, ArchDir.toComplexI, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  linear_combination (-(1 / 16 : ℂ) * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) g -
    (1 / 4 : ℂ) * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g) * Complex.I_sq

end Casimir

end E40DCFN

namespace E40UNI

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

theorem map_unipotentGL2 {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (x : A) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  ext i j
  change f ((unipotentGL2 x : Matrix (Fin 2) (Fin 2) A) i j) = (unipotentGL2 (f x) : Matrix (Fin 2) (Fin 2) B) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem archComponent_glArch_unipotentGL2 (w : InfinitePlace K) (X : AdeleRing (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K (unipotentGL2 X)) = unipotentGL2 (X.1 w) := by
  change Matrix.GeneralLinearGroup.map (archEval K w)
    (Matrix.GeneralLinearGroup.map (adeleArch (𝓞 K) K) (unipotentGL2 X)) = _
  rw [map_unipotentGL2, map_unipotentGL2]
  rfl

theorem glFin_unipotentGL2 (X : AdeleRing (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 X) = unipotentGL2 X.2 := by
  change Matrix.GeneralLinearGroup.map (adeleFin (𝓞 K) K) (unipotentGL2 X) = _
  rw [map_unipotentGL2]
  rfl

theorem glEquivOfRingEquiv_unipotentGL2 {A B : Type*} [NormedField A] [NormedField B] (e : A ≃+* B) (x : A) :
    glEquivOfRingEquiv e (unipotentGL2 x) = unipotentGL2 (e x) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glEquivOfRingEquiv_apply_entry, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

omit [NumberField K] in
theorem glArch_ext' {x y : GL (Fin 2) (InfiniteAdeleRing K)}
    (h : ∀ w : InfinitePlace K, archComponent K w x = archComponent K w y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => funext fun w => ?_
  exact congrArg (fun g : GL (Fin 2) w.Completion => (g : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h w)

open scoped Classical in

theorem archComplexGLAt_unipotentGL2 {w : InfinitePlace K} (hw : w.IsComplex) (z : ℂ) :
    archComplexGLAt hw (unipotentGL2 z) =
      unipotentGL2 (show (AdeleRing (𝓞 K) K) from (Pi.single w ((ringEquivComplexOfIsComplex hw).symm z), 0)) := by
  refine eq_of_glArch_eq_of_glFin_eq (glArch_ext' fun w' => ?_) ?_
  · rw [archComponent_glArch_unipotentGL2]
    have hL : glArch (𝓞 K) K (archComplexGLAt hw (unipotentGL2 z)) =
        archGLIncl K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm (unipotentGL2 z)) :=
      glArch_adelicArchGLIncl K _
    rw [hL, glEquivOfRingEquiv_unipotentGL2]
    by_cases hww : w' = w
    · subst hww
      rw [archComponent_archGLIncl_self]
      congr 1
      show _ = Pi.single (M := fun v : InfinitePlace K => v.Completion) w' ((ringEquivComplexOfIsComplex hw).symm z) w'
      rw [Pi.single_eq_same]
    · rw [archComponent_archGLIncl_of_ne K hww]
      have h0 : ((show (AdeleRing (𝓞 K) K) from (Pi.single w ((ringEquivComplexOfIsComplex hw).symm z), 0))).1 w' = 0 := by
        show Pi.single (M := fun v : InfinitePlace K => v.Completion) w ((ringEquivComplexOfIsComplex hw).symm z) w' = 0
        exact Pi.single_eq_of_ne hww _
      rw [h0, unipotentGL2_zero]
  · rw [glFin_unipotentGL2]
    have hF : glFin (𝓞 K) K (archComplexGLAt hw (unipotentGL2 z)) = 1 := glFin_adelicArchGLIncl K _
    rw [hF]
    show (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) = unipotentGL2 0
    rw [unipotentGL2_zero]

theorem unipotentGL2_algebraMap_eq_globalPoints (β : K) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) = globalPoints (𝓞 K) K (unipotentGL2 β) := by
  refine Units.ext ?_
  ext i j
  simp only [unipotentGL2_coe, globalPoints, Matrix.GeneralLinearGroup.map_apply,
    Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp

end E40UNI

namespace E40IFC

open E40DCFN E40UNI NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

open scoped Classical in

theorem hN_string (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxG : ∀ p (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x p (globalPoints (𝓞 K) K γ * g) = x p g)
    (hcomm : ∀ m : GL (Fin 2) ℂ, archComplexGLAt hw m * g0 w b = g0 w b * archComplexGLAt hw m) :
    ∀ (p : Fin (n + 1)) (z : ℂ) (h : GL (Fin 2) ℂ),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (unipotentGL2 z * h)) =
        Complex.exp (2 * Real.pi * Complex.I * ((2 * ((1 : ℂ) * z).re : ℝ) : ℂ)) *
          whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw h) := by
  intro p z h
  set X : AdeleRing (𝓞 K) K := (show (AdeleRing (𝓞 K) K) from (Pi.single w ((ringEquivComplexOfIsComplex hw).symm z), 0))
    with hX
  have hgeom : g0 w b * archComplexGLAt hw (unipotentGL2 z * h) = unipotentGL2 X * (g0 w b * archComplexGLAt hw h) := by
    rw [map_mul, ← mul_assoc, ← hcomm, archComplexGLAt_unipotentGL2, mul_assoc]
  rw [hgeom]
  have hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K),
      x p (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * (g0 w b * archComplexGLAt hw h)) =
        x p (unipotentGL2 u * (g0 w b * archComplexGLAt hw h)) := by
    intro β u
    rw [unipotentGL2_add, mul_assoc, unipotentGL2_algebraMap_eq_globalPoints, hxG]
  have hcov := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K D
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (NumberField.StandardAddChar.stdAddChar K)
    (NumberField.StandardAddChar.adelicTraceData K).isGlobalAddChar_psiK.principalInvariant
    (x p) (g0 w b * archComplexGLAt hw h) hper 1 X
  rw [map_one, one_mul] at hcov
  rw [hcov, hX, NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex K w hw z, one_mul]

end E40IFC

namespace E40DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

theorem glInf_ext {a b : GL (Fin 2) (InfiniteAdeleRing K)}
    (h : ∀ v : InfinitePlace K, archComponent K v a = archComponent K v b) : a = b := by
  apply Units.ext
  ext i j
  funext v
  have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (v.Completion) =>
    (m : Matrix (Fin 2) (Fin 2) (v.Completion))) (h v)) i) j
  beta_reduce at this
  rwa [archComponent_apply, archComponent_apply] at this

theorem archComplexGLAt_mul_comm_of_archComponent_eq_one {w : InfinitePlace K} (hw : w.IsComplex) (m : GL (Fin 2) ℂ)
    {k : AdelicGL2 (𝓞 K) K} (hk : archComponent K w (glArch (𝓞 K) K k) = 1) :
    archComplexGLAt hw m * k = k * archComplexGLAt hw m := by
  have hfin : glFin (𝓞 K) K (archComplexGLAt hw m) = 1 := glFin_adelicArchGLIncl K _
  have harch : glArch (𝓞 K) K (archComplexGLAt hw m) =
      archGLIncl K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m) := glArch_adelicArchGLIncl K _
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, harch]
    refine glInf_ext K fun v => ?_
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv; rw [hk, mul_one, one_mul, archComponent_archGLIncl_self]
    · rw [archComponent_archGLIncl_of_ne K hv, one_mul, mul_one]
  · rw [map_mul, map_mul, hfin, mul_one, one_mul]

theorem archComponent_glArch_g0 (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) :
    archComponent K w (glArch (𝓞 K) K (g0 w b)) = 1 := by
  ext i j
  rw [archComponent_apply, glArch_apply]
  show ((Matrix.diagonal ![((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1] i j).1 w) =
    (1 : Matrix (Fin 2) (Fin 2) (w.Completion)) i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, bprime_fst_self] <;> rfl

theorem archComplexGLAt_mul_g0 {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ) (m : GL (Fin 2) ℂ) :
    archComplexGLAt hw m * g0 w b = g0 w b * archComplexGLAt hw m :=
  archComplexGLAt_mul_comm_of_archComponent_eq_one K hw m (archComponent_glArch_g0 K w b)

section Wlemmas
variable (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)

theorem whittakerCoefficient_mul_right (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (g k : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * k) = whittakerCoefficient K pins ψ (fun y => φ (y * k)) α g := by
  unfold whittakerCoefficient
  congr 1
  funext u
  simp only [mul_assoc]

theorem whittakerCoefficient_const_mul (φ : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ (fun y => c * φ y) α g = c * whittakerCoefficient K pins ψ φ α g := by
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1
  funext u
  ring

end Wlemmas

theorem Fstr_mul_circleGL2 (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p)) :
    ∀ (p : Fin (n + 1)) (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ,
      Fstr D hw b x p (h * circleGL2 ζ) = (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * Fstr D hw b x p h := by
  intro p ζ hζ h
  unfold Fstr W
  rw [map_mul, ← mul_assoc, whittakerCoefficient_mul_right]
  have hfun : (fun y => x p (y * archComplexGLAt hw (circleGL2 ζ))) = fun y => (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * x p y :=
    funext fun y => hwt p ζ hζ y
  rw [hfun, whittakerCoefficient_const_mul]

theorem det_diagOne (a : (AdeleRing (𝓞 K) K)ˣ) : Matrix.GeneralLinearGroup.det (diagOne a : AdelicGL2 (𝓞 K) K) = a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![(a : AdeleRing (𝓞 K) K), 1]).det = a
  rw [Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

theorem ideleNorm_eq_norm_pow_mul_of_eq_off (w : InfinitePlace K) (b a : (AdeleRing (𝓞 K) K)ˣ)
    (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') :
    ideleNorm K a = ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ w.mult *
      ∏ w' ∈ Finset.univ.erase w, ‖((b : AdeleRing (𝓞 K) K)).1 w'‖ ^ w'.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K a ha,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  congr 1
  refine Finset.prod_congr rfl fun w' hw' => ?_
  rw [hab w' (Finset.mem_erase.1 hw').1]

theorem exists_norm_W_diagOne_le_norm_rpow_of_gr (D : Set (AdelicGL2 (𝓞 K) K)) (w₀ : ℝ) (w : InfinitePlace K)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hgr : ∀ p, ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (b : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 →
      (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
          (diagOne a)‖ ≤ C * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) := by
  choose C₀ hC₀ using hgr
  set Pb : ℝ := ∏ w' ∈ Finset.univ.erase w, ‖((b : AdeleRing (𝓞 K) K)).1 w'‖ ^ w'.mult with hPb
  have hbpos : ∀ w' : InfinitePlace K, 0 < ‖((b : AdeleRing (𝓞 K) K)).1 w'‖ := by
    intro w'
    have h := congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w') b.mul_inv
    change ((b : AdeleRing (𝓞 K) K)).1 w' * (((b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w' = 1 at h
    exact norm_pos_iff.2 (left_ne_zero_of_mul_eq_one h)
  have hPb0 : 0 < Pb := Finset.prod_pos fun w' _ => pow_pos (hbpos w') _
  refine ⟨(∑ p, |C₀ p|) * Pb ^ (w₀ / 2), mul_nonneg (Finset.sum_nonneg fun p _ => abs_nonneg _) (Real.rpow_nonneg hPb0.le _), ?_⟩
  intro p a ha hab
  have hr0 : 0 < ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := by
    have h := congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w) a.mul_inv
    change ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 at h
    exact norm_pos_iff.2 (left_ne_zero_of_mul_eq_one h)
  have hN : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (diagOne a : AdelicGL2 (𝓞 K) K)) ^ (w₀ / 2) =
      ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * Pb ^ (w₀ / 2) := by
    rw [det_diagOne, ideleNorm_eq_norm_pow_mul_of_eq_off K w b a ha hab, Real.mul_rpow (pow_nonneg hr0.le _) hPb0.le,
      ← Real.rpow_natCast_mul hr0.le]
    congr 2
    ring
  calc ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
          (diagOne a)‖
      ≤ C₀ p * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (diagOne a : AdelicGL2 (𝓞 K) K)) ^ (w₀ / 2) := hC₀ p _
    _ = C₀ p * Pb ^ (w₀ / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) := by rw [hN]; ring
    _ ≤ (∑ p, |C₀ p|) * Pb ^ (w₀ / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (Real.rpow_nonneg hPb0.le _))
          (Real.rpow_nonneg hr0.le _)
        exact Finset.single_le_sum (fun q _ => abs_nonneg (C₀ q)) (Finset.mem_univ p)

end E40DCFN

namespace E40DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

theorem mult_eq_two_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) : w.mult = 2 :=
  NumberField.InfinitePlace.mult_isComplex ⟨w, hw⟩

theorem norm_eC {w : InfinitePlace K} (hw : w.IsComplex) (x : w.Completion) : ‖eC hw x‖ = ‖x‖ := by
  show ‖ringEquivComplexOfIsComplex hw x‖ = ‖x‖
  rw [ringEquivComplexOfIsComplex_apply]
  exact (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

theorem norm_eC_symm {w : InfinitePlace K} (hw : w.IsComplex) (z : ℂ) : ‖(eC hw).symm z‖ = ‖z‖ := by
  conv_rhs => rw [← (eC hw).apply_symm_apply z]
  rw [norm_eC]

def diagGL (z₁ z₂ : ℂˣ) : GL (Fin 2) ℂ where
  val := !![(z₁ : ℂ), 0; 0, (z₂ : ℂ)]
  inv := !![((z₁⁻¹ : ℂˣ) : ℂ), 0; 0, ((z₂⁻¹ : ℂˣ) : ℂ)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagGL_eq_scalar_mul_split_mul_circle (z t ζ : ℂˣ) (u : ℝ) (ht : (t : ℂ) ^ 2 = z)
    (huζ : Complex.exp (u : ℂ) * (ζ : ℂ) = t) :
    diagGL z 1 = diagGL t t * (splitTorusGL2Complex (u : ℂ) * circleGL2 ζ) := by
  have ht0 : (t : ℂ) ≠ 0 := t.ne_zero
  have h11 : (t : ℂ) * (Complex.exp (-(u : ℂ)) * ((ζ : ℂ))⁻¹) = 1 := by
    rw [Complex.exp_neg, ← mul_inv, huζ, mul_inv_cancel₀ ht0]
  have h11' : (t : ℂ) * (Complex.exp (-(u : ℂ)) * ((ζ⁻¹ : ℂˣ) : ℂ)) = 1 := by
    rw [Units.val_inv_eq_inv_val]; exact h11
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, Units.val_mul]
  fin_cases i <;> fin_cases j <;>
    simp [diagGL, splitTorusGL2Complex, circleGL2, Matrix.mul_apply, Fin.sum_univ_two, ← ht, sq]
  · exact huζ.symm
  · exact h11.symm

theorem eq_bprime_mul_archUnitHom (w : InfinitePlace K) (b a : (AdeleRing (𝓞 K) K)ˣ)
    (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') :
    a = bprime w b * archUnitHom w (infiniteUnitsComponent (𝓞 K) K w a) := by
  apply Units.ext
  refine Prod.ext (funext fun v => ?_) ?_
  · show ((a : AdeleRing (𝓞 K) K)).1 v = ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v *
      ((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w a) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v
    rw [archUnitHom_apply]
    by_cases hv : v = w
    · subst hv
      rw [bprime_fst_self, one_mul]
      show _ = Function.update (1 : InfiniteAdeleRing K) v _ v
      rw [Function.update_self]; rfl
    · rw [bprime_fst_of_ne hv, hab v hv]
      show _ = _ * Function.update (1 : InfiniteAdeleRing K) w _ v
      rw [Function.update_of_ne hv]
      exact (mul_one _).symm
  · show ((a : AdeleRing (𝓞 K) K)).2 = ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 *
      ((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w a) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
    rw [bprime_snd, hb, ha, archUnitHom_apply]
    exact (mul_one _).symm

theorem glFin_diagOne_of_snd_eq_one (t : (AdeleRing (𝓞 K) K)ˣ) (ht : ((t : AdeleRing (𝓞 K) K)).2 = 1) :
    glFin (𝓞 K) K (diagOne t) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glFin_apply]
  change ((Matrix.diagonal ![(t : AdeleRing (𝓞 K) K), 1] i j).2) = ((1 : Matrix (Fin 2) (Fin 2) _) i j)
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ht] <;> rfl

theorem diagOne_archUnitHom_eq_archComplexGLAt {w : InfinitePlace K} (hw : w.IsComplex) (c : (w.Completion)ˣ) :
    (diagOne (archUnitHom w c) : AdelicGL2 (𝓞 K) K) =
      archComplexGLAt hw (diagGL (Units.map (eC hw).toRingHom.toMonoidHom c) 1) := by
  set m : GL (Fin 2) ℂ := diagGL (Units.map (eC hw).toRingHom.toMonoidHom c) 1 with hm
  have hfin : glFin (𝓞 K) K (archComplexGLAt hw m) = 1 := glFin_adelicArchGLIncl K _
  have harch : glArch (𝓞 K) K (archComplexGLAt hw m) =
      archGLIncl K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m) := glArch_adelicArchGLIncl K _
  have hsnd : (((archUnitHom w c : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 = 1 := by rw [archUnitHom_apply]; rfl
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [harch]
    refine glInf_ext K fun v => ?_
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archGLIncl_self]
      ext i j
      rw [archComponent_apply, glArch_apply, glEquivOfRingEquiv_apply_entry]
      change ((Matrix.diagonal ![(((archUnitHom v c : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K), 1] i j).1 v) = _
      rw [archUnitHom_apply]
      fin_cases i <;> fin_cases j
      · simp [Matrix.diagonal, hm, diagGL]
        show Function.update (1 : InfiniteAdeleRing K) v (c : v.Completion) v = _
        rw [Function.update_self]
        exact ((eC hw).symm_apply_apply _).symm
      · simp [Matrix.diagonal, hm, diagGL]; rfl
      · simp [Matrix.diagonal, hm, diagGL]; rfl
      · simp [Matrix.diagonal, hm, diagGL]; rfl
    · rw [archComponent_archGLIncl_of_ne K hv]
      ext i j
      rw [archComponent_apply, glArch_apply]
      change ((Matrix.diagonal ![(((archUnitHom w c : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K), 1] i j).1 v) =
        (1 : Matrix (Fin 2) (Fin 2) _) i j
      rw [archUnitHom_apply]
      fin_cases i <;> fin_cases j
      · simp [Matrix.diagonal]
        show Function.update (1 : InfiniteAdeleRing K) w (c : w.Completion) v = 1
        rw [Function.update_of_ne hv]; rfl
      · simp [Matrix.diagonal]; rfl
      · simp [Matrix.diagonal]; rfl
      · simp [Matrix.diagonal]; rfl
  · rw [hfin, glFin_diagOne_of_snd_eq_one K _ hsnd]

theorem centralScalar_iotaW_eq_archComplexGLAt {w : InfinitePlace K} (hw : w.IsComplex) (t : ℂˣ) :
    centralScalar (𝓞 K) K (iotaW hw t) = archComplexGLAt hw (diagGL t t) := by
  set m : GL (Fin 2) ℂ := diagGL t t with hm
  have hfin : glFin (𝓞 K) K (archComplexGLAt hw m) = 1 := glFin_adelicArchGLIncl K _
  have harch : glArch (𝓞 K) K (archComplexGLAt hw m) =
      archGLIncl K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m) := glArch_adelicArchGLIncl K _
  have hι : iotaW hw t = archUnitHom w (Units.map (eC hw).symm.toRingHom.toMonoidHom t) := rfl
  have hmat : ((centralScalar (𝓞 K) K (iotaW hw t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      Matrix.diagonal ![((iotaW hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), ((iotaW hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)] := by
    ext i j
    change (Matrix.scalar (Fin 2) ((iotaW hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) i j = _
    rw [Matrix.scalar_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [harch]
    refine glInf_ext K fun v => ?_
    ext i j
    rw [archComponent_apply, glArch_apply, hmat, hι, archUnitHom_apply]
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archGLIncl_self, glEquivOfRingEquiv_apply_entry]
      fin_cases i <;> fin_cases j
      · simp [Matrix.diagonal, hm, diagGL]
        show Function.update (1 : InfiniteAdeleRing K) v _ v = _
        rw [Function.update_self]; rfl
      · simp [Matrix.diagonal, hm, diagGL]; rfl
      · simp [Matrix.diagonal, hm, diagGL]; rfl
      · simp [Matrix.diagonal, hm, diagGL]
        show Function.update (1 : InfiniteAdeleRing K) v _ v = _
        rw [Function.update_self]; rfl
    · rw [archComponent_archGLIncl_of_ne K hv]
      fin_cases i <;> fin_cases j
      · simp [Matrix.diagonal]
        show Function.update (1 : InfiniteAdeleRing K) w _ v = 1
        rw [Function.update_of_ne hv]; rfl
      · simp [Matrix.diagonal]; rfl
      · simp [Matrix.diagonal]; rfl
      · simp [Matrix.diagonal]
        show Function.update (1 : InfiniteAdeleRing K) w _ v = 1
        rw [Function.update_of_ne hv]; rfl
  · rw [hfin]
    ext i j
    rw [glFin_apply, hmat, hι, archUnitHom_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> rfl

end E40DCFN

namespace E40DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    g * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) ((z : AdeleRing (𝓞 K) K)) =
    Matrix.scalar (Fin 2) ((z : AdeleRing (𝓞 K) K)) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
  exact ((Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq).symm

theorem whittakerCoefficient_centralScalar_mul (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (z : (AdeleRing (𝓞 K) K)ˣ) (c : ℂ)
    (hZ : ∀ g, φ (centralScalar (𝓞 K) K z * g) = c * φ g) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (centralScalar (𝓞 K) K z * g) = c * whittakerCoefficient K pins ψ φ α g := by
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1
  funext u
  rw [← mul_assoc, centralScalar_comm, mul_assoc, hZ]
  ring

theorem iotaW_snd {w : InfinitePlace K} (hw : w.IsComplex) (t : ℂˣ) :
    ((iotaW hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := rfl

theorem iotaW_fst_self {w : InfinitePlace K} (hw : w.IsComplex) (t : ℂˣ) :
    ((iotaW hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = (eC hw).symm t := by
  show Function.update (1 : InfiniteAdeleRing K) w _ w = _
  rw [Function.update_self]; rfl

theorem iotaW_fst_of_ne {w v : InfinitePlace K} (hw : w.IsComplex) (hv : v ≠ w) (t : ℂˣ) :
    ((iotaW hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v = ((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v := by
  show Function.update (1 : InfiniteAdeleRing K) w _ v = _
  rw [Function.update_of_ne hv]; rfl

theorem ideleNorm_iotaW {w : InfinitePlace K} (hw : w.IsComplex) (t : ℂˣ) :
    ideleNorm K (iotaW hw t) = ‖(t : ℂ)‖ ^ 2 := by
  rw [ideleNorm_eq_norm_pow_mul_of_eq_off K w 1 (iotaW hw t) (iotaW_snd K hw t) (fun v hv => iotaW_fst_of_ne K hw hv t),
    iotaW_fst_self, norm_eC_symm, mult_eq_two_of_isComplex K hw]
  have : ∏ w' ∈ Finset.univ.erase w, ‖(((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w'‖ ^ w'.mult = 1 :=
    Finset.prod_eq_one fun w' _ => by
      have : (((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w' = 1 := rfl
      rw [this, norm_one, one_pow]
  rw [this, mul_one]

theorem diagOne_eq_central_mul_g0_mul (w : InfinitePlace K) (hw : w.IsComplex) (b a : (AdeleRing (𝓞 K) K)ˣ)
    (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w')
    (t ζ : ℂˣ) (u : ℝ) (ht : (t : ℂ) ^ 2 = eC hw (((a : AdeleRing (𝓞 K) K)).1 w))
    (huζ : Complex.exp (u : ℂ) * (ζ : ℂ) = t) :
    (diagOne a : AdelicGL2 (𝓞 K) K) =
      centralScalar (𝓞 K) K (iotaW hw t) * (g0 w b * archComplexGLAt hw (splitTorusGL2Complex (u : ℂ) * circleGL2 ζ)) := by
  set c : (w.Completion)ˣ := infiniteUnitsComponent (𝓞 K) K w a with hc
  set z : ℂˣ := Units.map (eC hw).toRingHom.toMonoidHom c with hz
  have hz' : (z : ℂ) = eC hw (((a : AdeleRing (𝓞 K) K)).1 w) := rfl
  have hdec := diagGL_eq_scalar_mul_split_mul_circle z t ζ u (by rw [ht, hz']) huζ
  calc (diagOne a : AdelicGL2 (𝓞 K) K)
      = diagOne (bprime w b) * diagOne (archUnitHom w c) := by
          rw [← map_mul, ← eq_bprime_mul_archUnitHom K w b a ha hb hab]
    _ = g0 w b * archComplexGLAt hw (diagGL z 1) := by rw [diagOne_archUnitHom_eq_archComplexGLAt K hw c]; rfl
    _ = g0 w b * (centralScalar (𝓞 K) K (iotaW hw t) * archComplexGLAt hw (splitTorusGL2Complex (u : ℂ) * circleGL2 ζ)) := by
          rw [hdec, map_mul, centralScalar_iotaW_eq_archComplexGLAt]
    _ = centralScalar (𝓞 K) K (iotaW hw t) * (g0 w b * archComplexGLAt hw (splitTorusGL2Complex (u : ℂ) * circleGL2 ζ)) := by
          rw [← mul_assoc, centralScalar_comm, mul_assoc]

theorem norm_W_diagOne_eq_rpow_mul_norm_fstr (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') :
    ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
        (diagOne a)‖ =
      ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ w₀ * ‖fstr D hw b x p ‖((a : AdeleRing (𝓞 K) K)).1 w‖‖ := by

  set r : ℝ := ‖((a : AdeleRing (𝓞 K) K)).1 w‖ with hr
  have hzr : ‖eC hw (((a : AdeleRing (𝓞 K) K)).1 w)‖ = r := norm_eC K hw _
  have hr0 : 0 < r := by
    have h := congrArg (fun q : AdeleRing (𝓞 K) K => q.1 w) a.mul_inv
    change ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 at h
    exact norm_pos_iff.2 (left_ne_zero_of_mul_eq_one h)
  have hz0 : eC hw (((a : AdeleRing (𝓞 K) K)).1 w) ≠ 0 := fun h0 => by rw [h0, norm_zero] at hzr; exact hr0.ne' hzr.symm
  set t₀ : ℂ := (eC hw (((a : AdeleRing (𝓞 K) K)).1 w)) ^ ((2 : ℂ)⁻¹) with ht₀
  have ht₀sq : t₀ ^ 2 = eC hw (((a : AdeleRing (𝓞 K) K)).1 w) := by
    rw [ht₀]
    exact_mod_cast Complex.cpow_nat_inv_pow _ two_ne_zero
  have ht₀0 : t₀ ≠ 0 := fun h0 => hz0 (by rw [← ht₀sq, h0]; norm_num)
  have hnt : ‖t₀‖ ^ 2 = r := by rw [← norm_pow, ht₀sq, hzr]
  have hnt0 : 0 < ‖t₀‖ := norm_pos_iff.2 ht₀0
  set t : ℂˣ := Units.mk0 t₀ ht₀0 with htdef
  set ζ₀ : ℂ := t₀ / (‖t₀‖ : ℂ) with hζ₀
  have hζ₀0 : ζ₀ ≠ 0 := div_ne_zero ht₀0 (by exact_mod_cast hnt0.ne')
  have hζ₀1 : ‖ζ₀‖ = 1 := by rw [hζ₀, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnt0, div_self hnt0.ne']
  set ζ : ℂˣ := Units.mk0 ζ₀ hζ₀0 with hζdef
  set u : ℝ := Real.log r / 2 with hu
  have hexp : Real.exp u = ‖t₀‖ := by
    have h1 : Real.exp u = r ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos hr0, hu]; congr 1; ring
    rw [h1, ← hnt, ← Real.sqrt_eq_rpow, Real.sqrt_sq hnt0.le]
  have huζ : Complex.exp (u : ℂ) * (ζ : ℂ) = t := by
    show Complex.exp (u : ℂ) * ζ₀ = t₀
    rw [← Complex.ofReal_exp, hexp, hζ₀, mul_div_cancel₀ _ (by exact_mod_cast hnt0.ne')]

  have hgeo := diagOne_eq_central_mul_g0_mul K w hw b a ha hb hab t ζ u ht₀sq huζ
  have hval : whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
        (diagOne a) = ((ξ ⟨iotaW hw t, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * ((ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * fstr D hw b x p r) := by
    rw [hgeo, whittakerCoefficient_centralScalar_mul K _ _ (x p) 1 (iotaW hw t) _ (hxZ p (iotaW hw t))]
    congr 1
    have h5 := Fstr_mul_circleGL2 K D hw b x hwt p ζ hζ₀1 (splitTorusGL2Complex (u : ℂ))
    unfold Fstr W at h5
    rw [h5]
    congr 1
    unfold fstr
    rw [dif_pos p.2]
    rfl

  have hNι : NumberField.TateGlobal.ideleNorm K (iotaW hw t) = r := by
    rw [ideleNorm_iotaW K hw t]; exact hnt
  have hζ1 : ‖(ζ : ℂ)‖ = 1 := hζ₀1
  rw [hval, norm_mul, norm_mul, hξ, hNι, norm_zpow, hζ1, one_zpow, one_mul]

theorem rpow_eq_rpow_mult {w : InfinitePlace K} (hw : w.IsComplex) (r w₀ : ℝ) :
    r ^ w₀ = r ^ ((w.mult : ℝ) * w₀ / 2) := by
  rw [mult_eq_two_of_isComplex K hw]; congr 1; push_cast; ring

theorem exists_norm_fstr_le (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (hgr : ∀ p, ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → ‖fstr D hw b x p y‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_W_diagOne_le_norm_rpow_of_gr K D w₀ w x hgr b
  refine ⟨C, hC0, fun p y hy => ?_⟩

  have hy0 : (eC hw).symm (y : ℂ) ≠ 0 := by
    intro h0
    have := congrArg (eC hw) h0
    rw [RingEquiv.apply_symm_apply, map_zero] at this
    exact hy.ne' (by exact_mod_cast this)
  set cy : (w.Completion)ˣ := Units.mk0 ((eC hw).symm (y : ℂ)) hy0 with hcy
  set a : (AdeleRing (𝓞 K) K)ˣ := bprime w b * archUnitHom w cy with hadef
  have ha2 : ((a : AdeleRing (𝓞 K) K)).2 = 1 := by
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1
    rw [bprime_snd, hb, archUnitHom_apply, one_mul]; rfl
  have haw : ((a : AdeleRing (𝓞 K) K)).1 w = (eC hw).symm (y : ℂ) := by
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = _
    rw [bprime_fst_self, one_mul, archUnitHom_apply]
    show Function.update (1 : InfiniteAdeleRing K) w (cy : w.Completion) w = _
    rw [Function.update_self]; rfl
  have hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w' := by
    intro w' hw'
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' = _
    rw [bprime_fst_of_ne hw', archUnitHom_apply]
    show _ * Function.update (1 : InfiniteAdeleRing K) w (cy : w.Completion) w' = _
    rw [Function.update_of_ne hw']; exact mul_one _
  have hnorm : ‖((a : AdeleRing (𝓞 K) K)).1 w‖ = y := by
    rw [haw, norm_eC_symm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have h7 := norm_W_diagOne_eq_rpow_mul_norm_fstr K D ξ w₀ hξ w hw n x hxZ hwt b hb p a ha2 hab
  have h8 := hC p a ha2 hab
  rw [h7, hnorm, ← rpow_eq_rpow_mult K hw] at h8

  have hyw : 0 < y ^ w₀ := Real.rpow_pos_of_pos hy _
  rw [mul_comm C] at h8
  exact le_of_mul_le_mul_left h8 hyw

end E40DCFN

namespace E40IFC

open E40DCFN NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

theorem g0_comm {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ) (m : GL (Fin 2) ℂ) :
    archComplexGLAt hw m * g0 w b = g0 w b * archComplexGLAt hw m :=
  archComplexGLAt_mul_g0 K hw b m

theorem hM_string (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p)) :
    ∀ (p : Fin (n + 1)) (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ,
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (h * circleGL2 ζ)) =
        (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw h) := by
  intro p ζ hζ h
  have h5 := Fstr_mul_circleGL2 K D hw b x hwt p ζ hζ h
  unfold Fstr W at h5
  exact h5

theorem twist (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') :
    ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne a)‖ =
      ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log ‖((a : AdeleRing (𝓞 K) K)).1 w‖ / 2 : ℝ) : ℂ)))‖ := by
  have h7 := norm_W_diagOne_eq_rpow_mul_norm_fstr K D ξ w₀ hξ w hw n x hxZ hwt b hb p a ha hab
  rw [h7, ← rpow_eq_rpow_mult K hw]
  congr 2
  unfold fstr
  rw [dif_pos p.2]
  rfl

theorem large (D : Set (AdelicGL2 (𝓞 K) K)) (w₀ : ℝ) {w : InfinitePlace K} (hw : w.IsComplex)
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hgr : ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) :
    ∃ B : ℝ, ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
      (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne a)‖ ≤ B * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) := by
  obtain ⟨C, -, hC⟩ := exists_norm_W_diagOne_le_norm_rpow_of_gr K D w₀ w (n := 0) (fun _ => φ) (fun _ => hgr) b
  exact ⟨C, fun a ha hab => hC 0 a ha hab⟩

theorem bounded (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      φ (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g)
    (hgr : ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) :
    ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ)))‖ ≤ B := by
  obtain ⟨B, hB⟩ := large D w₀ hw b hb φ hgr
  refine ⟨B, fun y hy _ => ?_⟩

  have hy0 : (eC hw).symm (y : ℂ) ≠ 0 := by
    intro h0
    have := congrArg (eC hw) h0
    rw [RingEquiv.apply_symm_apply, map_zero] at this
    exact hy.ne' (by exact_mod_cast this)
  set cy : (w.Completion)ˣ := Units.mk0 ((eC hw).symm (y : ℂ)) hy0 with hcy
  set a : (AdeleRing (𝓞 K) K)ˣ := bprime w b * archUnitHom w cy with hadef
  have ha2 : ((a : AdeleRing (𝓞 K) K)).2 = 1 := by
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1
    rw [bprime_snd, hb, archUnitHom_apply, one_mul]; rfl
  have haw : ((a : AdeleRing (𝓞 K) K)).1 w = (eC hw).symm (y : ℂ) := by
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = _
    rw [bprime_fst_self, one_mul, archUnitHom_apply]
    show Function.update (1 : InfiniteAdeleRing K) w (cy : w.Completion) w = _
    rw [Function.update_self]; rfl
  have hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w' := by
    intro w' hw'
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' = _
    rw [bprime_fst_of_ne hw', archUnitHom_apply]
    show _ * Function.update (1 : InfiniteAdeleRing K) w (cy : w.Completion) w' = _
    rw [Function.update_of_ne hw']; exact mul_one _
  have heCa : eC hw (((a : AdeleRing (𝓞 K) K)).1 w) = (y : ℂ) := by rw [haw, RingEquiv.apply_symm_apply]
  have hnorm : ‖((a : AdeleRing (𝓞 K) K)).1 w‖ = y := by
    rw [haw, norm_eC_symm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]

  have hsy0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have ht0 : ((Real.sqrt y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsy0.ne'
  set t : ℂˣ := Units.mk0 ((Real.sqrt y : ℝ) : ℂ) ht0 with htdef
  have htsq : (t : ℂ) ^ 2 = eC hw (((a : AdeleRing (𝓞 K) K)).1 w) := by
    rw [heCa]; show ((Real.sqrt y : ℝ) : ℂ) ^ 2 = (y : ℂ)
    rw [← Complex.ofReal_pow, Real.sq_sqrt hy.le]
  have huζ : Complex.exp (((Real.log y / 2 : ℝ)) : ℂ) * ((1 : ℂˣ) : ℂ) = t := by
    rw [Units.val_one, mul_one, ← Complex.ofReal_exp]
    show ((Real.exp (Real.log y / 2) : ℝ) : ℂ) = ((Real.sqrt y : ℝ) : ℂ)
    congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]; congr 1; ring
  have hgeo := diagOne_eq_central_mul_g0_mul K w hw b a ha2 hb hab t 1 (Real.log y / 2) htsq huζ
  rw [circleGL2_one, mul_one] at hgeo
  have hval : whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) φ 1
        (diagOne a) = ((ξ ⟨iotaW hw t, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ))) := by
    rw [hgeo, whittakerCoefficient_centralScalar_mul K _ _ φ 1 (iotaW hw t) _ (hφZ (iotaW hw t))]
  have hNι : NumberField.TateGlobal.ideleNorm K (iotaW hw t) = y := by
    rw [ideleNorm_iotaW K hw t]
    show ‖((Real.sqrt y : ℝ) : ℂ)‖ ^ 2 = y
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsy0, Real.sq_sqrt hy.le]
  have h8 := hB a ha2 hab
  rw [hval, norm_mul, hξ, hNι, hnorm, ← rpow_eq_rpow_mult K hw, mul_comm B] at h8
  exact le_of_mul_le_mul_left h8 (Real.rpow_pos_of_pos hy _)

end E40IFC

namespace E40IFC

open E40DCFN

variable {K : Type} [Field K] [NumberField K]

theorem hCas_string (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (hxc : ∀ p, Continuous (x p))
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p)))
    (lam lam' : ℂ)
    (hcas : ∀ p, archCasimirAtComplex hw (x p) = lam • x p ∧ archCasimirBarAtComplex hw (x p) = lam' • x p) :
    (∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .H (x p))) 1 (g0 w b * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .iH (x p))) 1 (g0 w b * archComplexGLAt hw h)) -
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .H (x p))) 1 (g0 w b * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 (g0 w b * archComplexGLAt hw h))))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (x p)) 1 (g0 w b * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (x p)) 1 (g0 w b * archComplexGLAt hw h))) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm (x p))) 1 (g0 w b * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm (x p))) 1 (g0 w b * archComplexGLAt hw h)) -
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm (x p))) 1 (g0 w b * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 (g0 w b * archComplexGLAt hw h))))) = lam * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .H (x p))) 1 (g0 w b * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .iH (x p))) 1 (g0 w b * archComplexGLAt hw h)) +
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .H (x p))) 1 (g0 w b * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 (g0 w b * archComplexGLAt hw h))))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (x p)) 1 (g0 w b * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (x p)) 1 (g0 w b * archComplexGLAt hw h))) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm (x p))) 1 (g0 w b * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm (x p))) 1 (g0 w b * archComplexGLAt hw h)) +
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm (x p))) 1 (g0 w b * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 (g0 w b * archComplexGLAt hw h))))) = lam' * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw h)) := by
  have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).continuous

  have hcw : ∀ (p : Fin (n + 1)) (j : Fin 10), Continuous (casWords hw (x p) j) := by
    intro p j
    have h2 : ∀ a b' : ArchDirComplex, Continuous (archDerivAtComplex hw a (archDerivAtComplex hw b' (x p))) :=
      fun a b' => by simpa only [List.foldr] using (hreg p [a, b']).2
    have h1 : ∀ a : ArchDirComplex, Continuous (archDerivAtComplex hw a (x p)) :=
      fun a => by simpa only [List.foldr] using (hreg p [a]).2
    fin_cases j <;> simp only [casWords, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.head_cons,
      Fin.isValue] <;> first | exact h2 _ _ | exact h1 _
  have hsm : ∀ p : Fin (n + 1), IsArchSmoothAtComplex hw (x p) := fun p => by simpa only [List.foldr] using (hreg p []).1

  have hWsmul : ∀ (p : Fin (n + 1)) (c : ℂ) (g : AdelicGL2 (𝓞 K) K),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (c • x p) 1 g = c * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g := by
    intro p c g
    have h := AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ 1 (fun _ => x p) (fun _ => hxc p) (fun _ => c) 1 g
    simp only [Fin.sum_univ_one] at h
    rw [show (c • x p) = fun g' => c * x p g' from funext fun g' => by simp [Pi.smul_apply, smul_eq_mul]]
    exact h
  have hWsum : ∀ (p : Fin (n + 1)) (cf : Fin 10 → ℂ) (g : AdelicGL2 (𝓞 K) K),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (fun g' => ∑ j : Fin 10, cf j * casWords hw (x p) j g') 1 g =
        ∑ j : Fin 10, cf j * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (casWords hw (x p) j) 1 g := fun p cf g =>
    AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ 10 (casWords hw (x p)) (hcw p) cf 1 g
  constructor
  · intro p h
    set g : AdelicGL2 (𝓞 K) K := g0 w b * archComplexGLAt hw h with hg
    have key : ∑ j : Fin 10, casCoeff j * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (casWords hw (x p) j) 1 g = lam * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g := by
      rw [← hWsum, ← hWsmul, ← archCasimirAtComplex_eq_sum hw (hsm p), (hcas p).1]
    rw [← key]
    simp only [casCoeff, casWords, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.head_cons, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    linear_combination (-(1 / 16 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 g -
      (1 / 4 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 g) * Complex.I_sq
  · intro p h
    set g : AdelicGL2 (𝓞 K) K := g0 w b * archComplexGLAt hw h with hg
    have key : ∑ j : Fin 10, casBarCoeff j * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (casWords hw (x p) j) 1 g = lam' * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g := by
      rw [← hWsum, ← hWsmul, ← archCasimirBarAtComplex_eq_sum hw (hsm p), (hcas p).2]
    rw [← key]
    simp only [casBarCoeff, casWords, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.head_cons, Fin.isValue, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    linear_combination (-(1 / 16 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 g -
      (1 / 4 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 g) * Complex.I_sq

end E40IFC

namespace E37K

variable (K : Type) [Field K] [NumberField K]

theorem whittakerCoefficient_mul_right (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (g k : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * k) = whittakerCoefficient K pins ψ (fun y => φ (y * k)) α g := by
  letI := pins.nS
  simp only [whittakerCoefficient, mul_assoc]

theorem archComplexGLAt_eq_lift_rot {w : InfinitePlace K} (hw : w.IsComplex) (s : ℝ) (k : GL (Fin 2) ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s]) :
    archComplexGLAt hw k =
      archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)] := by
  have hmat : (Matrix.of !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ) =
      (k : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ofReal_cos, Complex.ofReal_sin]
  have hdet : (Matrix.of !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [hmat, ← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  rw [archComplexLiftAt_of_det_ne_zero hw hdet]
  congr 1
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hmat]

theorem archComplexGLAt_eq_lift_irot {w : InfinitePlace K} (hw : w.IsComplex) (s : ℝ) (k : GL (Fin 2) ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s]) :
    archComplexGLAt hw k =
      archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)] := by
  have hmat : (Matrix.of !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hk]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ofReal_cos, Complex.ofReal_sin, mul_comm]
  have hdet : (Matrix.of !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [hmat, ← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  rw [archComplexLiftAt_of_det_ne_zero hw hdet]
  congr 1
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hmat]

theorem hK_of_string (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (g₀ : AdelicGL2 (𝓞 K) K)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (hxc : ∀ p, Continuous (x p))
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) =
        ∑ p' : Fin (n + 1), E₁ s p' p * x p' g)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) =
        ∑ p' : Fin (n + 1), E₂ s p' p * x p' g) :
    (∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s] →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * k)) =
          ∑ p' : Fin (n + 1), E₁ s p' p * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p') 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s] →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * k)) =
          ∑ p' : Fin (n + 1), E₂ s p' p * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p') 1 (g₀ * archComplexGLAt hw h)) := by
  have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).continuous
  constructor
  · intro p s h k hk
    rw [map_mul, ← mul_assoc, whittakerCoefficient_mul_right, archComplexGLAt_eq_lift_rot K hw s k hk]
    rw [show (fun y => x p (y * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)])) =
        fun y => ∑ p' : Fin (n + 1), E₁ s p' p * x p' y from funext fun y => hK₁ p s y]
    exact AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ (n + 1) x hxc (fun p' => E₁ s p' p) 1 _
  · intro p s h k hk
    rw [map_mul, ← mul_assoc, whittakerCoefficient_mul_right, archComplexGLAt_eq_lift_irot K hw s k hk]
    rw [show (fun y => x p (y * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)])) =
        fun y => ∑ p' : Fin (n + 1), E₂ s p' p * x p' y from funext fun y => hK₂ p s y]
    exact AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ (n + 1) x hxc (fun p' => E₂ s p' p) 1 _

theorem final_bound (V C B w₀ δ r : ℝ) (hr : 0 < r) (hδ : 0 ≤ δ)
    (hsmall : r ≤ 1 → V ≤ C * r ^ w₀ * r ^ δ) (hlarge : V ≤ B * r ^ w₀) :
    V ≤ max C B * r ^ ((2 : ℝ) * w₀ / 2) * (min 1 r) ^ δ := by
  rw [show (2 : ℝ) * w₀ / 2 = w₀ by ring]
  have hrw : 0 ≤ r ^ w₀ := Real.rpow_nonneg hr.le _
  by_cases h1 : r ≤ 1
  · rw [min_eq_right h1]
    have hrδ : 0 ≤ r ^ δ := Real.rpow_nonneg hr.le _
    calc V ≤ C * r ^ w₀ * r ^ δ := hsmall h1
      _ ≤ max C B * r ^ w₀ * r ^ δ := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C B) hrw) hrδ
          exact this
  · rw [min_eq_left (le_of_lt (not_le.mp h1)), Real.one_rpow, mul_one]
    calc V ≤ B * r ^ w₀ := hlarge
      _ ≤ max C B * r ^ w₀ := mul_le_mul_of_nonneg_right (le_max_right C B) hrw

end E37K

namespace E43Z

open E40DCFN NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

def uW {w : InfinitePlace K} (hw : w.IsComplex) (z : ℂ) : AdeleRing (𝓞 K) K :=
  (show (AdeleRing (𝓞 K) K) from (Pi.single w ((ringEquivComplexOfIsComplex hw).symm z), 0))

theorem coe_archComplexGLAt {w : InfinitePlace K} (hw : w.IsComplex) (m : GL (Fin 2) ℂ) :
    ((archComplexGLAt hw m : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      Matrix.of fun i j => (archMatrixUpdate K w ((m : Matrix (Fin 2) (Fin 2) ℂ).map (ringEquivComplexOfIsComplex hw).symm) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) :=
  rfl

theorem archComplexGLAt_unipotentGL2 {w : InfinitePlace K} (hw : w.IsComplex) (t : ℂ) :
    archComplexGLAt hw (unipotentGL2 t) = unipotentGL2 (uW hw t) := by
  apply Units.ext
  rw [coe_archComplexGLAt, unipotentGL2_coe]
  ext i j
  ·
    show (archMatrixUpdate K w (((unipotentGL2 t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map
        (ringEquivComplexOfIsComplex hw).symm) i j) = ((!![(1 : AdeleRing (𝓞 K) K), uW hw t; 0, 1]) i j).1
    funext v
    by_cases hv : v = w
    · subst hv
      rw [archMatrixUpdate_apply_self, Matrix.map_apply, unipotentGL2_coe]
      fin_cases i <;> fin_cases j <;> simp [uW] <;> rfl
    · rw [archMatrixUpdate_apply_of_ne K _ _ i j hv]
      fin_cases i <;> fin_cases j <;> simp [uW, Pi.single_eq_of_ne hv] <;> rfl
  ·
    fin_cases i <;> fin_cases j <;> simp [uW] <;> rfl

theorem stdAddChar_principalInvariant : IsPrincipalInvariantAddChar K (NumberField.StandardAddChar.stdAddChar K) :=
  (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).principalInvariant

theorem unipotentGL2_algebraMap_eq_globalPoints (β : K) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) = globalPoints (𝓞 K) K (unipotentGL2 β) := by
  refine Units.ext ?_
  ext i j
  simp only [unipotentGL2_coe, globalPoints, Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp

private theorem _root_.E43Z.W_eq_zero_of_sl2_invariant (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (hZ : ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℂ), Matrix.GeneralLinearGroup.det h = 1 → φ (g * archComplexGLAt hw h) = φ g)
    (hcomm : ∀ m : GL (Fin 2) ℂ, archComplexGLAt hw m * g0 w b = g0 w b * archComplexGLAt hw m) (h : GL (Fin 2) ℂ) :
    whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g0 w b * archComplexGLAt hw h) = 0 := by
  set g : AdelicGL2 (𝓞 K) K := g0 w b * archComplexGLAt hw h with hg

  have hii : ∀ t : ℂ, whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (unipotentGL2 (uW hw t) * g) = whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g) := by
    intro t
    letI := (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS
    simp only [whittakerCoefficient]
    congr 1
    funext x
    congr 1
    have hconj : g⁻¹ * archComplexGLAt hw (unipotentGL2 t) * g =
        archComplexGLAt hw (h⁻¹ * unipotentGL2 t * h) := by
      rw [hg, mul_inv_rev, map_mul, map_mul, map_inv]
      calc (archComplexGLAt hw h)⁻¹ * (g0 w b)⁻¹ * archComplexGLAt hw (unipotentGL2 t) * (g0 w b * archComplexGLAt hw h)
          = (archComplexGLAt hw h)⁻¹ * ((g0 w b)⁻¹ * (archComplexGLAt hw (unipotentGL2 t) * g0 w b)) * archComplexGLAt hw h := by
            simp only [mul_assoc]
        _ = (archComplexGLAt hw h)⁻¹ * archComplexGLAt hw (unipotentGL2 t) * archComplexGLAt hw h := by
            rw [hcomm, ← mul_assoc (g0 w b)⁻¹, inv_mul_cancel, one_mul]
    have hdet : Matrix.GeneralLinearGroup.det (h⁻¹ * unipotentGL2 t * h) = 1 := by
      rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
      apply Units.ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two]
    calc φ (unipotentGL2 x * (unipotentGL2 (uW hw t) * g))
        = φ ((unipotentGL2 x * g) * (g⁻¹ * archComplexGLAt hw (unipotentGL2 t) * g)) := by
          rw [← archComplexGLAt_unipotentGL2]; congr 1; group
      _ = φ (unipotentGL2 x * g) := by rw [hconj]; exact hZ _ _ hdet

  have hi : ∀ t : ℂ, whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (unipotentGL2 (uW hw t) * g) =
      NumberField.StandardAddChar.stdAddChar K (uW hw t) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g) := by
    intro t
    have h := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (NumberField.StandardAddChar.stdAddChar K) stdAddChar_principalInvariant φ g
      (fun β u => by rw [unipotentGL2_add, unipotentGL2_algebraMap_eq_globalPoints, mul_assoc, hφG]) 1 (uW hw t)
    rwa [map_one, one_mul] at h

  have hval : NumberField.StandardAddChar.stdAddChar K (uW hw (1 / 4 : ℂ)) = -1 := by
    have h := NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex K w hw (1 / 4 : ℂ)
    rw [show uW hw (1 / 4 : ℂ) = (show (AdeleRing (𝓞 K) K) from (Pi.single w ((ringEquivComplexOfIsComplex hw).symm (1 / 4 : ℂ)), 0)) from rfl, h]
    have hre : (2 * (1 / 4 : ℂ).re : ℝ) = 1 / 2 := by norm_num
    rw [hre]
    push_cast
    rw [show (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (1 / 2) = (Real.pi : ℂ) * Complex.I by ring, Complex.exp_pi_mul_I]
  have h1 := hi (1 / 4 : ℂ)
  rw [hii, hval] at h1

  have : (2 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g) = 0 := by linear_combination h1
  exact (mul_eq_zero.mp this).resolve_left two_ne_zero

p2m_export "E43Z" "W_eq_zero_of_sl2_invariant"
end E43Z

namespace E40IFC

open E40DCFN

variable {K : Type} [Field K] [NumberField K]

private theorem _root_.E40IFC.W_eq_zero_of_sl2_invariant (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K γ * g) = φ g)
    (hZ : ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℂ), Matrix.GeneralLinearGroup.det h = 1 → φ (g * archComplexGLAt hw h) = φ g)
    (hcomm : ∀ m : GL (Fin 2) ℂ, archComplexGLAt hw m * g0 w b = g0 w b * archComplexGLAt hw m) (h : GL (Fin 2) ℂ) :
    whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g0 w b * archComplexGLAt hw h) = 0 :=
  E43Z.W_eq_zero_of_sl2_invariant D hw b φ hφG hZ hcomm h

p2m_export "E40IFC" "W_eq_zero_of_sl2_invariant"
end E40IFC

open scoped Real

namespace E41DISPATCH

open Real Set

theorem bdd_Icc (f : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (a b : ℝ) (ha : 0 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Set.Icc a b, ‖f y‖ ≤ M := by
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le ha hy.1
  have hcont : ContinuousOn f (Set.Icc a b) := (hf.continuousOn).mono hsub
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hcont).isBounded.exists_norm_le
  exact ⟨max M 0, le_max_right _ _, fun y hy => (hM _ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩

theorem extend_bdd (f : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (L B : ℝ)
    (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ B) :
    ∃ B' : ℝ, 0 ≤ B' ∧ ∀ y : ℝ, 0 < y → y ≤ L → ‖f y‖ ≤ B' := by
  obtain ⟨M, hM0, hM⟩ := bdd_Icc f hf 1 L one_pos
  refine ⟨max B 0 + M, by positivity, fun y hy hyL => ?_⟩
  rcases le_or_gt y 1 with h1 | h1
  · exact (hB y hy h1).trans ((le_max_left _ _).trans (by linarith))
  · exact (hM y ⟨h1.le, hyL⟩).trans (by linarith [le_max_right B 0])

theorem rpow_m12_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) (-(1 / 2 : ℝ) * (y ^ (-(1 / 2 : ℝ)) * y⁻¹)) y := by
  have h := Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hy.ne')
  rw [Real.rpow_sub_one hy.ne', div_eq_mul_inv] at h
  exact h

theorem rescale0 (κ lam : ℂ) (hκ : κ ≠ 0) (νC : ℂ) (hν : νC ^ 2 = 1 - 4 * lam) (F : ℝ → ℂ)
    (hF : DifferentiableOn ℝ F (Set.Ioi 0)) (hF' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0))
    (heq : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv F) y - (y : ℂ) * deriv F y +
      (4 * lam - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * F y = 0) :
    let c : ℝ := 2 * ‖κ‖
    let G : ℝ → ℂ := fun Y => ((((Y / c) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * F (Y / c)
    0 < c ∧ DifferentiableOn ℝ G (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv G) (Set.Ioi 0) ∧
    (∀ Y : ℝ, 0 < Y → (Y : ℂ) ^ 2 * deriv (deriv G) Y + (1 / 4 - νC ^ 2 - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * G Y = 0) ∧
    (∀ y : ℝ, 0 < y → G (c * y) = (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * F y) := by
  intro c G
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have hc : 0 < c := by positivity
  set g : ℝ → ℂ := fun y => (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * F y with hgdef
  set g1 : ℝ → ℂ := fun y => (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * (-(1 / 2 : ℂ) * (y : ℂ)⁻¹ * F y + deriv F y) with hg1def
  set g2 : ℝ → ℂ := fun y => (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) *
    ((3 / 4 : ℂ) * (y : ℂ)⁻¹ * (y : ℂ)⁻¹ * F y - (y : ℂ)⁻¹ * deriv F y + deriv (deriv F) y) with hg2def
  have hFd : ∀ y : ℝ, 0 < y → HasDerivAt F (deriv F y) y :=
    fun y hy => (hF.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hFdd : ∀ y : ℝ, 0 < y → HasDerivAt (deriv F) (deriv (deriv F) y) y :=
    fun y hy => (hF'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hpwC : ∀ y : ℝ, 0 < y → HasDerivAt (fun x : ℝ => (((x ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ))
      (((-(1 / 2 : ℝ) * (y ^ (-(1 / 2 : ℝ)) * y⁻¹)) : ℝ) : ℂ) y :=
    fun y hy => (rpow_m12_hasDerivAt hy).ofReal_comp
  have hg1 : ∀ y : ℝ, 0 < y → HasDerivAt g (g1 y) y := by
    intro y hy
    have h := (hpwC y hy).mul (hFd y hy)
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    convert h using 1
    all_goals try rfl
    try simp only [hg1def]; push_cast; ring
  have hderiv_g : ∀ y : ℝ, 0 < y → deriv g y = g1 y := fun y hy => (hg1 y hy).deriv
  have hg2 : ∀ y : ℝ, 0 < y → HasDerivAt g1 (g2 y) y := by
    intro y hy
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hinv : HasDerivAt (fun x : ℝ => (x : ℂ)⁻¹) (-((y : ℂ) ^ 2)⁻¹) y := by
      have h1 := (hasDerivAt_inv hy.ne').ofReal_comp
      have hfun : (fun x : ℝ => (x : ℂ)⁻¹) = fun x : ℝ => (((x⁻¹ : ℝ)) : ℂ) := by funext x; push_cast; rfl
      rw [hfun]
      convert h1 using 1
      all_goals try rfl
      push_cast; ring
    have hin : HasDerivAt (fun x : ℝ => -(1 / 2 : ℂ) * (x : ℂ)⁻¹ * F x + deriv F x)
        (-(1 / 2 : ℂ) * (-((y : ℂ) ^ 2)⁻¹) * F y + -(1 / 2 : ℂ) * (y : ℂ)⁻¹ * deriv F y + deriv (deriv F) y) y := by
      have := ((hinv.const_mul (-(1 / 2 : ℂ))).mul (hFd y hy)).add (hFdd y hy)
      convert this using 1 <;> first | rfl | ring
    have h := (hpwC y hy).mul hin
    convert h using 1
    all_goals try rfl
    try simp only [hg2def]; push_cast; field_simp; ring
  have hg1d : ∀ y : ℝ, 0 < y → HasDerivAt (deriv g) (g2 y) y := by
    intro y hy
    refine (hg2 y hy).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with s hs
    exact hderiv_g s hs
  have hGg : G = fun Y => g (Y / c) := rfl
  have hdiv : ∀ Y : ℝ, HasDerivAt (fun X : ℝ => X / c) (1 / c) Y := fun Y => by
    simpa using (hasDerivAt_id Y).div_const c
  have hG1 : ∀ Y : ℝ, 0 < Y → HasDerivAt G ((1 / c) • g1 (Y / c)) Y := by
    intro Y hY
    have hy : 0 < Y / c := div_pos hY hc
    rw [hGg]; exact (hg1 _ hy).scomp Y (hdiv Y)
  have hderiv_G : ∀ Y : ℝ, 0 < Y → deriv G Y = (1 / c) • g1 (Y / c) := fun Y hY => (hG1 Y hY).deriv
  have hG2 : ∀ Y : ℝ, 0 < Y → HasDerivAt (deriv G) ((1 / c) • ((1 / c) • g2 (Y / c))) Y := by
    intro Y hY
    have hy : 0 < Y / c := div_pos hY hc
    have h := ((hg2 _ hy).scomp Y (hdiv Y)).const_smul (1 / c)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hY] with s hs
    rw [hderiv_G s hs]; rfl
  have hGd : DifferentiableOn ℝ G (Set.Ioi 0) := fun Y hY => (hG1 Y hY).differentiableAt.differentiableWithinAt
  have hGd' : DifferentiableOn ℝ (deriv G) (Set.Ioi 0) := fun Y hY => (hG2 Y hY).differentiableAt.differentiableWithinAt
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcn : (c : ℂ) ^ 2 = 4 * ((‖κ‖ : ℝ) : ℂ) ^ 2 := by show ((2 * ‖κ‖ : ℝ) : ℂ) ^ 2 = _; push_cast; ring
  have hsum : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * g2 y + (-(3 / 4 : ℂ) + 4 * lam - 4 * (π : ℂ) ^ 2 * (c : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = 0 := by
    intro y hy
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have e := heq y hy
    have h2 : (y : ℂ) ^ 2 * g2 y = (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) *
        ((3 / 4 : ℂ) * F y - (y : ℂ) * deriv F y + (y : ℂ) ^ 2 * deriv (deriv F) y) := by
      simp only [hg2def]; field_simp
    rw [h2]
    simp only [hgdef]
    linear_combination (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * e +
      (-(4 : ℂ) * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 * (((y ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * F y) * hcn
  refine ⟨hc, hGd, hGd', fun Y hY => ?_, fun y hy => ?_⟩
  · have hy : 0 < Y / c := div_pos hY hc
    rw [(hG2 Y hY).deriv]
    have hYy : (Y : ℂ) = (c : ℂ) * ((Y / c : ℝ) : ℂ) := by push_cast; field_simp
    have h3 : (Y : ℂ) ^ 2 * ((1 / c) • ((1 / c) • g2 (Y / c))) = (((Y / c : ℝ)) : ℂ) ^ 2 * g2 (Y / c) := by
      rw [hYy]; simp only [Complex.real_smul]; push_cast; field_simp
    have hGY : G Y = g (Y / c) := rfl
    rw [h3, hGY, hYy, hν]
    linear_combination hsum (Y / c) hy
  · show g (c * y / c) = _
    rw [mul_div_cancel_left₀ _ hc.ne']

theorem n0_neg (κ lam : ℂ) (hκ : κ ≠ 0) (him : lam.im = 0) (hneg : lam.re < 0) (F : ℝ → ℂ)
    (hF : DifferentiableOn ℝ F (Set.Ioi 0)) (hF' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0))
    (heq : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv F) y - (y : ℂ) * deriv F y +
      (4 * lam - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * F y = 0)
    (B : ℝ) (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖F y‖ ≤ B) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖F y‖ ≤ C * y := by
  have hlam : lam = ((lam.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
  set ν : ℝ := Real.sqrt (1 - 4 * lam.re) with hνdef
  have hν1 : 1 < ν := by
    rw [hνdef]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (1 - 4 * lam.re) := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hν0 : 0 ≤ ν := by linarith
  have hνsq : ν ^ 2 = 1 - 4 * lam.re := Real.sq_sqrt (by linarith)
  have hνC : ((ν : ℝ) : ℂ) ^ 2 = 1 - 4 * lam := by rw [hlam]; exact_mod_cast hνsq
  have hνre : ((ν : ℝ) : ℂ).re = ν := Complex.ofReal_re _
  obtain ⟨hc, hGd, hGd', hGeq, hGval⟩ := rescale0 κ lam hκ ((ν : ℝ) : ℂ) hνC F hF hF' heq
  set c : ℝ := 2 * ‖κ‖ with hcdef
  set G : ℝ → ℂ := fun Y => ((((Y / c) ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * F (Y / c) with hGdef
  obtain ⟨B', hB'0, hB'⟩ := extend_bdd F hF (1 / c) B hB

  have hGap : ∀ Y : ℝ, 0 < Y → Y ≤ 1 → ‖G Y‖ ≤ (B' * c ^ (-(-(1 / 2 : ℝ)))) * Y ^ (-(1 / 2 : ℝ)) := by
    intro Y hY hY1
    have hy : 0 < Y / c := div_pos hY hc
    have hyc : Y / c ≤ 1 / c := div_le_div_of_nonneg_right hY1 hc.le
    simp only [hGdef]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy _),
      Real.div_rpow hY.le hc.le, Real.rpow_neg hc.le, div_eq_mul_inv, inv_inv]
    calc Y ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) * ‖F (Y / c)‖ ≤ Y ^ (-(1 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) * B' := by
          gcongr; exact hB' _ hy hyc
      _ = (B' * c ^ (-(-(1 / 2 : ℝ)))) * Y ^ (-(1 / 2 : ℝ)) := by rw [neg_neg]; ring
  have hGAP := LanglandsTunnell.norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori ((ν : ℝ) : ℂ)
    (by rw [hνre]; exact hν0) 10 0 (-(1 / 2)) _ G (fun _ => 0) hGd hGd' (fun Y _ _ => by simp)
    hGap (fun Y hY => by rw [hGeq Y hY])
  have hr : 1 / 2 - ((ν : ℝ) : ℂ).re < -(1 / 2) := by rw [hνre]; linarith
  obtain ⟨C, hC⟩ := hGAP.2 hr (1 / 2) (by norm_num)
  have hexp1 : (1 : ℝ) ≤ min (1 / 2 + ((ν : ℝ) : ℂ).re) 10 - 1 / 2 := by
    rw [hνre]; refine le_sub_iff_add_le.mpr (le_min (by linarith) (by norm_num))

  have hnear : ∀ y : ℝ, 0 < y → y ≤ 1 → c * y ≤ 1 → ‖F y‖ ≤ max C 0 * c * y := by
    intro y hy hy1 hcy
    have hY : 0 < c * y := by positivity
    have h := (hC (c * y) hY hcy).1
    rw [hGval y hy, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy _)] at h
    have hle : (c * y) ^ (min (1 / 2 + ((ν : ℝ) : ℂ).re) 10 - 1 / 2) ≤ (c * y) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hY hcy hexp1
    rw [Real.rpow_one] at hle
    have hpos := Real.rpow_pos_of_pos hy (1 / 2 : ℝ)
    have h2 := mul_le_mul_of_nonneg_left h hpos.le
    rw [← mul_assoc, ← Real.rpow_add hy, show (1 / 2 : ℝ) + -(1 / 2) = 0 by norm_num, Real.rpow_zero, one_mul] at h2
    have hy12 : y ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hy.le hy1 (by norm_num)
    have hA : C * (c * y) ^ (min (1 / 2 + ((ν : ℝ) : ℂ).re) 10 - 1 / 2) ≤ max C 0 * (c * y) :=
      calc C * (c * y) ^ (min (1 / 2 + ((ν : ℝ) : ℂ).re) 10 - 1 / 2)
          ≤ max C 0 * (c * y) ^ (min (1 / 2 + ((ν : ℝ) : ℂ).re) 10 - 1 / 2) := by gcongr; exact le_max_left _ _
        _ ≤ max C 0 * (c * y) := mul_le_mul_of_nonneg_left hle (le_max_right _ _)
    calc ‖F y‖ ≤ y ^ (1 / 2 : ℝ) * (C * (c * y) ^ (min (1 / 2 + ((ν : ℝ) : ℂ).re) 10 - 1 / 2)) := h2
      _ ≤ y ^ (1 / 2 : ℝ) * (max C 0 * (c * y)) := mul_le_mul_of_nonneg_left hA hpos.le
      _ ≤ 1 * (max C 0 * (c * y)) := mul_le_mul_of_nonneg_right hy12 (by positivity)
      _ = max C 0 * c * y := by ring

  obtain ⟨M, hM0, hM⟩ := bdd_Icc F hF (1 / c) 1 (by positivity)
  refine ⟨max C 0 * c + M * c, fun y hy hy1 => ?_⟩
  rcases le_or_gt (c * y) 1 with hcy | hcy
  · calc ‖F y‖ ≤ max C 0 * c * y := hnear y hy hy1 hcy
      _ ≤ (max C 0 * c + M * c) * y := by
          rw [add_mul]; linarith [mul_nonneg (mul_nonneg hM0 hc.le) hy.le]
  · have hyc' : 1 / c ≤ y := by rw [div_le_iff₀ hc, mul_comm]; exact hcy.le
    calc ‖F y‖ ≤ M := hM y ⟨hyc', hy1⟩
      _ ≤ M * (c * y) := le_mul_of_one_le_right hM0 hcy.le
      _ ≤ (max C 0 * c + M * c) * y := by nlinarith [le_max_right C 0, hc]

theorem exists_pos_norm_le_mul_rpow_of_torus_system
    (n : ℕ) (κ lam lam' : ℂ) (hκ : κ ≠ 0) (f : ℕ → ℝ → ℂ)
    (hsys :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0))
    (hfn : ∀ y : ℝ, f (n + 1) y = 0)
    (hU : lam' = (starRingEnd ℂ) lam)
    (hR : lam' = lam → lam.im = 0 → n = 0 ∨ -(((n : ℝ) ^ 2 + 4 * (n : ℝ)) / 16) < lam.re)
    (hZ0 : lam = 0 → n = 0 → ∀ y : ℝ, 0 < y → f 0 y = 0)
    (hbdd : ∀ p : Fin (n + 1), ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f p y‖ ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ δ := by

  have fromEps : (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ (1 - ε)) →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ δ := by
    intro h
    obtain ⟨C, hC⟩ := h (1 / 2) (by norm_num)
    exact ⟨1 / 2, by norm_num, C, fun p y hy hy1 => by have := hC p y hy hy1; norm_num at this ⊢; exact this⟩
  by_cases him : lam.im = 0
  ·
    have hlam' : lam' = lam := by rw [hU]; exact Complex.conj_eq_iff_im.mpr him
    rcases lt_or_ge 0 lam.re with hpos | hnp
    ·
      exact LanglandsTunnell.exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos n κ lam lam' hκ hlam' him hpos
        f hsys hfn
    · rcases Nat.even_or_odd n with hev | hodd
      · rcases Nat.eq_zero_or_pos n with hn0 | hnpos
        ·
          subst hn0
          by_cases hl0 : lam = 0
          ·
            refine ⟨1, one_pos, 0, fun p y hy hy1 => ?_⟩
            have hp : ((p : Fin (0 + 1)) : ℕ) = 0 := by omega
            rw [hp, hZ0 hl0 rfl y hy]; simp
          ·
            have hneg : lam.re < 0 := by
              rcases lt_or_eq_of_le hnp with h | h
              · exact h
              · exact absurd (Complex.ext (by simpa using h) (by simpa using him)) hl0
            obtain ⟨B, hB⟩ := hbdd 0
            have heq : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv (f 0)) y - (y : ℂ) * deriv (f 0) y +
                (4 * lam - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * f 0 y = 0 := by
              intro y hy
              have h2 := (((hsys 0).2.2) y hy).2
              rw [hlam'] at h2
              have h0 : (((0 : Fin (0 + 1)) : ℕ)) = 0 := rfl
              simp only [h0] at h2
              push_cast at h2 ⊢
              linear_combination h2
            obtain ⟨C, hC⟩ := n0_neg κ lam hκ him hneg (f 0) (hsys 0).1 (hsys 0).2.1 heq B hB
            refine ⟨1, one_pos, C, fun p y hy hy1 => ?_⟩
            have hp : ((p : Fin (0 + 1)) : ℕ) = 0 := by omega
            rw [hp, Real.rpow_one]
            exact hC y hy hy1
        ·
          have hn2 : 2 ≤ n := by obtain ⟨m, hm⟩ := hev; omega
          exact LanglandsTunnell.exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded n hev hn2
            κ lam lam' hκ hlam' him hnp f hfn hbdd hsys
      ·
        have hre : lam.re = lam'.re := by rw [hlam']
        exact fromEps (LanglandsTunnell.norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq n κ lam lam' hκ
          (Or.inr hodd) hre f hfn hsys)
  ·
    have hne : lam ≠ lam' := by
      intro h
      apply him
      have : (starRingEnd ℂ) lam = lam := by rw [← hU, ← h]
      exact Complex.conj_eq_iff_im.mp this
    have hre : lam.re = lam'.re := by rw [hU, Complex.conj_re]
    exact fromEps (LanglandsTunnell.norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq n κ lam lam' hκ
      (Or.inl hne) hre f hfn hsys)

end E41DISPATCH

namespace E41ASM

open E40DCFN NumberField.InfinitePlace

variable {K : Type} [Field K] [NumberField K]

theorem mult_eq_two {w : InfinitePlace K} (hw : w.IsComplex) : (w.mult : ℝ) = 2 := by
  rw [NumberField.InfinitePlace.mult, if_neg (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hw)]; norm_num

theorem core (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    {w : InfinitePlace K} (hw : w.IsComplex)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (hgr : ∀ p, ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (lam lam' : ℂ) (hU : lam' = (starRingEnd ℂ) lam)
    (hR : lam' = lam → lam.im = 0 → n = 0 ∨ -(((n : ℝ) ^ 2 + 4 * (n : ℝ)) / 16) < lam.re)
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (f : ℕ → ℝ → ℂ)
    (hf : ∀ (p : Fin (n + 1)) (y : ℝ), f p y =
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ))))
    (hsys :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) (1 : ℂ) * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0))
    (hfn : ∀ y : ℝ, f (n + 1) y = 0)
    (hZ0 : lam = 0 → n = 0 → ∀ y : ℝ, 0 < y → f 0 y = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ p : Fin (n + 1),
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne a)‖ ≤
          C * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ := by

  have hbdd : ∀ p : Fin (n + 1), ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f p y‖ ≤ B := by
    intro p
    obtain ⟨B, hB⟩ := E40IFC.bounded D ξ w₀ hξ hw b hb (x p) (hxZ p) (hgr p)
    exact ⟨B, fun y hy hy1 => by rw [hf]; exact hB y hy hy1⟩

  obtain ⟨δ, hδ, C, hC⟩ := E41DISPATCH.exists_pos_norm_le_mul_rpow_of_torus_system n 1 lam lam' one_ne_zero f hsys hfn hU hR hZ0 hbdd

  choose Bl hBl using fun p => E40IFC.large D w₀ hw b hb (x p) (hgr p)
  refine ⟨δ, hδ, max C 0 + ∑ p : Fin (n + 1), max (Bl p) 0, fun p a ha hab => ?_⟩
  set r : ℝ := ‖((a : AdeleRing (𝓞 K) K)).1 w‖ with hr
  set E : ℝ := (w.mult : ℝ) * w₀ / 2 with hE
  have hr0 : 0 < r := by
    rw [hr, norm_pos_iff]
    intro h0
    have h1 : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 := by rw [mul_inv_cancel]; rfl
    have : (((a * a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w =
        ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w := rfl
    rw [this, h0, zero_mul] at h1; exact zero_ne_one h1
  have hrE : 0 ≤ r ^ E := Real.rpow_nonneg hr0.le _
  have hmin0 : 0 < min 1 r := lt_min one_pos hr0
  have hminδ : 0 ≤ (min 1 r) ^ δ := Real.rpow_nonneg hmin0.le _
  have hBsum : max (Bl p) 0 ≤ ∑ q : Fin (n + 1), max (Bl q) 0 :=
    Finset.single_le_sum (fun q _ => le_max_right (Bl q) 0) (Finset.mem_univ p)
  have hlarge := hBl p a ha hab
  rcases le_or_gt r 1 with hr1 | hr1
  ·
    have htw := E40IFC.twist D ξ w₀ hξ hw b hb x hxZ hwt p a ha hab
    rw [min_eq_right hr1]
    rw [htw, ← hf p r]
    calc r ^ E * ‖f p r‖ ≤ r ^ E * (C * r ^ δ) := mul_le_mul_of_nonneg_left (hC p r hr0 hr1) hrE
      _ ≤ r ^ E * (max C 0 * r ^ δ) := by gcongr; exact le_max_left _ _
      _ = max C 0 * r ^ E * r ^ δ := by ring
      _ ≤ (max C 0 + ∑ q : Fin (n + 1), max (Bl q) 0) * r ^ E * r ^ δ := by
          gcongr
          linarith [Finset.sum_nonneg (fun q (_ : q ∈ Finset.univ) => le_max_right (Bl q) 0)]
  ·
    rw [min_eq_left hr1.le, Real.one_rpow, mul_one]
    calc _ ≤ Bl p * r ^ E := hlarge
      _ ≤ max (Bl p) 0 * r ^ E := by gcongr; exact le_max_left _ _
      _ ≤ (max C 0 + ∑ q : Fin (n + 1), max (Bl q) 0) * r ^ E := by
          gcongr; linarith [le_max_right C 0]

end E41ASM

open E40DCFN in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxc : ∀ p, Continuous (x p))
    (hxG : ∀ p (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x p (globalPoints (𝓞 K) K γ * g) = x p g)
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p)))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hE₁ : E₁ 0 = 1) (hE₂ : E₂ 0 = 1)
    (hE₁' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₁ s i j)
      (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hE₂' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₂ s i j)
      (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₁ s p' p * x p' g)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₂ s p' p * x p' g)
    (lam lam' : ℂ)
    (hcas : ∀ p, archCasimirAtComplex hw (x p) = lam • x p ∧ archCasimirBarAtComplex hw (x p) = lam' • x p)
    (hgr : ∀ p, ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (hU : lam' = (starRingEnd ℂ) lam)
    (hR : lam' = lam → lam.im = 0 → n = 0 ∨ -(((n : ℝ) ^ 2 + 4 * (n : ℝ)) / 16) < lam.re)
    (hZ : lam = 0 → n = 0 → ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℂ),
      Matrix.GeneralLinearGroup.det h = 1 → x 0 (g * archComplexGLAt hw h) = x 0 g)
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ p : Fin (n + 1),
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
              (diagOne a)‖ ≤
          C * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ := by

  have hW := E40DCFN.hasDerivAt_W_string D hw b x hxc hreg
  have hCas := E40IFC.hCas_string D hw b x hxc hreg lam lam' hcas
  have hK := E37K.hK_of_string K D hw (g0 w b) n x hxc E₁ E₂ hK₁ hK₂

  have hI := AutomorphicForm.gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype n
    (fun (p : Fin (n + 1)) (h : GL (Fin 2) ℂ) => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw h))
    1 lam lam'
    (fun (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ) =>
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (x p)) 1 (g0 w b * archComplexGLAt hw h))
    (fun (p : Fin (n + 1)) (d' d : ArchDirComplex) (h : GL (Fin 2) ℂ) =>
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d' (archDerivAtComplex hw d (x p))) 1 (g0 w b * archComplexGLAt hw h))
    hW.1 (fun p d d' h => hW.2 p d' d h) hCas.1 hCas.2
    (E40IFC.hN_string D hw b x hxG (E40IFC.g0_comm hw b)) (E40IFC.hM_string D hw b x hwt)
    E₁ E₂ hE₁ hE₂ hE₁' hE₂' hK.1 hK.2

  set f : ℕ → ℝ → ℂ := fun m y => if hm : m < n + 1 then
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x ⟨m, hm⟩) 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ)))
    else 0 with hfdef
  have hsys :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖(1 : ℂ)‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) (1 : ℂ) * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0) := hI
  have hf : ∀ (p : Fin (n + 1)) (y : ℝ), f p y =
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ))) := by
    intro p y
    simp only [hfdef, dif_pos p.isLt, Fin.eta]
  have hfn : ∀ y : ℝ, f (n + 1) y = 0 := fun y => by simp [hfdef]
  have hZ0 : lam = 0 → n = 0 → ∀ y : ℝ, 0 < y → f 0 y = 0 := by
    intro hl hn0 y _
    have h0 : f 0 y = whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x 0) 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ))) := by
      have := hf 0 y
      simpa using this
    rw [h0]
    exact E40IFC.W_eq_zero_of_sl2_invariant D hw b (x 0) (hxG 0) (hZ hl hn0) (E40IFC.g0_comm hw b) _
  exact E41ASM.core D ξ w₀ hξ hw x hxZ hwt hgr lam lam' hU hR b hb f hf hsys hfn hZ0

end

end S_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String (solution)
