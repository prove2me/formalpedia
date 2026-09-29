-- Prove2me | solution 1 for AutomorphicForm.exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/44e8103c-fd24-5356-978a-ac23925428df

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Definitions.Def_NumberField_IdeleBox
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt
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

end E40DCFN

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

namespace E40DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

theorem diagOne_eq_centralScalar_mul_diagOne_mul_archComplexGLAt
    (w : InfinitePlace K) (hw : w.IsComplex)
    (a b' z : (AdeleRing (𝓞 K) K)ˣ)
    (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) (hb' : ((b' : AdeleRing (𝓞 K) K)).2 = 1) (hz : ((z : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b' : AdeleRing (𝓞 K) K)).1 w')
    (hbw : ((b' : AdeleRing (𝓞 K) K)).1 w = 1)
    (t ζ : ℂˣ) (u : ℝ)
    (ht : (t : ℂ) ^ 2 = InfinitePlace.Completion.ringEquivComplexOfIsComplex hw (((a : AdeleRing (𝓞 K) K)).1 w))
    (huζ : Complex.exp (u : ℂ) * (ζ : ℂ) = t)
    (hzw' : ∀ w' : InfinitePlace K, w' ≠ w → ((z : AdeleRing (𝓞 K) K)).1 w' = 1)
    (hzw : InfinitePlace.Completion.ringEquivComplexOfIsComplex hw (((z : AdeleRing (𝓞 K) K)).1 w) = t) :
    diagOne a = centralScalar (𝓞 K) K z * (diagOne b' * archComplexGLAt hw (splitTorusGL2Complex (u : ℂ) * circleGL2 ζ)) ∧
      archComponent K w (glArch (𝓞 K) K (diagOne b')) = 1 := by

  have hb'eq : b' = bprime w a := by
    apply Units.ext
    refine Prod.ext (funext fun v => ?_) ?_
    · by_cases hv : v = w
      · subst hv; rw [bprime_fst_self, hbw]
      · rw [bprime_fst_of_ne hv, hab v hv]
    · rw [bprime_snd, hb', ha]
  have hzeq : z = iotaW hw t := by
    apply Units.ext
    refine Prod.ext (funext fun v => ?_) ?_
    · by_cases hv : v = w
      · subst hv
        rw [iotaW_fst_self]
        apply (eC hw).injective
        rw [RingEquiv.apply_symm_apply]
        exact hzw
      · rw [iotaW_fst_of_ne K hw hv, hzw' v hv]; rfl
    · rw [iotaW_snd, hz]
  have haa : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((a : AdeleRing (𝓞 K) K)).1 w' :=
    fun _ _ => rfl
  have hgeo := diagOne_eq_central_mul_g0_mul K w hw a a ha ha haa t ζ u ht huζ
  refine ⟨?_, ?_⟩
  · rw [hgeo, hzeq, hb'eq]; rfl
  · rw [hb'eq]; exact archComponent_glArch_g0 K w a

end E40DCFN

namespace E40DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

def sqrtC {w : InfinitePlace K} (hw : w.IsComplex) (tw : w.Completion) : ℂ := (eC hw tw) ^ ((2 : ℂ)⁻¹)

theorem sqrtC_sq {w : InfinitePlace K} (hw : w.IsComplex) (tw : w.Completion) : sqrtC K hw tw ^ 2 = eC hw tw := by
  unfold sqrtC; exact_mod_cast Complex.cpow_nat_inv_pow _ two_ne_zero

theorem sqrtC_ne_zero {w : InfinitePlace K} (hw : w.IsComplex) {tw : w.Completion} (htw : tw ≠ 0) : sqrtC K hw tw ≠ 0 := by
  intro h0
  have h := sqrtC_sq K hw tw
  rw [h0] at h
  have : eC hw tw = 0 := by rw [← h]; norm_num
  exact htw ((eC hw).injective (by rw [this, map_zero]))

theorem norm_sqrtC_sq {w : InfinitePlace K} (hw : w.IsComplex) (tw : w.Completion) : ‖sqrtC K hw tw‖ ^ 2 = ‖tw‖ := by
  rw [← norm_pow, sqrtC_sq, norm_eC]

def muC (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    {w : InfinitePlace K} (hw : w.IsComplex) (w₀' : ℝ) (n : ℕ) (p : Fin (n + 1)) (tw : w.Completion) : ℂ :=
  if htw : tw = 0 then (if (w.mult : ℝ) * w₀' / 2 = 0 then 1 else 0) else
    ((ξ ⟨iotaW hw (Units.mk0 (sqrtC K hw tw) (sqrtC_ne_zero K hw htw)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
      (sqrtC K hw tw / (‖sqrtC K hw tw‖ : ℂ)) ^ ((n : ℤ) - 2 * (p : ℕ))

theorem exists_mu_whittakerCoefficient_diagOne_eq (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p)) :
    ∃ μ : Fin (n + 1) → w.Completion → ℂ,
      (∀ (p : Fin (n + 1)) (t : w.Completion), ‖μ p t‖ = ‖t‖ ^ ((w.mult : ℝ) * w₀ / 2)) ∧
      ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 →
        ∀ (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          whittakerCoefficient K (productionPinsOf K D
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne a) =
          μ p (((a : AdeleRing (𝓞 K) K)).1 w) *
            whittakerCoefficient K (productionPinsOf K D
              (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) (x p) 1
              (diagOne (b * (archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹) *
                archComplexGLAt hw (splitTorusGL2Complex ((Real.log ‖((a : AdeleRing (𝓞 K) K)).1 w‖ / 2 : ℝ) : ℂ))) := by
  refine ⟨muC K D ξ hw w₀ n, ?_, ?_⟩
  · intro p tw
    by_cases htw : tw = 0
    · unfold muC
      rw [dif_pos htw, htw, norm_zero]
      by_cases he : (w.mult : ℝ) * w₀ / 2 = 0
      · rw [if_pos he, he, Real.rpow_zero, norm_one]
      · rw [if_neg he, Real.zero_rpow he, norm_zero]
    have ht0 := sqrtC_ne_zero K hw htw
    have hnt0 : 0 < ‖sqrtC K hw tw‖ := norm_pos_iff.2 ht0
    have hζ1 : ‖sqrtC K hw tw / (‖sqrtC K hw tw‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnt0, div_self hnt0.ne']
    unfold muC
    rw [dif_neg htw, norm_mul, norm_zpow, hζ1, one_zpow, mul_one, hξ, ideleNorm_iotaW, ← rpow_eq_rpow_mult K hw]
    show (‖sqrtC K hw tw‖ ^ 2) ^ w₀ = ‖tw‖ ^ w₀
    rw [norm_sqrtC_sq]
  · intro b hb p a ha hab

    set tw : w.Completion := ((a : AdeleRing (𝓞 K) K)).1 w with htw
    set r : ℝ := ‖tw‖ with hr
    have hr0 : 0 < r := by
      have h := congrArg (fun q : AdeleRing (𝓞 K) K => q.1 w) a.mul_inv
      change ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 at h
      exact norm_pos_iff.2 (left_ne_zero_of_mul_eq_one h)
    have htw0 : tw ≠ 0 := norm_pos_iff.1 hr0
    set t₀ : ℂ := sqrtC K hw tw with ht₀
    have ht₀0 : t₀ ≠ 0 := sqrtC_ne_zero K hw htw0
    have hnt : ‖t₀‖ ^ 2 = r := norm_sqrtC_sq K hw tw
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
    have hgeo := diagOne_eq_central_mul_g0_mul K w hw b a ha hb hab t ζ u (sqrtC_sq K hw tw) huζ
    have hζ1 : ‖(ζ : ℂ)‖ = 1 := hζ₀1
    rw [hgeo, whittakerCoefficient_centralScalar_mul K _ _ (x p) 1 (iotaW hw t) _ (hxZ p (iotaW hw t))]
    have h5 := Fstr_mul_circleGL2 K D hw b x hwt p ζ hζ1 (splitTorusGL2Complex (u : ℂ))
    unfold Fstr W at h5
    rw [h5, ← mul_assoc]
    congr 1
    unfold muC
    rw [dif_neg htw0]
    rfl

end E40DCFN

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
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p)) :
    ∃ μ : Fin (n + 1) → w.Completion → ℂ,
      (∀ (p : Fin (n + 1)) (t : w.Completion), ‖μ p t‖ = ‖t‖ ^ ((w.mult : ℝ) * w₀ / 2)) ∧
      ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 →
        ∀ (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne a) =
            μ p (((a : AdeleRing (𝓞 K) K)).1 w) *
              whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne (b * (NumberField.TateGlobal.archUnitHom w (NumberField.AdeleRing.infiniteUnitsComponent (𝓞 K) K w b))⁻¹) *
                archComplexGLAt hw (splitTorusGL2Complex ((Real.log ‖((a : AdeleRing (𝓞 K) K)).1 w‖ / 2 : ℝ) : ℂ))) :=
  E40DCFN.exists_mu_whittakerCoefficient_diagOne_eq K D ξ w₀ hξ w hw n x hxZ hwt

end

end S_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt
end P2MW
export P2MW.S_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt (solution)
