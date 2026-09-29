-- Prove2me | solution 1 for AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2c8c7039-ea51-5733-b9cd-dfcdb4ddd968

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
import Theorems.Thm_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half
import Theorems.Thm_LanglandsTunnell_exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero
import Theorems.Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_AdelicLevel_diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar
import Theorems.Thm_NumberField_AdelicLevel_diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
import Theorems.Thm_Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero
import Theorems.Thm_AutomorphicForm_exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup unipotentGL2 unipotentGL2_coe unipotentGL2_add archRealGLAt archRealLiftAt IsArchSmoothAt ArchDir archDerivAt archCasimirAt archDerivAt_smul archDerivAt_comp_mul_left norm_ringEquivRealOfIsReal archWeightCharAt HasArchCharacterAt₀ whittakerCoefficient whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt whittakerCoefficient_unipotentGL2_mul exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul"
namespace Core25Idele
p2m_open "AutomorphicForm"

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

noncomputable def archComp (a : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) : (w.Completion)ˣ where
  val := ((a : AdeleRing (𝓞 K) K)).1 w
  inv := ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w
  val_inv := by
    have h := congrArg (fun x : AdeleRing (𝓞 K) K => x.1 w) a.mul_inv
    exact h
  inv_val := by
    have h := congrArg (fun x : AdeleRing (𝓞 K) K => x.1 w) a.inv_mul
    exact h

theorem archComp_val (a : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) :
    ((archComp K a w : (w.Completion)ˣ) : w.Completion) = ((a : AdeleRing (𝓞 K) K)).1 w := rfl

theorem archIdele_archComp (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) :
    archIdele K (archComp K a) = a := by
  apply Units.ext
  refine Prod.ext ?_ ?_
  · funext w; rfl
  · exact ha.symm

theorem archComp_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) : archComp K (archIdele K t) = t := by
  funext w; apply Units.ext; rfl

end AutomorphicForm.Core25Idele

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup unipotentGL2 unipotentGL2_coe unipotentGL2_add archRealGLAt archRealLiftAt IsArchSmoothAt ArchDir archDerivAt archCasimirAt archDerivAt_smul archDerivAt_comp_mul_left norm_ringEquivRealOfIsReal archWeightCharAt HasArchCharacterAt₀ whittakerCoefficient whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt whittakerCoefficient_unipotentGL2_mul exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul"
namespace Core25Aux
p2m_open "AutomorphicForm"

open MeasureTheory

variable (K : Type) [Field K] [NumberField K]

theorem unipotentGL2_algebraMap (β : K) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) = globalPoints (𝓞 K) K (unipotentGL2 β) := by
  ext i j
  change (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
    algebraMap K (AdeleRing (𝓞 K) K) ((unipotentGL2 β : Matrix (Fin 2) (Fin 2) K) i j)
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem det_diagOne {R : Type*} [CommRing R] (a : Rˣ) : Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  apply Units.ext
  change ((diagOne a : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = (a : R)
  rw [Matrix.det_fin_two]
  simp [diagOne_coe_apply]

theorem det_unipotentGL2 (x : ℝ) : Matrix.GeneralLinearGroup.det (unipotentGL2 x) = 1 := by
  apply Units.ext
  change ((unipotentGL2 x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
  rw [unipotentGL2_coe, Matrix.det_fin_two_of]; ring

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    g * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * g := by
  apply Units.ext
  change (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * (Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) (AdeleRing (𝓞 K) K)) =
    (Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) (AdeleRing (𝓞 K) K)) * g
  change (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (z : (AdeleRing (𝓞 K) K)) =
    Matrix.scalar (Fin 2) (z : (AdeleRing (𝓞 K) K)) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
  exact (Matrix.scalar_commute (z : (AdeleRing (𝓞 K) K)) (fun r' => Commute.all _ r') (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).symm.eq

theorem whittakerCoefficient_mul_centralScalar
    (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ)
    (z : (AdeleRing (𝓞 K) K)ˣ) (hφ : ∀ g, φ (centralScalar (𝓞 K) K z * g) = c * φ g) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * centralScalar (𝓞 K) K z) = c * whittakerCoefficient K pins ψ φ α g := by
  letI := pins.nS
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [← mul_assoc, centralScalar_comm, hφ]
  ring

theorem whittakerCoefficient_mul_of_rightInvariant
    (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (h : AdelicGL2 (𝓞 K) K) (hφ : ∀ g, φ (g * h) = φ g) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * h) = whittakerCoefficient K pins ψ φ α g := by
  letI := pins.nS
  unfold whittakerCoefficient
  congr 1
  funext x
  rw [← mul_assoc, hφ]

end AutomorphicForm.Core25Aux

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup unipotentGL2 unipotentGL2_coe unipotentGL2_add archRealGLAt archRealLiftAt IsArchSmoothAt ArchDir archDerivAt archCasimirAt archDerivAt_smul archDerivAt_comp_mul_left norm_ringEquivRealOfIsReal archWeightCharAt HasArchCharacterAt₀ whittakerCoefficient whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt whittakerCoefficient_unipotentGL2_mul exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul"
namespace Core25JP
p2m_open "AutomorphicForm"

theorem prod_min_rpow_le {ι : Type} [Fintype ι] (u : ι → ℝ) (hu : ∀ i, 0 < u i) (m : ι → ℕ)
    (δs : ι → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδle : ∀ i, δ * m i ≤ δs i) :
    ∏ i, (min 1 (u i)) ^ δs i ≤ (min 1 (∏ i, u i ^ (m i))) ^ δ := by
  classical
  have hmin_pos : ∀ i, 0 < min 1 (u i) := fun i => lt_min one_pos (hu i)
  have hmin_le : ∀ i, min 1 (u i) ≤ 1 := fun i => min_le_left _ _

  have h1 : ∀ i, (min 1 (u i)) ^ δs i ≤ ((min 1 (u i)) ^ (m i)) ^ δ := by
    intro i
    calc (min 1 (u i)) ^ δs i ≤ (min 1 (u i)) ^ (δ * m i) :=
          Real.rpow_le_rpow_of_exponent_ge (hmin_pos i) (hmin_le i) (hδle i)
      _ = (min 1 (u i)) ^ ((m i : ℝ) * δ) := by rw [mul_comm]
      _ = ((min 1 (u i)) ^ (m i : ℝ)) ^ δ := Real.rpow_mul (hmin_pos i).le _ _
      _ = ((min 1 (u i)) ^ (m i)) ^ δ := by rw [Real.rpow_natCast]
  have h2 : ∏ i, (min 1 (u i)) ^ δs i ≤ ∏ i, ((min 1 (u i)) ^ (m i)) ^ δ :=
    Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (hmin_pos i).le _) fun i _ => h1 i
  refine h2.trans ?_
  rw [Real.finsetProd_rpow _ _ (fun i _ => pow_nonneg (hmin_pos i).le _)]
  apply Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => pow_nonneg (hmin_pos i).le _) _ hδ
  refine le_min ?_ ?_
  · exact Finset.prod_le_one (fun i _ => pow_nonneg (hmin_pos i).le _) fun i _ => pow_le_one₀ (hmin_pos i).le (hmin_le i)
  · exact Finset.prod_le_prod (fun i _ => pow_nonneg (hmin_pos i).le _)
      fun i _ => pow_le_pow_left₀ (hmin_pos i).le (min_le_right _ _) _

theorem prod_rpow_natCast_mul {ι : Type} [Fintype ι] (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (m : ι → ℕ) (r : ℝ) :
    ∏ i, u i ^ ((m i : ℝ) * r) = (∏ i, u i ^ (m i)) ^ r := by
  have : ∀ i, u i ^ ((m i : ℝ) * r) = (u i ^ (m i)) ^ r := fun i => by
    rw [Real.rpow_mul (hu i), Real.rpow_natCast]
  simp_rw [this]
  exact Real.finsetProd_rpow _ _ (fun i _ => pow_nonneg (hu i) _) r

end AutomorphicForm.Core25JP

open AutomorphicForm.Core25Idele AutomorphicForm.Core25Aux AutomorphicForm.Core25JP MeasureTheory

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup unipotentGL2 unipotentGL2_coe unipotentGL2_add archRealGLAt archRealLiftAt IsArchSmoothAt ArchDir archDerivAt archCasimirAt archDerivAt_smul archDerivAt_comp_mul_left norm_ringEquivRealOfIsReal archWeightCharAt HasArchCharacterAt₀ whittakerCoefficient whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt whittakerCoefficient_unipotentGL2_mul exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul"
namespace Core25
p2m_open "AutomorphicForm"

theorem central_iterate (K : Type) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal) (ε : ℝ)
    (ξv : (AdeleRing (𝓞 K) K)ˣ → ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), φ (centralScalar (𝓞 K) K z * g) = ξv z * φ g)
    (j : ℕ) :
    ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hw .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E z + archDerivAt hw .Fm z))^[j] φ) (centralScalar (𝓞 K) K z * g) =
        ξv z * ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hw .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E z + archDerivAt hw .Fm z))^[j] φ) g := by
  induction j generalizing φ with
  | zero => simpa using hφ
  | succ j ih =>
    intro z g
    simp only [Function.iterate_succ_apply]
    apply ih
    intro z' g'
    have hD : ∀ d : ArchDir, archDerivAt hw d φ (centralScalar (𝓞 K) K z' * g') = ξv z' * archDerivAt hw d φ g' := by
      intro d
      have h1 := archDerivAt_comp_mul_left hw d φ (centralScalar (𝓞 K) K z')
      have hfun : (fun g => φ (centralScalar (𝓞 K) K z' * g)) = (ξv z') • φ := by
        funext g''; rw [Pi.smul_apply, smul_eq_mul]; exact hφ z' g''
      rw [hfun, archDerivAt_smul] at h1
      have := congrFun h1 g'
      simpa only [Pi.smul_apply, smul_eq_mul] using this.symm
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hD]
    ring

theorem dpure_fn
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ) (lam : ℝ)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hcontY : Continuous y)
    (hleft : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g)
    (hcent : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * y g)
    (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y)
    (hys : IsArchSmoothAt hw y)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d y))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' y)))
    (hD : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) y))
    (hΩ : archCasimirAt hw y = ((lam : ℝ) : ℂ) • y)
    (hgr : ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 g‖ ≤ M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (htri : 0 < lam ∨
      (∃ (ε : ℝ) (k₀ M : ℕ), (ε = 1 ∨ ε = -1) ∧ 2 ≤ k₀ ∧ lam = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
        ((n : ℤ) : ℝ) = ε * (k₀ + 2 * M) ∧ (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hw .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E z + archDerivAt hw .Fm z))^[M + 1] y = 0 ∧
        ∃ Mgr : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
          ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hw .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E z + archDerivAt hw .Fm z))^[M] y) 1 g‖ ≤
            Mgr * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) ∨
      (lam = 0 ∧ ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ),
        Matrix.GeneralLinearGroup.det h = 1 → y (g * archRealGLAt hw h) = y g))
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne a)‖ ≤ C * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
            (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ := by
  classical
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he_def

  by_cases hy0 : y = 0
  · refine ⟨1, one_pos, 0, ?_⟩
    intro a ha hab
    subst hy0
    have h0 : whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (0 : AdelicGL2 (𝓞 K) K → ℂ) 1 (diagOne a) = 0 := by
      unfold whittakerCoefficient; simp
    rw [h0, norm_zero, zero_mul, zero_mul]

  obtain ⟨M, hM⟩ := hgr
  have hper : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      y (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = y g := by
    intro β g; rw [unipotentGL2_algebraMap]; exact hleft _ _

  have hsymm_ne : ∀ t : ℝ, t ≠ 0 → e.symm t ≠ 0 := fun t ht h => ht (by simpa using congrArg e h)
  let unitAt : ∀ t : ℝ, t ≠ 0 → (w.Completion)ˣ := fun t ht => Units.mk0 (e.symm t) (hsymm_ne t ht)
  let aOf : ∀ t : ℝ, t ≠ 0 → (AdeleRing (𝓞 K) K)ˣ := fun t ht => archIdele K (Function.update (archComp K b) w (unitAt t ht))
  let b' : (AdeleRing (𝓞 K) K)ˣ := archIdele K (Function.update (archComp K b) w 1)
  have haOf_snd : ∀ t ht, ((aOf t ht : (AdeleRing (𝓞 K) K))).2 = 1 := fun t ht => archIdele_snd K _
  have haOf_w : ∀ t ht, e (((aOf t ht : (AdeleRing (𝓞 K) K))).1 w) = t := by
    intro t ht
    show e ((Function.update (archComp K b) w (unitAt t ht) w : (w.Completion)ˣ) : w.Completion) = t
    rw [Function.update_self]; show e (e.symm t) = t; exact e.apply_symm_apply t
  have haOf_off : ∀ t ht (w' : InfinitePlace K), w' ≠ w → ((aOf t ht : (AdeleRing (𝓞 K) K))).1 w' = ((b : (AdeleRing (𝓞 K) K))).1 w' := by
    intro t ht w' hw'
    show ((Function.update (archComp K b) w (unitAt t ht) w' : (w'.Completion)ˣ) : w'.Completion) = _
    rw [Function.update_of_ne hw']; rfl
  have hb'_snd : ((b' : (AdeleRing (𝓞 K) K))).2 = 1 := archIdele_snd K _
  have hb'_w : ((b' : (AdeleRing (𝓞 K) K))).1 w = 1 := by
    show ((Function.update (archComp K b) w 1 w : (w.Completion)ˣ) : w.Completion) = 1
    rw [Function.update_self]; rfl
  have hab' : ∀ t ht (w' : InfinitePlace K), w' ≠ w → ((aOf t ht : (AdeleRing (𝓞 K) K))).1 w' = ((b' : (AdeleRing (𝓞 K) K))).1 w' := by
    intro t ht w' hw'
    rw [haOf_off t ht w' hw']
    show _ = ((Function.update (archComp K b) w 1 w' : (w'.Completion)ˣ) : w'.Completion)
    rw [Function.update_of_ne hw']; rfl

  have ha_eq : ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : (AdeleRing (𝓞 K) K))).2 = 1 →
      (∀ w' : InfinitePlace K, w' ≠ w → ((a : (AdeleRing (𝓞 K) K))).1 w' = ((b : (AdeleRing (𝓞 K) K))).1 w') →
      ∀ (ht : e (((a : (AdeleRing (𝓞 K) K))).1 w) ≠ 0), a = aOf (e (((a : (AdeleRing (𝓞 K) K))).1 w)) ht := by
    intro a ha hab ht
    have h1 : archIdele K (archComp K a) = a := archIdele_archComp K a ha
    have h2 : archComp K a = Function.update (archComp K b) w (unitAt (e (((a : (AdeleRing (𝓞 K) K))).1 w)) ht) := by
      funext w'
      by_cases hw' : w' = w
      · subst hw'; rw [Function.update_self]; apply Units.ext
        show ((a : (AdeleRing (𝓞 K) K))).1 w' = e.symm (e (((a : (AdeleRing (𝓞 K) K))).1 w')); exact (e.symm_apply_apply _).symm
      · rw [Function.update_of_ne hw']; apply Units.ext; exact hab w' hw'
    calc a = archIdele K (archComp K a) := h1.symm
      _ = aOf (e (((a : (AdeleRing (𝓞 K) K))).1 w)) ht := by rw [h2]

  let zOf : ∀ s : ℝ, s ≠ 0 → (AdeleRing (𝓞 K) K)ˣ := fun s hs =>
    archIdele K (Function.update (fun w' : InfinitePlace K => (1 : (w'.Completion)ˣ)) w (unitAt s hs))
  have hzOf_snd : ∀ s hs, ((zOf s hs : (AdeleRing (𝓞 K) K))).2 = 1 := fun s hs => archIdele_snd K _
  have hzOf_w : ∀ s hs, e (((zOf s hs : (AdeleRing (𝓞 K) K))).1 w) = s := by
    intro s hs
    show e ((Function.update (fun w' : InfinitePlace K => (1 : (w'.Completion)ˣ)) w (unitAt s hs) w : (w.Completion)ˣ) : w.Completion) = s
    rw [Function.update_self]; exact e.apply_symm_apply s
  have hzOf_off : ∀ s hs (w' : InfinitePlace K), w' ≠ w → ((zOf s hs : (AdeleRing (𝓞 K) K))).1 w' = 1 := by
    intro s hs w' hw'
    show ((Function.update (fun w' : InfinitePlace K => (1 : (w'.Completion)ˣ)) w (unitAt s hs) w' : (w'.Completion)ˣ) : w'.Completion) = 1
    rw [Function.update_of_ne hw']; rfl

  have hξz : ∀ s (hs : 0 < s), ‖((ξ ⟨zOf s hs.ne', Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ = s ^ w₀ := by
    intro s hs
    rw [hξ, NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _ (hzOf_snd s hs.ne')]
    rw [Finset.prod_eq_single w]
    · have h1 : ‖((zOf s hs.ne' : (AdeleRing (𝓞 K) K))).1 w‖ = s := by
        rw [← AutomorphicForm.norm_ringEquivRealOfIsReal hw, ← he_def, hzOf_w s hs.ne', Real.norm_eq_abs]; exact abs_of_pos hs
      rw [h1, InfinitePlace.mult, if_pos hw, pow_one]
    · intro w' _ hw'; rw [hzOf_off s hs.ne' w' hw', norm_one, one_pow]
    · intro h; exact absurd (Finset.mem_univ w) h

  have hg₀ : archComponent K w (glArch (𝓞 K) K (diagOne b')) = 1 :=
    (NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar K w hw 1 (Or.inl rfl) 1 one_pos
      b' b' (zOf 1 one_ne_zero) hb'_snd hb'_snd (hzOf_snd 1 one_ne_zero) (fun _ _ => rfl) hb'_w
      (by rw [hb'_w, map_one]; norm_num) (hzOf_off 1 one_ne_zero) (by rw [hzOf_w 1 one_ne_zero]; simp)).2

  let Bn : ℝ := ∏ w' ∈ Finset.univ.erase w, ‖((b : (AdeleRing (𝓞 K) K))).1 w'‖ ^ w'.mult
  have hBn : 0 < Bn := Finset.prod_pos fun w' _ => pow_pos (norm_pos_iff.2 (archComp K b w').ne_zero) _
  have hNgen : ∀ t (ht : t ≠ 0), NumberField.TateGlobal.ideleNorm K (aOf t ht) = |t| * Bn := by
    intro t ht
    rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _ (haOf_snd _ ht),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
    congr 1
    · rw [InfinitePlace.mult, if_pos hw, pow_one, ← AutomorphicForm.norm_ringEquivRealOfIsReal hw, ← he_def,
        haOf_w _ ht, Real.norm_eq_abs]
    · exact Finset.prod_congr rfl fun w' hw' => by rw [haOf_off _ ht w' (Finset.ne_of_mem_erase hw')]
  have haOf_congr : ∀ t₁ t₂ (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0), t₁ = t₂ → aOf t₁ h₁ = aOf t₂ h₂ := by
    intro t₁ t₂ h₁ h₂ h; subst h; rfl

  have key : ∀ ε : ℝ, ∀ hε0 : ε ≠ 0, (ε = 1 ∨ ε = -1) → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ uu : ℝ, ∀ huu : 0 < uu, uu ≤ 1 →
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne (aOf (ε * uu) (mul_ne_zero hε0 huu.ne')))‖ ≤
        C * uu ^ (w₀ / 2) * uu ^ δ := by
    intro ε hε0 hε

    have hlamre : (1 / 4 : ℂ) - ((lam : ℝ) : ℂ) = (((1 / 4 : ℝ) - lam : ℝ) : ℂ) := by push_cast; try ring
    set r : ℝ := 1 / 4 - lam with hr
    let ν : ℂ := if 0 ≤ r then ((Real.sqrt r : ℝ) : ℂ) else ((Real.sqrt (-r) : ℝ) : ℂ) * Complex.I
    have hν : ν ^ 2 = 1 / 4 - ((lam : ℝ) : ℂ) := by
      rw [hlamre]
      simp only [ν]
      split_ifs with h
      · rw [← Complex.ofReal_pow, Real.sq_sqrt h]
      · rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith), mul_neg_one,
          ← Complex.ofReal_neg, neg_neg]

    have hT := AutomorphicForm.whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
      K D w hw n ((lam : ℝ) : ℂ) ν hν y hcontY hper
      hys hD1 hD2 hΩ hyn (diagOne b') hg₀ ε hε
    set f : ℝ → ℂ := fun uu => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne b' * archRealLiftAt hw (Matrix.of.symm !![ε * Real.sqrt uu, 0; 0, (Real.sqrt uu)⁻¹])) with hfdef
    obtain ⟨hf, hf', hfeq⟩ := hT

    have hsqne : ∀ uu : ℝ, 0 < uu → Real.sqrt uu ≠ 0 := fun uu huu => (Real.sqrt_pos.2 huu).ne'
    have hrel : ∀ uu (huu : 0 < uu),
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne (aOf (ε * uu) (mul_ne_zero hε0 huu.ne'))) =
          ((ξ ⟨zOf (Real.sqrt uu) (hsqne uu huu), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * f uu := by
      intro uu huu
      have hne1 : ε * uu ≠ 0 := mul_ne_zero hε0 huu.ne'
      have hne2 : Real.sqrt uu ≠ 0 := hsqne uu huu
      have hE := (NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar K w hw ε hε uu huu
        (aOf (ε * uu) hne1) b' (zOf (Real.sqrt uu) hne2)
        (haOf_snd _ hne1) hb'_snd (hzOf_snd _ hne2) (hab' _ hne1) hb'_w (haOf_w _ hne1) (hzOf_off _ hne2) (hzOf_w _ hne2)).1
      rw [hE, whittakerCoefficient_mul_centralScalar K _ _ y _ (zOf (Real.sqrt uu) (hsqne uu huu))
        (fun g => hcent _ g) 1]
    have hξsq : ∀ uu (huu : 0 < uu),
        ‖((ξ ⟨zOf (Real.sqrt uu) (hsqne uu huu), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ = uu ^ (w₀ / 2) := by
      intro uu huu
      rw [hξz (Real.sqrt uu) (Real.sqrt_pos.2 huu), Real.sqrt_eq_rpow, ← Real.rpow_mul huu.le]
      ring_nf
    have hξne : ∀ uu (huu : 0 < uu),
        ((ξ ⟨zOf (Real.sqrt uu) (hsqne uu huu), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ≠ 0 := fun uu huu => Units.ne_zero _

    have hNa : ∀ uu (huu : 0 < uu),
        NumberField.TateGlobal.ideleNorm K (aOf (ε * uu) (mul_ne_zero hε0 huu.ne')) = uu * Bn := by
      intro uu huu
      rw [hNgen _ (mul_ne_zero hε0 huu.ne'), abs_mul]
      rcases hε with h | h <;> simp [h, abs_of_pos huu]
    have hfgr : ∃ C N : ℝ, ∀ uu : ℝ, 1 ≤ uu → ‖f uu‖ ≤ C * uu ^ N := by
      refine ⟨M * Bn ^ (w₀ / 2), 0, fun uu huu1 => ?_⟩
      have huu : 0 < uu := by linarith
      rw [Real.rpow_zero, mul_one]
      have h1 := hrel uu huu
      have h2 := hM (diagOne (aOf (ε * uu) (mul_ne_zero hε0 huu.ne')))
      rw [det_diagOne, hNa uu huu, h1, norm_mul, hξsq uu huu, Real.mul_rpow huu.le hBn.le] at h2
      have hpos : 0 < uu ^ (w₀ / 2) := Real.rpow_pos_of_pos huu _
      nlinarith [hpos, h2, norm_nonneg (f uu)]

    suffices hS : ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ uu : ℝ, ∀ huu : 0 < uu, uu ≤ 1 →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne (aOf (ε * uu) (mul_ne_zero hε0 huu.ne'))) = 0 ∨ ‖f uu‖ ≤ C * uu ^ δ by
      obtain ⟨δ, hδ, C, hC⟩ := hS
      refine ⟨δ, hδ, max C 0, fun uu huu huu1 => ?_⟩
      rcases hC uu huu huu1 with h0 | hb
      · rw [h0, norm_zero]; positivity
      · rw [hrel uu huu, norm_mul, hξsq uu huu]
        calc uu ^ (w₀ / 2) * ‖f uu‖ ≤ uu ^ (w₀ / 2) * (max C 0 * uu ^ δ) :=
              mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
                (Real.rpow_nonneg huu.le _))) (Real.rpow_nonneg huu.le _)
          _ = max C 0 * uu ^ (w₀ / 2) * uu ^ δ := by ring
    rcases htri with hA | ⟨εB, k₀, Mn, hεB, hk₀, hlamB, hnB, hlow, Mgr, hMgr⟩ | ⟨hlam0, hinv⟩
    ·
      have hrA : r < 1 / 4 := by rw [hr]; linarith
      have hre : |ν.re| < 1 / 2 := by
        simp only [ν]
        split_ifs with h
        · rw [Complex.ofReal_re, abs_of_nonneg (Real.sqrt_nonneg _)]
          calc Real.sqrt r < Real.sqrt (1 / 4) := Real.sqrt_lt_sqrt h hrA
            _ = 1 / 2 := by
                rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        · simp
      obtain ⟨δ, hδ, C, hC⟩ := LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_abs_re_lt_half
        ν hre (ε * n) f hf hf' (by simpa using hfeq)
      exact ⟨δ, hδ, C, fun uu huu huu1 => Or.inr (hC uu huu huu1)⟩
    ·
      have hKpos : (0 : ℝ) < k₀ + 2 * Mn := by positivity
      by_cases hgood : 0 < ε * (n : ℝ)
      ·
        have hεε : ε * εB = 1 := by
          rw [hnB] at hgood
          rcases hε with h | h <;> rcases hεB with h' | h' <;> subst h <;> subst h' <;> norm_num at hgood ⊢ <;> linarith
        have hk : ε * (n : ℝ) = ((k₀ - 1 : ℕ) : ℝ) + 1 + 2 * (Mn : ℝ) := by
          rw [hnB, ← mul_assoc, hεε, one_mul, Nat.cast_sub (by omega)]; push_cast; ring
        have hrB : r = ((k₀ : ℝ) - 1) ^ 2 / 4 := by rw [hr, hlamB]; ring
        have hk₀R : (2 : ℝ) ≤ k₀ := by exact_mod_cast hk₀
        have hνB : ν = (((k₀ - 1 : ℕ) : ℕ) : ℂ) / 2 := by
          simp only [ν]
          have hr0 : 0 ≤ r := by rw [hrB]; positivity
          rw [if_pos hr0, hrB, show ((k₀ : ℝ) - 1) ^ 2 / 4 = (((k₀ : ℝ) - 1) / 2) ^ 2 by ring,
            Real.sqrt_sq (by linarith)]
          push_cast
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        obtain ⟨δ, hδ, C, hC⟩ :=
          LanglandsTunnell.exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth
            (k₀ - 1) Mn (ε * n) ν hk hνB f hf hf' (by simpa using hfeq) hfgr
        exact ⟨δ, hδ, C, fun uu huu huu1 => Or.inr (hC uu huu huu1)⟩
      ·
        have hεeq : ε = -εB := by
          rw [hnB] at hgood
          rcases hε with h | h <;> rcases hεB with h' | h' <;> subst h <;> subst h' <;> norm_num at hgood ⊢ <;> linarith
        subst hεeq

        have hm := AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt K w hw n y hys hyn
        have hΩ' : archCasimirAt hw y = (((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2)) • y := by
          rw [hΩ, hlamB]; push_cast; rfl

        set Lop : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) := fun z =>
          archDerivAt hw .H z - ((εB : ℂ) * Complex.I) • (archDerivAt hw .E z + archDerivAt hw .Fm z) with hLop
        have hcentL : ∀ (j : ℕ) (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
            (Lop^[j] y) (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * (Lop^[j] y) g :=
          fun j z => central_iterate K hw εB (fun z' => ((ξ ⟨z', Subgroup.mem_top z'⟩ : ℂˣ) : ℂ)) y hcent j z
        have hrelL : ∀ uu (huu : 0 < uu),
            whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (Lop^[Mn] y) 1 (diagOne (aOf (-εB * uu) (mul_ne_zero hε0 huu.ne'))) =
              ((ξ ⟨zOf (Real.sqrt uu) (hsqne uu huu), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
                whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (Lop^[Mn] y) 1
                  (diagOne b' * archRealLiftAt hw (Matrix.of.symm !![-εB * Real.sqrt uu, 0; 0, (Real.sqrt uu)⁻¹])) := by
          intro uu huu
          have hne1 : -εB * uu ≠ 0 := mul_ne_zero hε0 huu.ne'
          have hne2 : Real.sqrt uu ≠ 0 := hsqne uu huu
          have hE := (NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar K w hw (-εB) hε uu huu
            (aOf (-εB * uu) hne1) b' (zOf (Real.sqrt uu) hne2)
            (haOf_snd _ hne1) hb'_snd (hzOf_snd _ hne2) (hab' _ hne1) hb'_w (haOf_w _ hne1) (hzOf_off _ hne2) (hzOf_w _ hne2)).1
          rw [hE, whittakerCoefficient_mul_centralScalar K _ _ (Lop^[Mn] y) _ (zOf (Real.sqrt uu) (hsqne uu huu))
            (fun g => hcentL Mn _ g) 1]
        have hgrowth : ∀ t : ℝ, 1 ≤ t →
            ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (Lop^[Mn] y) 1
                (diagOne b' * archRealLiftAt hw (Matrix.of.symm !![-εB * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]))‖ ≤
              (Mgr * Bn ^ (w₀ / 2)) * t ^ (0 : ℕ) := by
          intro t ht1
          have ht : 0 < t := by linarith
          rw [pow_zero, mul_one]
          have h1 := hrelL t ht
          have h2 := hMgr (diagOne (aOf (-εB * t) (mul_ne_zero hε0 ht.ne')))
          rw [det_diagOne, hNa t ht, h1, norm_mul, hξsq t ht, Real.mul_rpow ht.le hBn.le] at h2
          have hpos : 0 < t ^ (w₀ / 2) := Real.rpow_pos_of_pos ht _
          nlinarith [hpos, h2, norm_nonneg (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (Lop^[Mn] y) 1
                (diagOne b' * archRealLiftAt hw (Matrix.of.symm !![-εB * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹])))]
        refine ⟨1, one_pos, 0, fun uu huu huu1 => Or.inl ?_⟩
        have hOS := AutomorphicForm.whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero
          K D w hw y hcontY hper hys hD εB hεB k₀ Mn (by omega) n hnB hm hΩ' hlow (diagOne b') hg₀
          (Mgr * Bn ^ (w₀ / 2)) 0 hgrowth uu huu
        rw [hrel uu huu]
        show _ * f uu = 0
        rw [show f uu = 0 from hOS, mul_zero]
    ·
      refine ⟨1, one_pos, 0, fun uu huu huu1 => Or.inl ?_⟩
      set a := aOf (ε * uu) (mul_ne_zero hε0 huu.ne') with ha_def
      have haw_ne : e (((a : (AdeleRing (𝓞 K) K))).1 w) ≠ 0 := by
        rw [ha_def, haOf_w _ (mul_ne_zero hε0 huu.ne')]; exact mul_ne_zero hε0 huu.ne'
      set x : ℝ := (e (((a : (AdeleRing (𝓞 K) K))).1 w))⁻¹ * (1 / 2) with hx_def
      have ha2 : ((a : (AdeleRing (𝓞 K) K))).2 = 1 := haOf_snd _ (mul_ne_zero hε0 huu.ne')
      obtain ⟨hE2, hψ⟩ := NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
        K w hw a ha2 x
      have hX : ((a : (AdeleRing (𝓞 K) K))).1 w * e.symm x = e.symm (1 / 2) := by
        have : ((a : (AdeleRing (𝓞 K) K))).1 w = e.symm (e (((a : (AdeleRing (𝓞 K) K))).1 w)) := (e.symm_apply_apply _).symm
        rw [this, ← map_mul]
        congr 1
        rw [hx_def, ← mul_assoc, mul_inv_cancel₀ haw_ne, one_mul]
      rw [← he_def] at hE2 hψ
      rw [hX] at hE2
      have hinvW : whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne a * archRealGLAt hw (unipotentGL2 x)) = whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne a) :=
        whittakerCoefficient_mul_of_rightInvariant K _ _ y _ (fun g => hinv g _ (det_unipotentGL2 x)) 1 _
      have hper' : ∀ (β : K) (uA : (AdeleRing (𝓞 K) K)),
          y (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uA) * diagOne a) = y (unipotentGL2 uA * diagOne a) := by
        intro β uA; rw [unipotentGL2_add, mul_assoc, hper]
      have hcov := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K
        D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (NumberField.StandardAddChar.stdAddChar K)
        (NumberField.StandardAddChar.adelicTraceData K).isGlobalAddChar_psiK.principalInvariant
        y (diagOne a) hper' 1
        (show (AdeleRing (𝓞 K) K) from (Pi.single w (e.symm (1 / 2)), 0))
      rw [map_one, one_mul, hψ, ← hE2, hinvW] at hcov

      have : (2 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne a) = 0 := by linear_combination hcov
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero

  obtain ⟨δ₁, hδ₁, C₁, hC₁⟩ := key 1 one_ne_zero (Or.inl rfl)
  obtain ⟨δ₂, hδ₂, C₂, hC₂⟩ := key (-1) (by norm_num) (Or.inr rfl)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, max (max C₁ C₂) (M * Bn ^ (w₀ / 2)), ?_⟩
  intro a ha hab
  have hm : ((w.mult : ℝ) * w₀ / 2) = w₀ / 2 := by
    rw [InfinitePlace.mult, if_pos hw]; push_cast; ring
  rw [hm]
  set uN : ℝ := ‖((a : (AdeleRing (𝓞 K) K))).1 w‖ with huN
  set t : ℝ := e (((a : (AdeleRing (𝓞 K) K))).1 w) with ht_def
  have ht0 : t ≠ 0 := by
    rw [ht_def, map_ne_zero_iff _ e.injective]; exact (archComp K a w).ne_zero
  have hut : uN = |t| := by
    rw [huN, ht_def, he_def, ← Real.norm_eq_abs, AutomorphicForm.norm_ringEquivRealOfIsReal hw]
  have hupos : 0 < uN := by rw [hut]; exact abs_pos.2 ht0
  have hCmax0 : 0 ≤ max (max C₁ C₂) (M * Bn ^ (w₀ / 2)) := by

    by_cases h : 0 ≤ max C₁ C₂
    · exact h.trans (le_max_left _ _)
    · push Not at h

      have hM0 : 0 ≤ M := by
        have h1 := hM 1
        rw [map_one, show NumberField.TateGlobal.ideleNorm K 1 = 1 by
          rw [NumberField.TateGlobal.ideleNorm, map_one]; rfl, Real.one_rpow, mul_one] at h1
        exact (norm_nonneg _).trans h1
      exact (mul_nonneg hM0 (Real.rpow_nonneg hBn.le _)).trans (le_max_right _ _)
  by_cases hsmall : uN ≤ 1
  ·
    have hsgn : (if 0 < t then (1 : ℝ) else -1) * |t| = t := by
      split_ifs with h
      · rw [one_mul, abs_of_pos h]
      · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) ht0)]; ring
    have haa : a = aOf t ht0 := ha_eq a ha hab ht0
    by_cases hpos : 0 < t
    · have hb := hC₁ |t| (abs_pos.2 ht0) (hut ▸ hsmall)
      have heq : aOf (1 * |t|) (mul_ne_zero one_ne_zero (abs_pos.2 ht0).ne') = a := by
        rw [haa]; exact haOf_congr (1 * |t|) t (mul_ne_zero one_ne_zero (abs_pos.2 ht0).ne') ht0 (by rw [one_mul, abs_of_pos hpos])
      rw [heq, ← hut] at hb
      refine hb.trans ?_
      rw [min_eq_right hsmall]
      have h1 : uN ^ δ₁ ≤ uN ^ min δ₁ δ₂ := Real.rpow_le_rpow_of_exponent_ge hupos hsmall (min_le_left _ _)
      exact mul_le_mul (mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (Real.rpow_nonneg hupos.le _))
        h1 (Real.rpow_nonneg hupos.le _) (mul_nonneg hCmax0 (Real.rpow_nonneg hupos.le _))
    · have hneg : t < 0 := lt_of_le_of_ne (not_lt.1 hpos) ht0
      have hb := hC₂ |t| (abs_pos.2 ht0) (hut ▸ hsmall)
      have heq : aOf (-1 * |t|) (mul_ne_zero (by norm_num) (abs_pos.2 ht0).ne') = a := by
        rw [haa]; exact haOf_congr (-1 * |t|) t (mul_ne_zero (by norm_num) (abs_pos.2 ht0).ne') ht0 (by rw [abs_of_neg hneg]; ring)
      rw [heq, ← hut] at hb
      refine hb.trans ?_
      rw [min_eq_right hsmall]
      have h1 : uN ^ δ₂ ≤ uN ^ min δ₁ δ₂ := Real.rpow_le_rpow_of_exponent_ge hupos hsmall (min_le_right _ _)
      exact mul_le_mul (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (Real.rpow_nonneg hupos.le _))
        h1 (Real.rpow_nonneg hupos.le _) (mul_nonneg hCmax0 (Real.rpow_nonneg hupos.le _))
  ·
    push Not at hsmall
    have hb := hM (diagOne a)
    have haa : a = aOf t ht0 := ha_eq a ha hab ht0
    rw [det_diagOne] at hb
    rw [haa, hNgen t ht0, ← hut, Real.mul_rpow hupos.le hBn.le, ← haa] at hb
    rw [min_eq_left hsmall.le, Real.one_rpow, mul_one]
    refine hb.trans ?_
    calc M * (uN ^ (w₀ / 2) * Bn ^ (w₀ / 2)) = (M * Bn ^ (w₀ / 2)) * uN ^ (w₀ / 2) := by ring
      _ ≤ max (max C₁ C₂) (M * Bn ^ (w₀ / 2)) * uN ^ (w₀ / 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hupos.le _)

theorem main
    (K : Type) [Field K] [NumberField K]
    (h1 : ∀ v v' : InfinitePlace K, v.IsComplex → v'.IsComplex → v = v')
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous y)
    (hxG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g)
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * y g)
    (nw : ∀ v : InfinitePlace K, v.IsReal → ℤ) (lam : ∀ v : InfinitePlace K, v.IsReal → ℝ)
    (hxn : ∀ (v : InfinitePlace K) (hv : v.IsReal), HasArchCharacterAt₀ K v (archWeightCharAt hv (nw v hv)) y)
    (hreg : ∀ (v : InfinitePlace K) (hv : v.IsReal) (l : List ArchDir),
      IsArchSmoothAt hv (l.foldr (archDerivAt hv) y) ∧ Continuous (l.foldr (archDerivAt hv) y))
    (hgr : ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              g‖ ≤
        M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (hcas : ∀ (v : InfinitePlace K) (hv : v.IsReal), archCasimirAt hv y = ((lam v hv : ℝ) : ℂ) • y)
    (harch : ∀ (v : InfinitePlace K) (hv : v.IsReal),
      0 < lam v hv ∨
      (∃ (ε : ℝ) (k₀ M : ℕ), (ε = 1 ∨ ε = -1) ∧ 2 ≤ k₀ ∧ lam v hv = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
        ((nw v hv : ℤ) : ℝ) = ε * (k₀ + 2 * M) ∧ (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M + 1] y = 0 ∧
        ∃ Mgr : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
          ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M] y) 1
              g‖ ≤
            Mgr * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) ∨
      (lam v hv = 0 ∧ ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ),
        Matrix.GeneralLinearGroup.det h = 1 → y (g * archRealGLAt hv h) = y g))
    (hcx : ∀ (v : InfinitePlace K), v.IsComplex → ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ v → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              (diagOne a)‖ ≤
            C * ‖((a : AdeleRing (𝓞 K) K)).1 v‖ ^ ((v.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 v‖) ^ δ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne a)‖ ≤
          C * ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := by
  classical
  have h2 : ∀ w w' : InfinitePlace K, w ≠ w' → w.IsComplex → ¬ w'.IsComplex :=
    fun w w' hne hw hw' => hne (h1 w w' hw hw')
  have hper_of : ∀ (i : InfinitePlace K) (hi : i.IsReal) (β : K) (g : AdelicGL2 (𝓞 K) K),
      y (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = y g := by
    intro i hi β g; rw [unipotentGL2_algebraMap]; exact hxG _ _

  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : InfinitePlace K, ∀ i : InfinitePlace K, i ≠ i₀ → i.IsReal := by
    by_cases hc : ∃ w : InfinitePlace K, w.IsComplex
    · obtain ⟨w, hw⟩ := hc
      refine ⟨w, fun i hi => ?_⟩
      rcases InfinitePlace.isReal_or_isComplex i with h | h
      · exact h
      · exact absurd hw (h2 i w hi h)
    · push Not at hc
      obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
      refine ⟨w, fun i _ => ?_⟩
      rcases InfinitePlace.isReal_or_isComplex i with h | h
      · exact h
      · exact absurd h (hc i)

  have key : ∀ σ : InfinitePlace K → ℝ, (∀ w, σ w = 1 ∨ σ w = -1) →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ∀ w : InfinitePlace K, (w.Completion)ˣ,
        (∀ (w : InfinitePlace K) (hw : w.IsReal),
          0 < σ w * InfinitePlace.Completion.ringEquivRealOfIsReal hw ((t w : (w.Completion)ˣ) : w.Completion)) →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne (archIdele K t))‖ ≤
          C * (∏ v : InfinitePlace K, ‖((t v : (v.Completion)ˣ) : v.Completion)‖ ^ ((v.mult : ℝ) * w₀ / 2)) *
            ∏ v : InfinitePlace K, (min 1 ‖((t v : (v.Completion)ˣ) : v.Completion)‖) ^ δ := by
    intro σ hσ

    let X : InfinitePlace K → Type := fun w =>
      {s : (w.Completion)ˣ // ∀ hw : w.IsReal,
        0 < σ w * InfinitePlace.Completion.ringEquivRealOfIsReal hw ((s : (w.Completion)ˣ) : w.Completion)}
    let val : (∀ w, X w) → ∀ w : InfinitePlace K, (w.Completion)ˣ := fun s w => (s w).1
    let Φ : (∀ w, X w) → ℂ := fun s => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne (archIdele K (val s)))
    by_cases hΦ : ∀ s : ∀ w, X w, Φ s = 0
    · refine ⟨1, one_pos, 0, le_rfl, ?_⟩
      intro t ht
      have h0 : Φ (fun w => ⟨t w, ht w⟩) = 0 := hΦ _
      have : whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne (archIdele K t)) = 0 := h0
      rw [this, norm_zero, zero_mul, zero_mul]
    push Not at hΦ
    obtain ⟨b₀, hb₀⟩ := hΦ

    have hdep : ∀ i : InfinitePlace K, i ≠ i₀ → ∀ b b' : ∀ j, X j,
        ∃ l : ℂ × ℂ, l ≠ 0 ∧ ∀ s : X i,
          l.1 * Φ (Function.update b i s) + l.2 * Φ (Function.update b' i s) = 0 := by
      intro i hi b b'
      have hir : i.IsReal := hi₀ i hi
      obtain ⟨l, hl0, hl⟩ :=
        AutomorphicForm.exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul
          K D ξ i hir (nw i hir) (lam i hir) y hxc (hper_of i hir) hxZ (hreg i hir []).1
          (fun d => (hreg i hir [d]).2) (fun d d' => (hreg i hir [d, d']).2) (hcas i hir) (hxn i hir) w₀ hξ hgr
          (archIdele K (val b)) (archIdele K (val b')) (archIdele_snd K _) (archIdele_snd K _) (σ i) (hσ i)
      refine ⟨l, hl0, fun s => hl (archIdele K (val (Function.update b i s))) (archIdele K (val (Function.update b' i s)))
        (archIdele_snd K _) (archIdele_snd K _) ?_ ?_ ?_ ?_⟩
      · intro w' hw'
        show ((val (Function.update b i s) w' : (w'.Completion)ˣ) : w'.Completion) = ((val b w' : (w'.Completion)ˣ) : w'.Completion)
        simp only [val, Function.update_of_ne hw']
      · intro w' hw'
        show ((val (Function.update b' i s) w' : (w'.Completion)ˣ) : w'.Completion) = ((val b' w' : (w'.Completion)ˣ) : w'.Completion)
        simp only [val, Function.update_of_ne hw']
      · show ((val (Function.update b i s) i : (i.Completion)ˣ) : i.Completion) = ((val (Function.update b' i s) i : (i.Completion)ˣ) : i.Completion)
        simp only [val, Function.update_self]
      · show 0 < σ i * InfinitePlace.Completion.ringEquivRealOfIsReal hir ((val (Function.update b i s) i : (i.Completion)ˣ) : i.Completion)
        simp only [val, Function.update_self]
        exact s.2 hir

    have hfac := Function.mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero Φ i₀ hdep b₀

    have hD : ∀ w : InfinitePlace K, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : (AdeleRing (𝓞 K) K))).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ w → ((a : (AdeleRing (𝓞 K) K))).1 w' = ((archIdele K (val b₀) : (AdeleRing (𝓞 K) K))).1 w') →
          ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne a)‖ ≤ C * ‖((a : (AdeleRing (𝓞 K) K))).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
            (min 1 ‖((a : (AdeleRing (𝓞 K) K))).1 w‖) ^ δ := by
      intro w
      rcases InfinitePlace.isReal_or_isComplex w with hwr | hwc
      · exact dpure_fn K D ξ w₀ hξ w hwr (nw w hwr) (lam w hwr) y hxc hxG hxZ (hxn w hwr) (hreg w hwr []).1
          (fun d => (hreg w hwr [d]).2) (fun d d' => (hreg w hwr [d, d']).2) (fun l => (hreg w hwr l).2)
          (hcas w hwr) hgr (harch w hwr) (archIdele K (val b₀)) (archIdele_snd K _)
      · exact hcx w hwc (archIdele K (val b₀)) (archIdele_snd K _)
    choose δw hδw Cw hCw using hD
    have hne : (Finset.univ : Finset (InfinitePlace K)).Nonempty := Finset.univ_nonempty
    let δ : ℝ := Finset.univ.inf' hne fun w => δw w
    have hδpos : 0 < δ := (Finset.lt_inf'_iff hne).2 fun w _ => hδw w
    have hδle : ∀ w : InfinitePlace K, δ ≤ δw w := fun w => Finset.inf'_le _ (Finset.mem_univ w)
    let n : ℕ := Fintype.card (InfinitePlace K)
    let C : ℝ := (‖Φ b₀‖⁻¹) ^ (n - 1) * ∏ w, max (Cw w) 0
    have hC : 0 ≤ C :=
      mul_nonneg (pow_nonneg (inv_nonneg.2 (norm_nonneg _)) _) (Finset.prod_nonneg fun w _ => le_max_right _ _)
    refine ⟨δ, hδpos, C, hC, ?_⟩
    intro t ht
    let s : ∀ w, X w := fun w => ⟨t w, ht w⟩
    have hvs : val s = t := rfl

    have hprod : Φ s * Φ b₀ ^ (n - 1) = ∏ i, Φ (Function.update b₀ i (s i)) := by
      rw [hfac s, ← Finset.mul_prod_erase Finset.univ (fun i => Φ (Function.update b₀ i (s i))) (Finset.mem_univ i₀)]
    have hnorm : ‖Φ s‖ = (‖Φ b₀‖⁻¹) ^ (n - 1) * ∏ i, ‖Φ (Function.update b₀ i (s i))‖ := by
      have h := congrArg (fun z : ℂ => ‖z‖) hprod
      simp only [norm_mul, norm_pow] at h
      rw [← norm_prod]
      have hb : ‖Φ b₀‖ ^ (n - 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hb₀)
      rw [inv_pow, eq_inv_mul_iff_mul_eq₀ hb, mul_comm]
      exact h

    have hb : ∀ i : InfinitePlace K, ‖Φ (Function.update b₀ i (s i))‖ ≤
        max (Cw i) 0 * ‖((t i : (i.Completion)ˣ) : i.Completion)‖ ^ ((i.mult : ℝ) * w₀ / 2) *
          (min 1 ‖((t i : (i.Completion)ˣ) : i.Completion)‖) ^ δw i := by
      intro i
      have h := hCw i (archIdele K (val (Function.update b₀ i (s i)))) (archIdele_snd K _) (fun w' hw' => by
        show ((val (Function.update b₀ i (s i)) w' : (w'.Completion)ˣ) : w'.Completion) = ((val b₀ w' : (w'.Completion)ˣ) : w'.Completion)
        simp only [val, Function.update_of_ne hw'])
      have hcomp : ((archIdele K (val (Function.update b₀ i (s i))) : (AdeleRing (𝓞 K) K))).1 i = ((t i : (i.Completion)ˣ) : i.Completion) := by
        show ((val (Function.update b₀ i (s i)) i : (i.Completion)ˣ) : i.Completion) = _
        simp only [val, Function.update_self]
        rfl
      rw [hcomp] at h
      refine h.trans ?_
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _)

    have hu : ∀ i : InfinitePlace K, 0 < ‖((t i : (i.Completion)ˣ) : i.Completion)‖ := fun i =>
      norm_pos_iff.2 (t i).ne_zero
    have hN : NumberField.TateGlobal.ideleNorm K (archIdele K t) =
        ∏ w, ‖((t w : (w.Completion)ˣ) : w.Completion)‖ ^ w.mult :=
      NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K (archIdele K t) (archIdele_snd K t)

    calc ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne (archIdele K t))‖ = ‖Φ s‖ := rfl
      _ = (‖Φ b₀‖⁻¹) ^ (n - 1) * ∏ i, ‖Φ (Function.update b₀ i (s i))‖ := hnorm
      _ ≤ (‖Φ b₀‖⁻¹) ^ (n - 1) * ∏ i, (max (Cw i) 0 * ‖((t i : (i.Completion)ˣ) : i.Completion)‖ ^ ((i.mult : ℝ) * w₀ / 2) *
            (min 1 ‖((t i : (i.Completion)ˣ) : i.Completion)‖) ^ δw i) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (inv_nonneg.2 (norm_nonneg _)) _)
          exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hb i
      _ = C * (∏ i, ‖((t i : (i.Completion)ˣ) : i.Completion)‖ ^ ((i.mult : ℝ) * (w₀ / 2))) *
            ∏ i, (min 1 ‖((t i : (i.Completion)ˣ) : i.Completion)‖) ^ δw i := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
          simp only [C]
          have : ∀ i : InfinitePlace K, ((i.mult : ℝ) * w₀ / 2) = ((i.mult : ℝ) * (w₀ / 2)) := fun i => by ring
          simp_rw [this]
          ring
      _ ≤ C * (∏ i, ‖((t i : (i.Completion)ˣ) : i.Completion)‖ ^ ((i.mult : ℝ) * w₀ / 2)) *
            ∏ i, (min 1 ‖((t i : (i.Completion)ˣ) : i.Completion)‖) ^ δ := by
          have : ∀ i : InfinitePlace K, ((i.mult : ℝ) * (w₀ / 2)) = ((i.mult : ℝ) * w₀ / 2) := fun i => by ring
          simp_rw [this]
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _))
          exact Finset.prod_le_prod (fun i _ => Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _)
            fun i _ => Real.rpow_le_rpow_of_exponent_ge (lt_min one_pos (hu i)) (min_le_left _ _) (hδle i)

  let pats : Finset (InfinitePlace K → ℝ) := Fintype.piFinset fun _ => ({1, -1} : Finset ℝ)
  have hpat : ∀ σ ∈ pats, ∀ w, σ w = 1 ∨ σ w = -1 := by
    intro σ hσ w
    have h := Fintype.mem_piFinset.1 hσ w
    simpa using h
  have key' : ∀ σ : InfinitePlace K → ℝ, ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ (σ ∈ pats → ∀ t : ∀ w : InfinitePlace K, (w.Completion)ˣ,
        (∀ (w : InfinitePlace K) (hw : w.IsReal),
          0 < σ w * InfinitePlace.Completion.ringEquivRealOfIsReal hw ((t w : (w.Completion)ˣ) : w.Completion)) →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne (archIdele K t))‖ ≤
          C * (∏ v : InfinitePlace K, ‖((t v : (v.Completion)ˣ) : v.Completion)‖ ^ ((v.mult : ℝ) * w₀ / 2)) *
            ∏ v : InfinitePlace K, (min 1 ‖((t v : (v.Completion)ˣ) : v.Completion)‖) ^ δ) := by
    intro σ
    by_cases hσ : σ ∈ pats
    · obtain ⟨δ, hδ, C, hC, h⟩ := key σ (hpat σ hσ)
      exact ⟨δ, hδ, C, hC, fun _ => h⟩
    · exact ⟨1, one_pos, 0, le_rfl, fun h => absurd h hσ⟩
  choose δp hδp Cp hCp0 hCp using key'
  have hpne : pats.Nonempty := ⟨fun _ => 1, Fintype.mem_piFinset.2 fun _ => by simp⟩
  refine ⟨pats.inf' hpne δp, (Finset.lt_inf'_iff hpne).2 fun σ _ => hδp σ, ∑ σ ∈ pats, Cp σ, ?_⟩
  intro a ha2
  rw [Finset.prod_mul_distrib, ← mul_assoc]

  let σ : InfinitePlace K → ℝ := fun w =>
    if hw : w.IsReal then
      (if 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (((a : (AdeleRing (𝓞 K) K))).1 w) then 1 else -1)
    else 1
  have hσmem : σ ∈ pats := Fintype.mem_piFinset.2 fun w => by
    simp only [σ]
    split_ifs <;> simp
  have ht : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < σ w * InfinitePlace.Completion.ringEquivRealOfIsReal hw ((archComp K a w : (w.Completion)ˣ) : w.Completion) := by
    intro w hw
    have hne : InfinitePlace.Completion.ringEquivRealOfIsReal hw (((a : (AdeleRing (𝓞 K) K))).1 w) ≠ 0 := by
      rw [map_ne_zero_iff _ (InfinitePlace.Completion.ringEquivRealOfIsReal hw).injective]
      exact (archComp K a w).ne_zero
    rw [archComp_val]
    simp only [σ, dif_pos hw]
    split_ifs with hpos
    · rwa [one_mul]
    · have hlt : InfinitePlace.Completion.ringEquivRealOfIsReal hw (((a : (AdeleRing (𝓞 K) K))).1 w) < 0 :=
        lt_of_le_of_ne (not_lt.1 hpos) hne
      nlinarith
  have hbound := hCp σ hσmem (archComp K a) ht
  rw [archIdele_archComp K a ha2] at hbound
  simp only [archComp_val] at hbound
  have hu' : ∀ v : InfinitePlace K, 0 < ‖((a : (AdeleRing (𝓞 K) K))).1 v‖ := fun v =>
    norm_pos_iff.2 (archComp K a v).ne_zero
  have hP : 0 ≤ ∏ v : InfinitePlace K, ‖((a : (AdeleRing (𝓞 K) K))).1 v‖ ^ ((v.mult : ℝ) * w₀ / 2) :=
    Finset.prod_nonneg fun v _ => Real.rpow_nonneg (norm_nonneg _) _
  calc ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne a)‖
      ≤ Cp σ * (∏ v : InfinitePlace K, ‖((a : (AdeleRing (𝓞 K) K))).1 v‖ ^ ((v.mult : ℝ) * w₀ / 2)) *
          ∏ v : InfinitePlace K, (min 1 ‖((a : (AdeleRing (𝓞 K) K))).1 v‖) ^ δp σ := hbound
    _ ≤ (∑ σ' ∈ pats, Cp σ') * (∏ v : InfinitePlace K, ‖((a : (AdeleRing (𝓞 K) K))).1 v‖ ^ ((v.mult : ℝ) * w₀ / 2)) *
          ∏ v : InfinitePlace K, (min 1 ‖((a : (AdeleRing (𝓞 K) K))).1 v‖) ^ pats.inf' hpne δp := by
        apply mul_le_mul _ _ (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _)
          (mul_nonneg (Finset.sum_nonneg fun σ' _ => hCp0 σ') hP)
        · exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun σ' _ => hCp0 σ') hσmem) hP
        · exact Finset.prod_le_prod (fun v _ => Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _)
            fun v _ => Real.rpow_le_rpow_of_exponent_ge (lt_min one_pos (hu' v)) (min_le_left _ _)
              (Finset.inf'_le _ hσmem)

end AutomorphicForm.Core25

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (h1 : ∀ v v' : InfinitePlace K, v.IsComplex → v'.IsComplex → v = v')
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x)
    (hxG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x g)
    (nw : ∀ v : InfinitePlace K, v.IsReal → ℤ) (lam : ∀ v : InfinitePlace K, v.IsReal → ℝ)
    (hxn : ∀ (v : InfinitePlace K) (hv : v.IsReal), HasArchCharacterAt₀ K v (archWeightCharAt hv (nw v hv)) x)
    (hreg : ∀ (v : InfinitePlace K) (hv : v.IsReal) (l : List ArchDir),
      IsArchSmoothAt hv (l.foldr (archDerivAt hv) x) ∧ Continuous (l.foldr (archDerivAt hv) x))
    (hgr : ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              g‖ ≤
        C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (hcas : ∀ (v : InfinitePlace K) (hv : v.IsReal), archCasimirAt hv x = ((lam v hv : ℝ) : ℂ) • x)
    (harch : ∀ (v : InfinitePlace K) (hv : v.IsReal),
      0 < lam v hv ∨
      (∃ (ε : ℝ) (k₀ M : ℕ), (ε = 1 ∨ ε = -1) ∧ 2 ≤ k₀ ∧ lam v hv = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
        ((nw v hv : ℤ) : ℝ) = ε * (k₀ + 2 * M) ∧ (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M + 1] x = 0 ∧
        ∃ Mgr : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
          ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M] x) 1
              g‖ ≤
            Mgr * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) ∨
      (lam v hv = 0 ∧ ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ),
        Matrix.GeneralLinearGroup.det h = 1 → x (g * archRealGLAt hv h) = x g))
    (hcx : ∀ (v : InfinitePlace K), v.IsComplex → ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ v → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (diagOne a)‖ ≤
            C * ‖((a : AdeleRing (𝓞 K) K)).1 v‖ ^ ((v.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 v‖) ^ δ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (diagOne a)‖ ≤
          C * ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) :=
  AutomorphicForm.Core25.main K h1 D ξ w₀ hξ x hxc hxG hxZ nw lam hxn hreg hgr hcas harch hcx

end S_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy (solution)
