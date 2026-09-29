-- Prove2me | solution 1 for AutomorphicForm.exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/fd4b9247-f553-5e30-be86-ceafbe1e4af1

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
import Theorems.Thm_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_AdelicLevel_diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup unipotentGL2 unipotentGL2_coe archRealLiftAt IsArchSmoothAt ArchDir archDerivAt archCasimirAt norm_ringEquivRealOfIsReal archWeightCharAt HasArchCharacterAt₀ whittakerCoefficient whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt"
namespace UFn25Idele
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

end AutomorphicForm.UFn25Idele

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup unipotentGL2 unipotentGL2_coe archRealLiftAt IsArchSmoothAt ArchDir archDerivAt archCasimirAt norm_ringEquivRealOfIsReal archWeightCharAt HasArchCharacterAt₀ whittakerCoefficient whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt"
namespace UFn25Aux
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

end AutomorphicForm.UFn25Aux

open AutomorphicForm.UFn25Idele AutomorphicForm.UFn25Aux MeasureTheory

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar finiteAdelicGL2Subgroup unipotentGL2 unipotentGL2_coe archRealLiftAt IsArchSmoothAt ArchDir archDerivAt archCasimirAt norm_ringEquivRealOfIsReal archWeightCharAt HasArchCharacterAt₀ whittakerCoefficient whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt"
namespace UFn25
p2m_open "AutomorphicForm"

theorem main
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ) (lam : ℝ)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hyc : Continuous y)
    (hper : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      y (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = y g)
    (hcent : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * y g)
    (hys : IsArchSmoothAt hw y)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d y))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' y)))
    (hΩ : archCasimirAt hw y = ((lam : ℝ) : ℂ) • y)
    (hn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (hgr : ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 g‖ ≤ M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (b b' : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1) (hb' : ((b' : AdeleRing (𝓞 K) K)).2 = 1)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ∃ l : ℂ × ℂ, l ≠ 0 ∧
      ∀ a a' : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ((a' : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a' : AdeleRing (𝓞 K) K)).1 w' = ((b' : AdeleRing (𝓞 K) K)).1 w') →
        ((a : AdeleRing (𝓞 K) K)).1 w = ((a' : AdeleRing (𝓞 K) K)).1 w →
        0 < ε * InfinitePlace.Completion.ringEquivRealOfIsReal hw (((a : AdeleRing (𝓞 K) K)).1 w) →
        (l.1 * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne a) +
          l.2 * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne a')) = 0 := by
  classical
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he_def
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> rw [h] <;> norm_num
  have hεsq : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
  obtain ⟨Mg, hMg⟩ := hgr

  have hsymm_ne : ∀ t : ℝ, t ≠ 0 → e.symm t ≠ 0 := fun t ht h => ht (by simpa using congrArg e h)
  let unitAt : ∀ t : ℝ, t ≠ 0 → (w.Completion)ˣ := fun t ht => Units.mk0 (e.symm t) (hsymm_ne t ht)
  let aOf : (AdeleRing (𝓞 K) K)ˣ → ∀ t : ℝ, t ≠ 0 → (AdeleRing (𝓞 K) K)ˣ :=
    fun β t ht => archIdele K (Function.update (archComp K β) w (unitAt t ht))
  let bOne : (AdeleRing (𝓞 K) K)ˣ → (AdeleRing (𝓞 K) K)ˣ := fun β => archIdele K (Function.update (archComp K β) w 1)
  have haOf_snd : ∀ β t ht, ((aOf β t ht : (AdeleRing (𝓞 K) K))).2 = 1 := fun β t ht => archIdele_snd K _
  have haOf_w : ∀ β t ht, e (((aOf β t ht : (AdeleRing (𝓞 K) K))).1 w) = t := by
    intro β t ht
    show e ((Function.update (archComp K β) w (unitAt t ht) w : (w.Completion)ˣ) : w.Completion) = t
    rw [Function.update_self]; show e (e.symm t) = t; exact e.apply_symm_apply t
  have haOf_off : ∀ β t ht (w' : InfinitePlace K), w' ≠ w →
      ((aOf β t ht : (AdeleRing (𝓞 K) K))).1 w' = ((β : (AdeleRing (𝓞 K) K))).1 w' := by
    intro β t ht w' hw'
    show ((Function.update (archComp K β) w (unitAt t ht) w' : (w'.Completion)ˣ) : w'.Completion) = _
    rw [Function.update_of_ne hw']; rfl
  have hbOne_snd : ∀ β, ((bOne β : (AdeleRing (𝓞 K) K))).2 = 1 := fun β => archIdele_snd K _
  have hbOne_w : ∀ β, ((bOne β : (AdeleRing (𝓞 K) K))).1 w = 1 := by
    intro β
    show ((Function.update (archComp K β) w 1 w : (w.Completion)ˣ) : w.Completion) = 1
    rw [Function.update_self]; rfl
  have hab1 : ∀ β t ht (w' : InfinitePlace K), w' ≠ w →
      ((aOf β t ht : (AdeleRing (𝓞 K) K))).1 w' = ((bOne β : (AdeleRing (𝓞 K) K))).1 w' := by
    intro β t ht w' hw'
    rw [haOf_off β t ht w' hw']
    show _ = ((Function.update (archComp K β) w 1 w' : (w'.Completion)ˣ) : w'.Completion)
    rw [Function.update_of_ne hw']; rfl

  have ha_eq : ∀ (β a : (AdeleRing (𝓞 K) K)ˣ), ((a : (AdeleRing (𝓞 K) K))).2 = 1 →
      (∀ w' : InfinitePlace K, w' ≠ w → ((a : (AdeleRing (𝓞 K) K))).1 w' = ((β : (AdeleRing (𝓞 K) K))).1 w') →
      ∀ (ht : e (((a : (AdeleRing (𝓞 K) K))).1 w) ≠ 0), a = aOf β (e (((a : (AdeleRing (𝓞 K) K))).1 w)) ht := by
    intro β a ha hab ht
    have h1 : archIdele K (archComp K a) = a := archIdele_archComp K a ha
    have h2 : archComp K a = Function.update (archComp K β) w (unitAt (e (((a : (AdeleRing (𝓞 K) K))).1 w)) ht) := by
      funext w'
      by_cases hw' : w' = w
      · subst hw'; rw [Function.update_self]; apply Units.ext
        show ((a : (AdeleRing (𝓞 K) K))).1 w' = e.symm (e (((a : (AdeleRing (𝓞 K) K))).1 w')); exact (e.symm_apply_apply _).symm
      · rw [Function.update_of_ne hw']; apply Units.ext; exact hab w' hw'
    calc a = archIdele K (archComp K a) := h1.symm
      _ = aOf β (e (((a : (AdeleRing (𝓞 K) K))).1 w)) ht := by rw [h2]

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
  have hsqne : ∀ s : ℝ, 0 < s → Real.sqrt s ≠ 0 := fun s hs => (Real.sqrt_pos.2 hs).ne'
  have hξsq : ∀ s (hs : 0 < s),
      ‖((ξ ⟨zOf (Real.sqrt s) (hsqne s hs), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ = s ^ (w₀ / 2) := by
    intro s hs
    rw [hξz (Real.sqrt s) (Real.sqrt_pos.2 hs), Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
    ring_nf

  have hg₀ : ∀ β, archComponent K w (glArch (𝓞 K) K (diagOne (bOne β))) = 1 := fun β =>
    (NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar K w hw 1 (Or.inl rfl) 1 one_pos
      (bOne β) (bOne β) (zOf 1 one_ne_zero) (hbOne_snd β) (hbOne_snd β) (hzOf_snd 1 one_ne_zero) (fun _ _ => rfl) (hbOne_w β)
      (by rw [hbOne_w, map_one]; norm_num) (hzOf_off 1 one_ne_zero) (by rw [hzOf_w 1 one_ne_zero]; simp)).2

  have hNgen : ∀ β t (ht : t ≠ 0), NumberField.TateGlobal.ideleNorm K (aOf β t ht) =
      |t| * ∏ w' ∈ Finset.univ.erase w, ‖((β : (AdeleRing (𝓞 K) K))).1 w'‖ ^ w'.mult := by
    intro β t ht
    rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _ (haOf_snd β _ ht),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
    congr 1
    · rw [InfinitePlace.mult, if_pos hw, pow_one, ← AutomorphicForm.norm_ringEquivRealOfIsReal hw, ← he_def,
        haOf_w β _ ht, Real.norm_eq_abs]
    · exact Finset.prod_congr rfl fun w' hw' => by rw [haOf_off β _ ht w' (Finset.ne_of_mem_erase hw')]

  set r : ℝ := 1 / 4 - lam with hr
  let ν : ℂ := if 0 ≤ r then ((Real.sqrt r : ℝ) : ℂ) else ((Real.sqrt (-r) : ℝ) : ℂ) * Complex.I
  have hν : ν ^ 2 = 1 / 4 - ((lam : ℝ) : ℂ) := by
    have hlamre : (1 / 4 : ℂ) - ((lam : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by rw [hr]; push_cast; ring
    rw [hlamre]
    simp only [ν]
    split_ifs with h
    · rw [← Complex.ofReal_pow, Real.sq_sqrt h]
    · rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith), mul_neg_one,
        ← Complex.ofReal_neg, neg_neg]
  have hνim : (ν ^ 2).im = 0 := by
    rw [hν]; simp

  let f : (AdeleRing (𝓞 K) K)ˣ → ℝ → ℂ := fun β uu =>
    whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne (bOne β) * archRealLiftAt hw (Matrix.of.symm !![ε * Real.sqrt uu, 0; 0, (Real.sqrt uu)⁻¹]))
  have hT : ∀ β, DifferentiableOn ℝ (f β) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f β)) (Set.Ioi 0) ∧
      ∀ uu : ℝ, 0 < uu → (uu : ℂ) ^ 2 * deriv (deriv (f β)) uu +
        (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * n : ℝ) : ℂ) * (uu : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (uu : ℂ) ^ 2) * f β uu = 0 :=
    fun β => AutomorphicForm.whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
      K D w hw n ((lam : ℝ) : ℂ) ν hν y hyc hper hys hD1 hD2 hΩ hn (diagOne (bOne β)) (hg₀ β) ε hε
  have hrel : ∀ β uu (huu : 0 < uu),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1 (diagOne (aOf β (ε * uu) (mul_ne_zero hε0 huu.ne'))) =
        ((ξ ⟨zOf (Real.sqrt uu) (hsqne uu huu), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * f β uu := by
    intro β uu huu
    have hne1 : ε * uu ≠ 0 := mul_ne_zero hε0 huu.ne'
    have hne2 : Real.sqrt uu ≠ 0 := hsqne uu huu
    have hE := (NumberField.AdelicLevel.diagOne_eq_diagOne_mul_archRealLiftAt_mul_centralScalar K w hw ε hε uu huu
      (aOf β (ε * uu) hne1) (bOne β) (zOf (Real.sqrt uu) hne2)
      (haOf_snd β _ hne1) (hbOne_snd β) (hzOf_snd _ hne2) (hab1 β _ hne1) (hbOne_w β) (haOf_w β _ hne1)
      (hzOf_off _ hne2) (hzOf_w _ hne2)).1
    rw [hE, whittakerCoefficient_mul_centralScalar K _ _ y _ (zOf (Real.sqrt uu) (hsqne uu huu))
      (fun g => hcent _ g) 1]
  have hfgr : ∀ β, ∃ C N : ℝ, ∀ uu : ℝ, 1 ≤ uu → ‖f β uu‖ ≤ C * uu ^ N := by
    intro β
    set Bn : ℝ := ∏ w' ∈ Finset.univ.erase w, ‖((β : (AdeleRing (𝓞 K) K))).1 w'‖ ^ w'.mult with hBn_def
    have hBn : 0 < Bn := Finset.prod_pos fun w' _ => pow_pos (norm_pos_iff.2 (archComp K β w').ne_zero) _
    refine ⟨Mg * Bn ^ (w₀ / 2), 0, fun uu huu1 => ?_⟩
    have huu : 0 < uu := by linarith
    rw [Real.rpow_zero, mul_one]
    have h1 := hrel β uu huu
    have h2 := hMg (diagOne (aOf β (ε * uu) (mul_ne_zero hε0 huu.ne')))
    have hNa : NumberField.TateGlobal.ideleNorm K (aOf β (ε * uu) (mul_ne_zero hε0 huu.ne')) = uu * Bn := by
      rw [hNgen β _ (mul_ne_zero hε0 huu.ne'), abs_mul, hBn_def]
      rcases hε with h | h <;> simp [h, abs_of_pos huu]
    rw [det_diagOne, hNa, h1, norm_mul, hξsq uu huu, Real.mul_rpow huu.le hBn.le] at h2
    have hpos : 0 < uu ^ (w₀ / 2) := Real.rpow_pos_of_pos huu _
    nlinarith [hpos, h2, norm_nonneg (f β uu)]

  obtain ⟨hfb, hfb', hfbeq⟩ := hT b
  obtain ⟨hgb, hgb', hgbeq⟩ := hT b'
  obtain ⟨c₁, c₂, hc, hdep⟩ := LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth ν hνim (ε * n)
    (f b) (f b') hfb hfb' (by simpa using hfbeq) (hfgr b) hgb hgb' (by simpa using hgbeq) (hfgr b')
  refine ⟨(c₁, c₂), hc, fun a a' ha ha' hab hab' haa' hpos => ?_⟩

  set t : ℝ := e (((a : (AdeleRing (𝓞 K) K))).1 w) with ht_def
  have ht' : e (((a' : (AdeleRing (𝓞 K) K))).1 w) = t := by rw [ht_def, haa']
  set uu : ℝ := ε * t with huu_def
  have huu : 0 < uu := hpos
  have htu : t = ε * uu := by rw [huu_def, ← mul_assoc, hεsq, one_mul]
  have hne : ε * uu ≠ 0 := mul_ne_zero hε0 huu.ne'
  have ht0 : t ≠ 0 := by rw [htu]; exact hne
  have haOf_congr : ∀ β t₁ t₂ (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0), t₁ = t₂ → aOf β t₁ h₁ = aOf β t₂ h₂ := by
    intro β t₁ t₂ h₁ h₂ h; subst h; rfl
  have ht0a : e (((a : (AdeleRing (𝓞 K) K))).1 w) ≠ 0 := by rw [← ht_def]; exact ht0
  have ht0a' : e (((a' : (AdeleRing (𝓞 K) K))).1 w) ≠ 0 := by rw [ht']; exact ht0
  have ha1 : a = aOf b (ε * uu) hne :=
    (ha_eq b a ha hab ht0a).trans (haOf_congr b _ _ ht0a hne (by rw [← ht_def, htu]))
  have ha2 : a' = aOf b' (ε * uu) hne :=
    (ha_eq b' a' ha' hab' ht0a').trans (haOf_congr b' _ _ ht0a' hne (by rw [ht', htu]))
  show c₁ * _ + c₂ * _ = 0
  rw [ha1, ha2, hrel b uu huu, hrel b' uu huu]
  have h0 := hdep uu huu
  calc c₁ * (_ * f b uu) + c₂ * (_ * f b' uu)
      = ((ξ ⟨zOf (Real.sqrt uu) (hsqne uu huu), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * (c₁ * f b uu + c₂ * f b' uu) := by ring
    _ = 0 := by rw [h0, mul_zero]

end AutomorphicForm.UFn25

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ) (lam : ℝ)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hyc : Continuous y)
    (hper : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      y (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = y g)
    (hcent : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * y g)
    (hys : IsArchSmoothAt hw y)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d y))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' y)))
    (hΩ : archCasimirAt hw y = ((lam : ℝ) : ℂ) • y)
    (hn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (hgr : ∃ M : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              g‖ ≤ M * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (b b' : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1) (hb' : ((b' : AdeleRing (𝓞 K) K)).2 = 1)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ∃ l : ℂ × ℂ, l ≠ 0 ∧
      ∀ a a' : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ((a' : AdeleRing (𝓞 K) K)).2 = 1 →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
        (∀ w' : InfinitePlace K, w' ≠ w → ((a' : AdeleRing (𝓞 K) K)).1 w' = ((b' : AdeleRing (𝓞 K) K)).1 w') →
        ((a : AdeleRing (𝓞 K) K)).1 w = ((a' : AdeleRing (𝓞 K) K)).1 w →
        0 < ε * InfinitePlace.Completion.ringEquivRealOfIsReal hw (((a : AdeleRing (𝓞 K) K)).1 w) →
        l.1 * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              (diagOne a) +
          l.2 * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              (diagOne a') = 0 :=
  AutomorphicForm.UFn25.main K D ξ w hw n lam y hyc hper hcent hys hD1 hD2 hΩ hn w₀ hξ hgr b b' hb hb' ε hε

end S_AutomorphicForm_exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_exists_ne_zero_forall_linearCombination_whittakerCoefficient_diagOne_eq_zero_of_archCasimirAt_eq_smul (solution)
