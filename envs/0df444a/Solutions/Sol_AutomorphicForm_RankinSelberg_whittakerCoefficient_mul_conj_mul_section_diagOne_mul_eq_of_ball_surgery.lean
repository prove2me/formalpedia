-- Prove2me | solution 1 for AutomorphicForm.RankinSelberg.whittakerCoefficient_mul_conj_mul_section_diagOne_mul_eq_of_ball_surgery
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/1529454b-c1d8-57c4-acbd-92e168ce62e1

import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_RankinSelberg_whittakerCoefficient_mul_conj_mul_section_diagOne_mul_eq_of_ball_surgery
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped ENNReal NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace RS12W

variable (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)

theorem whittakerCoefficient_mul_right (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g k : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (g * k) = whittakerCoefficient F pins ψ (fun y => φ (y * k)) α g := by
  letI := pins.nS
  simp only [whittakerCoefficient, mul_assoc]

theorem whittakerCoefficient_mul_right_eq_of_forall (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g k : AdelicGL2 (𝓞 F) F)
    (hk : ∀ y, φ (y * k) = φ y) :
    whittakerCoefficient F pins ψ φ α (g * k) = whittakerCoefficient F pins ψ φ α g := by
  rw [whittakerCoefficient_mul_right]
  congr 1
  funext y
  exact hk y

theorem whittakerCoefficient_mul_central (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g c : AdelicGL2 (𝓞 F) F) (ω : ℂ)
    (hcomm : ∀ h : AdelicGL2 (𝓞 F) F, h * c = c * h) (hc : ∀ h, φ (c * h) = ω * φ h) :
    whittakerCoefficient F pins ψ φ α (g * c) = ω * whittakerCoefficient F pins ψ φ α g := by
  letI := pins.nS
  simp only [whittakerCoefficient]
  rw [← integral_const_mul]
  congr 1
  funext u
  rw [← mul_assoc, hcomm (unipotentGL2 u * g), hc]
  ring

theorem sum_whittakerCoefficient_mul_right_eq {ι : Type*} [Fintype ι] (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) (r : ι → AdelicGL2 (𝓞 F) F) (a : ℂ)
    (hsum : ∀ h : AdelicGL2 (𝓞 F) F, (∑ j, φ (h * r j)) = a * φ h)
    (hint : ∀ j, WhittakerCoefficientIntegrable F pins ψ (fun y => φ (y * r j)) α g) :
    (∑ j, whittakerCoefficient F pins ψ φ α (g * r j)) = a * whittakerCoefficient F pins ψ φ α g := by
  letI := pins.nS
  simp only [whittakerCoefficient_mul_right]
  simp only [whittakerCoefficient]
  rw [← integral_finset_sum _ (fun j _ => hint j), ← integral_const_mul]
  congr 1
  funext u
  rw [← Finset.sum_mul, hsum]
  ring

end RS12W

namespace RS37P4
theorem unipotentGL2_algebraMap_eq_globalPoints (K : Type) [Field K] [NumberField K] (β : K) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) = globalPoints (𝓞 K) K (unipotentGL2 β) := by
  refine Units.ext ?_
  ext i j
  simp only [unipotentGL2_coe, globalPoints, Matrix.GeneralLinearGroup.map_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem glArch_unipotentGL2_eq_one (K : Type) [Field K] [NumberField K]
    (y : AdeleRing (𝓞 K) K) (hy : y.1 = 0) : glArch (𝓞 K) K (unipotentGL2 y) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, unipotentGL2_coe, Units.val_one]
  fin_cases i <;> fin_cases j <;> first | rfl | simp [hy] | simp [hy, Prod.fst_one, Prod.fst_zero]

theorem glArch_diagOne_of_fst_eq_one (K : Type) [Field K] [NumberField K]
    (ε : (AdeleRing (𝓞 K) K)ˣ) (hε : ((ε : AdeleRing (𝓞 K) K)).1 = 1) : glArch (𝓞 K) K (diagOne ε) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, diagOne_coe_apply, Units.val_one]
  fin_cases i <;> fin_cases j <;> (try simp [Matrix.diagonal, Matrix.one_apply, hε]) <;> rfl

variable (K : Type) [Field K] [NumberField K] in
theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (h : AdelicGL2 (𝓞 K) K) :
    h * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * h := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  change (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) ((z : AdeleRing (𝓞 K) K)) =
    Matrix.scalar (Fin 2) ((z : AdeleRing (𝓞 K) K)) * (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq.symm

end RS37P4

namespace RS27

variable (K : Type) [Field K] [NumberField K]

theorem gl_ext {g h : AdelicGL2 (𝓞 K) K} (h₁ : glArch (𝓞 K) K g = glArch (𝓞 K) K h)
    (h₂ : ∀ u, finComponent (𝓞 K) K u (glFin (𝓞 K) K g) = finComponent (𝓞 K) K u (glFin (𝓞 K) K h)) :
    g = h := by
  apply Units.ext
  ext i j
  apply Prod.ext
  · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing K) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) h₁) i) j
    rwa [glArch_apply, glArch_apply] at this
  · refine RestrictedProduct.ext _ _ fun u => ?_
    have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (u.adicCompletion K) => (m : Matrix (Fin 2) (Fin 2) (u.adicCompletion K))) (h₂ u)) i) j
    rwa [finComponent_apply, finComponent_apply, glFin_apply, glFin_apply] at this

theorem commute_placeEmbed_of_finComponent_eq_one {κ : AdelicGL2 (𝓞 K) K} (hκa : glArch (𝓞 K) K κ = 1)
    {v : HeightOneSpectrum (𝓞 K)} (hκv : finComponent (𝓞 K) K v (glFin (𝓞 K) K κ) = 1)
    (xv : GL (Fin 2) (v.adicCompletion K)) :
    κ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * κ := by
  have hP : UnramifiedWhittaker.placeEmbed K v xv = AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v xv) := rfl
  refine gl_ext K ?_ fun u => ?_
  · rw [map_mul, map_mul, hP, AdelicDock.glArch_finEmbed, hκa]
  · rw [map_mul, map_mul, map_mul, map_mul]
    by_cases hu : u = v
    · subst hu
      rw [hκv, one_mul, mul_one]
    · rw [hP, AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hu, mul_one, one_mul]

noncomputable def evalAt (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →+* v.adicCompletion K :=
  (finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)

theorem evalAt_eq (v : HeightOneSpectrum (𝓞 K)) (x : AdeleRing (𝓞 K) K) : x.2 v = evalAt K v x := rfl

theorem mul_comm_of_glArch_eq_one_of_glFin_eq_one {a b : AdelicGL2 (𝓞 K) K} (ha : glArch (𝓞 K) K a = 1)
    (hb : glFin (𝓞 K) K b = 1) : a * b = b * a :=
  gl_ext K (by rw [map_mul, map_mul, ha, one_mul, mul_one])
    (fun u => by rw [map_mul, map_mul, map_mul, map_mul, hb, map_one, mul_one, one_mul])

theorem glFin_diagOne_of_snd_eq_one (ε : (AdeleRing (𝓞 K) K)ˣ) (hε : ((ε : AdeleRing (𝓞 K) K)).2 = 1) :
    glFin (𝓞 K) K (diagOne ε) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glFin_apply, diagOne_coe_apply, Units.val_one]
  fin_cases i <;> fin_cases j <;> (try simp [Matrix.diagonal, Matrix.one_apply, hε]) <;> rfl

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul]
  change (Matrix.scalar (Fin 2) ((z : AdeleRing (𝓞 K) K))).det = _
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]

end RS27

namespace RS37

section Local

variable {L Γ₀ : Type*} [Field L] [LinearOrderedCommGroupWithZero Γ₀] (val : Valuation L Γ₀)

theorem val_conj_sub_one_apply_le (A Ai Q : Matrix (Fin 2) (Fin 2) L) (hAi : Ai * A = 1) (x y : Γ₀)
    (hA : ∀ i j, val (A i j) ≤ x) (hAi' : ∀ i j, val (Ai i j) ≤ x) (hQ : ∀ i j, val ((Q - 1) i j) ≤ y) :
    ∀ i j, val ((Ai * Q * A - 1) i j) ≤ x * y * x := by
  intro i j
  have h1 : Ai * Q * A - 1 = Ai * (Q - 1) * A := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAi]
  have hterm : ∀ l m, val (Ai i l * (Q - 1) l m * A m j) ≤ x * y * x := fun l m => by
    rw [map_mul, map_mul]
    exact mul_le_mul' (mul_le_mul' (hAi' i l) (hQ l m)) (hA m j)
  rw [h1, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, add_mul, add_mul]
  exact (val.map_add _ _).trans (max_le ((val.map_add _ _).trans (max_le (hterm 0 0) (hterm 1 0)))
    ((val.map_add _ _).trans (max_le (hterm 0 1) (hterm 1 1))))

theorem val_inv_sub_one_apply_le (Q Qi : Matrix (Fin 2) (Fin 2) L) (hQi : Qi * Q = 1) (y : Γ₀)
    (hQi' : ∀ i j, val (Qi i j) ≤ 1) (hQ : ∀ i j, val ((Q - 1) i j) ≤ y) :
    ∀ i j, val ((Qi - 1) i j) ≤ y := by
  intro i j
  have h1 : Qi - 1 = -(Qi * (Q - 1)) := by rw [Matrix.mul_sub, Matrix.mul_one, hQi, neg_sub]
  have hterm : ∀ l, val (Qi i l * (Q - 1) l j) ≤ y := fun l => by
    rw [map_mul]
    calc val (Qi i l) * val ((Q - 1) l j) ≤ 1 * y := mul_le_mul' (hQi' i l) (hQ l j)
      _ = y := one_mul y
  rw [h1, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply, Fin.sum_univ_two]
  exact (val.map_add _ _).trans (max_le (hterm 0) (hterm 1))

theorem val_apply_le_one_of_sub_one (Q : Matrix (Fin 2) (Fin 2) L) (y : Γ₀) (hy : y ≤ 1)
    (hQ : ∀ i j, val ((Q - 1) i j) ≤ y) : ∀ i j, val (Q i j) ≤ 1 := by
  intro i j
  have h1 : Q i j = (Q - 1) i j + (1 : Matrix (Fin 2) (Fin 2) L) i j := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [h1]
  refine (val.map_add _ _).trans (max_le ((hQ i j).trans hy) ?_)
  rw [Matrix.one_apply]
  split_ifs
  · exact le_of_eq val.map_one
  · exact le_of_eq_of_le val.map_zero zero_le'

end Local

variable (K : Type) [Field K] [NumberField K]

theorem conj_cong (S : Finset (HeightOneSpectrum (𝓞 K))) (a : AdelicGL2 (𝓞 K) K) (c : ℕ)
    (ha : ∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v ((((a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (c : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
      Valued.v (((((a⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (c : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (n₀ : ℕ) (k : AdelicGL2 (𝓞 K) K) (hka : k ∈ finiteAdelicGL2Subgroup K)
    (hki : glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K)
    (hks : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1)
    (hkc : ∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (-((n₀ + 2 * c : ℕ) : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    a⁻¹ * k * a ∈ finiteAdelicGL2Subgroup K ∧
    glFin (𝓞 K) K (a⁻¹ * k * a) ∈ finiteIntegralGL2 (𝓞 K) K ∧
    (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K (a⁻¹ * k * a)) = 1) ∧
    (∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v (((((a⁻¹ * k * a : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd (-(n₀ : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) := by

  set F : (v : HeightOneSpectrum (𝓞 K)) → AdelicGL2 (𝓞 K) K →* GL (Fin 2) (v.adicCompletion K) :=
    fun v => (finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K) with hFdef
  have hF : ∀ (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2),
      ((F v g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
        (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v := fun _ _ _ _ => rfl
  have hF1 : ∀ (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2),
      (((F v g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j =
        (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v := by
    intro v g i j
    rw [Matrix.sub_apply, hF, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  have hconj : ∀ v : HeightOneSpectrum (𝓞 K), F v (a⁻¹ * k * a) = (F v a)⁻¹ * F v k * F v a := fun v => by
    rw [map_mul, map_mul, map_inv]

  set x : WithZero (Multiplicative ℤ) := ((Multiplicative.ofAdd (c : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    with hx
  set y : WithZero (Multiplicative ℤ) :=
    ((Multiplicative.ofAdd (-((n₀ + 2 * c : ℕ) : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) with hy
  set z : WithZero (Multiplicative ℤ) := ((Multiplicative.ofAdd (-(n₀ : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    with hz
  have hxyx : x * y * x = z := by
    rw [hx, hy, hz, ← WithZero.coe_mul, ← WithZero.coe_mul, ← ofAdd_add, ← ofAdd_add]
    congr 2
    push_cast
    ring
  have hz1 : z ≤ 1 := by
    rw [hz, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    omega
  have hy1 : y ≤ 1 := by
    rw [hy, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    omega

  have hS : ∀ v ∈ S, (∀ i j : Fin 2, Valued.v
        ((((F v (a⁻¹ * k * a) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1)
          i j) ≤ z) ∧
      (∀ i j : Fin 2, Valued.v
        (((((F v (a⁻¹ * k * a))⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1)
          i j) ≤ z) := by
    intro v hv
    obtain ⟨hint, hint'⟩ := (mem_finiteIntegralGL2_iff).mp hki
    have hA : ∀ i j : Fin 2, Valued.v (((F v a : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ x :=
      fun i j => by rw [hF]; exact (ha v hv i j).1
    have hAi : ∀ i j : Fin 2, Valued.v ((((F v a)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ x :=
      fun i j => by rw [← map_inv, hF]; exact (ha v hv i j).2
    have hQ : ∀ i j : Fin 2, Valued.v ((((F v k : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) ≤ y :=
      fun i j => by rw [hF1]; exact hkc v hv i j
    have hQi1 : ∀ i j : Fin 2, Valued.v ((((F v k)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1 :=
      fun i j => by
        rw [← map_inv, hF]
        exact valued_apply_le_one (hint' i j) v
    have hQi : ∀ i j : Fin 2, Valued.v (((((F v k)⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) ≤ y :=
      val_inv_sub_one_apply_le Valued.v _ _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) y hQi1 hQ
    constructor
    · intro i j
      rw [hconj, Units.val_mul, Units.val_mul, ← hxyx]
      exact val_conj_sub_one_apply_le Valued.v _ _ _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
        x y hA hAi hQ i j
    · intro i j
      rw [hconj, mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul, ← hxyx]
      exact val_conj_sub_one_apply_le Valued.v _ _ _ (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
        x y hA hAi hQi i j

  have hoff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → F v (a⁻¹ * k * a) = 1 := fun v hv => by
    rw [hconj]
    have hk1 : F v k = 1 := hks v hv
    rw [hk1, mul_one, inv_mul_cancel]
  refine ⟨?_, ?_, hoff, fun v hv i j => ?_⟩
  · rw [mem_finiteAdelicGL2Subgroup_iff] at hka ⊢
    rw [map_mul, map_mul, map_inv, hka, mul_one, inv_mul_cancel]
  · rw [mem_finiteIntegralGL2_iff]
    constructor
    · intro i j v
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v (((F v (a⁻¹ * k * a) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1
      by_cases hv : v ∈ S
      · exact val_apply_le_one_of_sub_one Valued.v _ z hz1 (hS v hv).1 i j
      · rw [hoff v hv, Units.val_one, Matrix.one_apply]
        split_ifs
        · exact le_of_eq (map_one _)
        · exact le_of_eq_of_le (map_zero _) zero_le'
    · intro i j v
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v ((((F v (a⁻¹ * k * a))⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ 1
      by_cases hv : v ∈ S
      · exact val_apply_le_one_of_sub_one Valued.v _ z hz1 (hS v hv).2 i j
      · rw [hoff v hv, inv_one, Units.val_one, Matrix.one_apply]
        split_ifs
        · exact le_of_eq (map_one _)
        · exact le_of_eq_of_le (map_zero _) zero_le'
  · rw [← hF1]
    exact (hS v hv).1 i j

end RS37

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain AdelicDock AutomorphicForm.WindowedSiegel

namespace RS27T2

variable (F : Type) [Field F] [NumberField F]

private noncomputable def _root_.RS27T2.evalAt (v : HeightOneSpectrum (𝓞 F)) : AdeleRing (𝓞 F) F →+* v.adicCompletion F :=
  (finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)

p2m_export "RS27T2" "evalAt"
theorem evalAt_eq (v : HeightOneSpectrum (𝓞 F)) (x : AdeleRing (𝓞 F) F) : x.2 v = evalAt F v x := rfl

noncomputable def finAdeleOf (x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hx : ∀ v, x v ∈ v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨x, Filter.Eventually.of_forall hx⟩

theorem finAdeleOf_apply (x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (hx : ∀ v, x v ∈ v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    finAdeleOf F x hx v = x v := rfl

theorem diagOne_coe_eq (t : (AdeleRing (𝓞 F) F)ˣ) :
    ((diagOne t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![(t : AdeleRing (𝓞 F) F), 0; 0, 1] := by
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem diagOne_mul_unipotentGL2 (t : (AdeleRing (𝓞 F) F)ˣ) (x : AdeleRing (𝓞 F) F) :
    diagOne t * unipotentGL2 x = unipotentGL2 ((t : AdeleRing (𝓞 F) F) * x) * diagOne t := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, unipotentGL2_coe, unipotentGL2_coe, diagOne_coe_eq, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  simp only [mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add]

theorem centralScalar_coe_eq (z : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      !![(z : AdeleRing (𝓞 F) F), 0; 0, (z : AdeleRing (𝓞 F) F)] := by
  change Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) = _
  exact (Matrix.eta_fin_two _).trans (by simp [Matrix.scalar_apply, Matrix.diagonal])

theorem diagOne_mul_centralScalar (t z : (AdeleRing (𝓞 F) F)ˣ) :
    diagOne t * centralScalar (𝓞 F) F z = centralScalar (𝓞 F) F z * diagOne t := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, centralScalar_coe_eq, diagOne_coe_eq, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add, mul_comm]

end RS27T2

set_option maxHeartbeats 6400000 in
open RS27T2 in
theorem RS27.torus_at_S'
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (n : ℕ)
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ maximalCompactAt F S)
    (hsupp : ∀ v ∈ S,
      Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 v) ≤
        Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v) *
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    ∃ (u D : (AdeleRing (𝓞 F) F)ˣ) (β : AdeleRing (𝓞 F) F),
      ((u : AdeleRing (𝓞 F) F)).1 = 1 ∧ (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ((u : AdeleRing (𝓞 F) F)).2 w = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (((u : AdeleRing (𝓞 F) F)).2 v) = 1) ∧
      ((D : AdeleRing (𝓞 F) F)).1 = 1 ∧ (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → ((D : AdeleRing (𝓞 F) F)).2 w = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), Valued.v (((D : AdeleRing (𝓞 F) F)).2 v) = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), ((D : AdeleRing (𝓞 F) F)).2 v = ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v) ∧
      ∀ (W : AdelicGL2 (𝓞 F) F → ℂ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ),
        (∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), W (unipotentGL2 u * g) = ψ u * W g) →
        (∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F), W (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * W g) →
        (∀ (γ : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), γ.1 = 0 →
          (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → γ.2 w = 0) →
          (∀ v ∈ S, Valued.v (γ.2 v) ≤ ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          W (g * lowerUnipotentGL2 γ) = W g) →
        ∀ t : (AdeleRing (𝓞 F) F)ˣ,
          W (diagOne t * k) = ψ ((t : AdeleRing (𝓞 F) F) * β) * ((ω D : ℂˣ) : ℂ) *
            W (diagOne (t * u) * (k * (finEmbed (𝓞 F) F (glFin (𝓞 F) F k))⁻¹)) := by
  classical
  have hkK : k ∈ adelicMaximalCompact F := maximalCompactAt_le F S hk
  have hkoff : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → finComponent (𝓞 F) F w (glFin (𝓞 F) F k) = 1 :=
    (mem_maximalCompactAt_iff.mp hk).2

  have hent : ∀ (g : AdelicGL2 (𝓞 F) F) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 F)),
      ((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j =
        (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2) v := by
    intro g i j v; rw [finComponent_apply, glFin_apply]
  have hent1 : ∀ (g : AdelicGL2 (𝓞 F) F) (i j : Fin 2),
      ((glArch (𝓞 F) F g : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j =
        (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1) := by
    intro g i j; rw [glArch_apply]
  have hint : ∀ (i j : Fin 2) (v : HeightOneSpectrum (𝓞 F)),
      Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2) v) ≤ 1 := by
    intro i j v; rw [← hent]; exact (valued_finComponent_apply_le_one hkK v i j).1
  have hc_off : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
      (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) w = 0 := by
    intro w hw; rw [← hent, hkoff w hw, Units.val_one, Matrix.one_apply_ne (by decide)]
  have hd_off : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S →
      (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) w = 1 := by
    intro w hw; rw [← hent, hkoff w hw, Units.val_one, Matrix.one_apply_eq]
  have hexp_le : ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]; omega

  have hd_S : ∀ v ∈ S, Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v) = 1 := by
    intro v hv
    apply le_antisymm (hint 1 1 v)
    have hdet := valued_det_finComponent_eq_one hkK v
    rw [Matrix.det_fin_two, hent, hent, hent, hent] at hdet
    have hcd : Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) v) ≤
        Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v) :=
      (hsupp v hv).trans (mul_le_of_le_one_right' hexp_le)
    rw [← hdet]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_) <;> rw [Valuation.map_mul]
    · exact mul_le_of_le_one_left' (hint 0 0 v)
    · exact (mul_le_of_le_one_left' (hint 0 1 v)).trans hcd
  have hd_all : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v) = 1 := by
    intro v; by_cases hv : v ∈ S
    · exact hd_S v hv
    · rw [hd_off v hv, map_one]
  have hd_ne : ∀ v : HeightOneSpectrum (𝓞 F), (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v ≠ 0 := by
    intro v h; have h1 := hd_all v; rw [h, map_zero] at h1; exact zero_ne_one h1

  set γloc : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F := fun v =>
    (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) v *
      ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v)⁻¹ with hγloc
  have hγint : ∀ v : HeightOneSpectrum (𝓞 F), γloc v ∈ v.adicCompletionIntegers F := by
    intro v
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, hγloc]
    dsimp only
    rw [map_mul, map_inv₀, hd_all, inv_one, mul_one]
    exact hint 1 0 v
  set γ : AdeleRing (𝓞 F) F := ((0 : InfiniteAdeleRing F), finAdeleOf F γloc hγint) with hγdef
  have hγ1 : γ.1 = 0 := rfl
  have hγ2 : ∀ v : HeightOneSpectrum (𝓞 F), γ.2 v = γloc v := fun v => rfl
  have hγoff : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → γ.2 w = 0 := by
    intro w hw; rw [hγ2, hγloc]; dsimp only; rw [hc_off w hw, zero_mul]
  have hγS : ∀ v ∈ S, Valued.v (γ.2 v) ≤
      ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro v hv
    rw [hγ2, hγloc]; dsimp only
    rw [map_mul, map_inv₀, hd_S v hv, inv_one, mul_one]
    have h := hsupp v hv
    rwa [hd_S v hv, one_mul] at h

  set kfin : AdelicGL2 (𝓞 F) F := finEmbed (𝓞 F) F (glFin (𝓞 F) F k) with hkfin
  have hkfin_arch : glArch (𝓞 F) F kfin = 1 := glArch_finEmbed _ _ _
  have hkfin_fin : glFin (𝓞 F) F kfin = glFin (𝓞 F) F k := glFin_finEmbed _ _ _
  set karch : AdelicGL2 (𝓞 F) F := k * kfin⁻¹ with hkarch
  have hkarch_fin : glFin (𝓞 F) F karch = 1 := by rw [hkarch, map_mul, map_inv, hkfin_fin, mul_inv_cancel]
  have hk_eq : k = karch * kfin := by rw [hkarch, inv_mul_cancel_right]
  set lam : AdelicGL2 (𝓞 F) F := lowerUnipotentGL2 γ with hlam
  have hlam_coe : ((lam : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![1, 0; γ, 1] := rfl
  have hlaminv_coe : (((lam⁻¹ : AdelicGL2 (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![1, 0; -γ, 1] := rfl

  have gl_ext : ∀ {g h : AdelicGL2 (𝓞 F) F}, glArch (𝓞 F) F g = glArch (𝓞 F) F h →
      (∀ u, finComponent (𝓞 F) F u (glFin (𝓞 F) F g) = finComponent (𝓞 F) F u (glFin (𝓞 F) F h)) → g = h := by
    intro g h h₁ h₂
    apply Units.ext; ext i j; apply Prod.ext
    · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
        (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) h₁) i) j
      rwa [glArch_apply, glArch_apply] at this
    · refine RestrictedProduct.ext _ _ fun u => ?_
      have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (u.adicCompletion F) =>
        (m : Matrix (Fin 2) (Fin 2) (u.adicCompletion F))) (h₂ u)) i) j
      rwa [finComponent_apply, finComponent_apply, glFin_apply, glFin_apply] at this

  have hlam_arch : glArch (𝓞 F) F lam = 1 := by
    apply Units.ext; ext i j
    rw [hent1, hlam_coe, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [hγ1] <;> rfl
  have hlam_off : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → finComponent (𝓞 F) F w (glFin (𝓞 F) F lam) = 1 := by
    intro w hw
    apply Units.ext; ext i j
    rw [hent, hlam_coe, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [hγoff w hw] <;> rfl
  have hlam_K : lam ∈ adelicMaximalCompact F := by
    refine ⟨mem_finiteIntegralGL2_iff.mpr ⟨fun i j w => ?_, fun i j w => ?_⟩, fun w' => ?_⟩
    · rw [glFin_apply, hlam_coe]
      fin_cases i <;> fin_cases j
      · show (1 : AdeleRing (𝓞 F) F).2 w ∈ _; exact one_mem _
      · show (0 : AdeleRing (𝓞 F) F).2 w ∈ _; exact zero_mem _
      · show γ.2 w ∈ _; exact hγint w
      · show (1 : AdeleRing (𝓞 F) F).2 w ∈ _; exact one_mem _
    · rw [← map_inv, glFin_apply, hlaminv_coe]
      fin_cases i <;> fin_cases j
      · show (1 : AdeleRing (𝓞 F) F).2 w ∈ _; exact one_mem _
      · show (0 : AdeleRing (𝓞 F) F).2 w ∈ _; exact zero_mem _
      · show (-γ).2 w ∈ _; exact neg_mem (hγint w)
      · show (1 : AdeleRing (𝓞 F) F).2 w ∈ _; exact one_mem _
    · rw [hlam_arch, map_one]; exact isRowIsometry_one
  set βm : AdelicGL2 (𝓞 F) F := kfin * lam⁻¹ with hβm
  have hkfin_K : kfin ∈ adelicMaximalCompact F :=
    ⟨by rw [hkfin_fin]; exact hkK.1, fun w => by rw [hkfin_arch, map_one]; exact isRowIsometry_one⟩
  have hβm_K : βm ∈ adelicMaximalCompact F := mul_mem hkfin_K (inv_mem hlam_K)
  have hβm_arch : glArch (𝓞 F) F βm = 1 := by rw [hβm, map_mul, map_inv, hkfin_arch, hlam_arch, inv_one, mul_one]
  have hβm_off : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → finComponent (𝓞 F) F w (glFin (𝓞 F) F βm) = 1 := by
    intro w hw; rw [hβm, map_mul, map_inv, map_mul, map_inv, hkfin_fin, hkoff w hw, hlam_off w hw, inv_one, mul_one]
  have h1arch : ∀ i : Fin 2, ((((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i i)).1 = 1 := by
    intro i; rw [← hent1, hβm_arch, Units.val_one, Matrix.one_apply_eq]
  have h1off : ∀ (i : Fin 2) (w : HeightOneSpectrum (𝓞 F)), w ∉ S →
      ((((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i i)).2 w = 1 := by
    intro i w hw; rw [← hent, hβm_off w hw, Units.val_one, Matrix.one_apply_eq]

  have hβ10 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := by
    apply Prod.ext
    · rw [← hent1, hβm_arch, Units.val_one, Matrix.one_apply_ne (by decide)]; rfl
    · refine RestrictedProduct.ext _ _ fun v => ?_
      have h1 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 =
          ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 * 1 +
          ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 * (-γ) := by
        rw [hβm, Units.val_mul, hlaminv_coe, Matrix.mul_apply, Fin.sum_univ_two]
        simp
      have hk10 : evalAt F v ((((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0)) =
          (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) v := by rw [← evalAt_eq, ← hent, ← hent, hkfin_fin]
      have hk11 : evalAt F v ((((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1)) =
          (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v := by rw [← evalAt_eq, ← hent, ← hent, hkfin_fin]
      have hγv : evalAt F v γ = γloc v := rfl
      show evalAt F v ((((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0)) = evalAt F v 0
      rw [h1, map_add, map_mul, map_mul, map_one, map_neg, map_zero, hk10, hk11, hγv, hγloc]
      dsimp only
      rw [mul_one, mul_neg, ← mul_assoc, mul_comm ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v),
        mul_assoc, mul_inv_cancel₀ (hd_ne v), mul_one, add_neg_cancel]
  have hβ : βm ∈ adelicBorel (𝓞 F) F := hβ10
  have hkf00 : ∀ v : HeightOneSpectrum (𝓞 F), evalAt F v (((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0) = (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2) v := by
    intro v; rw [← evalAt_eq, ← hent, ← hent, hkfin_fin]
  have hkf01 : ∀ v : HeightOneSpectrum (𝓞 F), evalAt F v (((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1) = (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1).2) v := by
    intro v; rw [← evalAt_eq, ← hent, ← hent, hkfin_fin]
  have hkf10 : ∀ v : HeightOneSpectrum (𝓞 F), evalAt F v (((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) = (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2) v := by
    intro v; rw [← evalAt_eq, ← hent, ← hent, hkfin_fin]
  have hkf11 : ∀ v : HeightOneSpectrum (𝓞 F), evalAt F v (((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1) = (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2) v := by
    intro v; rw [← evalAt_eq, ← hent, ← hent, hkfin_fin]

  set Bel : ↥(adelicBorel (𝓞 F) F) := ⟨βm, hβ⟩ with hBel
  set t₁ : (AdeleRing (𝓞 F) F)ˣ := borelDiagFst Bel with ht₁
  set t₂ : (AdeleRing (𝓞 F) F)ˣ := borelDiagSnd Bel with ht₂
  set βad : AdeleRing (𝓞 F) F :=
    ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 *
      ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) with hβad
  have h00 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = (t₁ : AdeleRing (𝓞 F) F) := rfl
  have h11 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = (t₂ : AdeleRing (𝓞 F) F) := rfl
  have ht2inv : ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (t₂ : AdeleRing (𝓞 F) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcs := RS27T2.centralScalar_coe_eq F t₂
  have hdo : ((diagOne (t₁ * t₂⁻¹) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(t₁ : AdeleRing (𝓞 F) F) * ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0; 0, 1] := by
    rw [RS27T2.diagOne_coe_eq, Units.val_mul]
  have hx00 : (t₂ : AdeleRing (𝓞 F) F) * ((t₁ : AdeleRing (𝓞 F) F) * ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
      = (t₁ : AdeleRing (𝓞 F) F) := by
    rw [mul_left_comm, Units.mul_inv, mul_one]
  have hβ01 : βad * (t₂ : AdeleRing (𝓞 F) F)
      = ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 := by
    rw [hβad, mul_assoc, ht2inv, mul_one]
  have hR : ((unipotentGL2 βad : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((centralScalar (𝓞 F) F t₂ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((diagOne (t₁ * t₂⁻¹) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(t₁ : AdeleRing (𝓞 F) F), βad * (t₂ : AdeleRing (𝓞 F) F); 0, (t₂ : AdeleRing (𝓞 F) F)] := by
    rw [hcs, hdo, unipotentGL2_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
    simp only [mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add, hx00]
  have hdecomp : βm = unipotentGL2 βad * centralScalar (𝓞 F) F t₂ * diagOne (t₁ * t₂⁻¹) := by
    apply Units.ext
    change ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = ((unipotentGL2 βad : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((centralScalar (𝓞 F) F t₂ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((diagOne (t₁ * t₂⁻¹) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    rw [hR, hβ01]
    conv_lhs => rw [Matrix.eta_fin_two ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))]
    rw [h00, h11, hβ10]

  have hcomm_fa : ∀ {a b : AdelicGL2 (𝓞 F) F}, glArch (𝓞 F) F a = 1 → glFin (𝓞 F) F b = 1 → a * b = b * a := by
    intro a b ha hb
    exact gl_ext (by rw [map_mul, map_mul, ha, one_mul, mul_one])
      (fun u => by rw [map_mul, map_mul, map_mul, map_mul, hb, map_one, mul_one, one_mul])
  have hdn := RS27T2.diagOne_mul_unipotentGL2 F
  have hdz := RS27T2.diagOne_mul_centralScalar F

  have hkβ : k = karch * βm * lam := by
    rw [hβm, hkarch]; simp only [mul_assoc, inv_mul_cancel, inv_mul_cancel_left, mul_one]
  have hmain : ∀ (W : AdelicGL2 (𝓞 F) F → ℂ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ),
      (∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), W (unipotentGL2 u * g) = ψ u * W g) →
      (∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F), W (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * W g) →
      (∀ (γ : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), γ.1 = 0 →
        (∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → γ.2 w = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤ ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        W (g * lowerUnipotentGL2 γ) = W g) →
      ∀ t : (AdeleRing (𝓞 F) F)ˣ,
      W (diagOne t * k) = ψ ((t : (AdeleRing (𝓞 F) F)) * βad) * ((ω t₂ : ℂˣ) : ℂ) *
        W (diagOne (t * (t₁ * t₂⁻¹)) * karch) := by
    intro W ψ ω hN hZ hinv t
    have e1 : diagOne t * k = (diagOne t * βm * karch) * lam := by
      rw [hkβ, ← hcomm_fa hβm_arch hkarch_fin]; simp only [mul_assoc]
    have e2 : diagOne t * (unipotentGL2 βad * centralScalar (𝓞 F) F t₂ * diagOne (t₁ * t₂⁻¹)) * karch =
        unipotentGL2 ((t : (AdeleRing (𝓞 F) F)) * βad) * (centralScalar (𝓞 F) F t₂ * (diagOne (t * (t₁ * t₂⁻¹)) * karch)) := by
      calc diagOne t * (unipotentGL2 βad * centralScalar (𝓞 F) F t₂ * diagOne (t₁ * t₂⁻¹)) * karch
          = (diagOne t * unipotentGL2 βad) * centralScalar (𝓞 F) F t₂ * diagOne (t₁ * t₂⁻¹) * karch := by
            simp only [mul_assoc]
        _ = (unipotentGL2 ((t : (AdeleRing (𝓞 F) F)) * βad) * diagOne t) * centralScalar (𝓞 F) F t₂ * diagOne (t₁ * t₂⁻¹) * karch := by
            rw [hdn]
        _ = unipotentGL2 ((t : (AdeleRing (𝓞 F) F)) * βad) * (diagOne t * centralScalar (𝓞 F) F t₂) * diagOne (t₁ * t₂⁻¹) * karch := by
            simp only [mul_assoc]
        _ = unipotentGL2 ((t : (AdeleRing (𝓞 F) F)) * βad) * (centralScalar (𝓞 F) F t₂ * diagOne t) * diagOne (t₁ * t₂⁻¹) * karch := by
            rw [hdz]
        _ = unipotentGL2 ((t : (AdeleRing (𝓞 F) F)) * βad) * (centralScalar (𝓞 F) F t₂ * ((diagOne t * diagOne (t₁ * t₂⁻¹)) * karch)) := by
            simp only [mul_assoc]
        _ = unipotentGL2 ((t : (AdeleRing (𝓞 F) F)) * βad) * (centralScalar (𝓞 F) F t₂ * (diagOne (t * (t₁ * t₂⁻¹)) * karch)) := by
            rw [← map_mul]
    rw [e1, hinv γ (diagOne t * βm * karch) hγ1 hγoff hγS, hdecomp, e2, hN, hZ]
    ring

  have hval : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (((t₁ : (AdeleRing (𝓞 F) F))).2 v) = 1 ∧ Valued.v (((t₂ : (AdeleRing (𝓞 F) F))).2 v) = 1 := by
    intro v
    have hγv : evalAt F v γ = γloc v := rfl

    have e00 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 * 1 + ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 * (-γ) := by
      rw [hβm, Units.val_mul, hlaminv_coe, Matrix.mul_apply, Fin.sum_univ_two]; simp
    have e11 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 * 0 + ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 * 1 := by
      rw [hβm, Units.val_mul, hlaminv_coe, Matrix.mul_apply, Fin.sum_univ_two]; simp
    have ht2 : ((t₂ : (AdeleRing (𝓞 F) F))).2 v = ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v := by
      show evalAt F v (((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1) = _
      rw [e11, map_add, map_mul, map_mul, map_zero, map_one, hkf10 v, hkf11 v, mul_zero, zero_add, mul_one]
    have hdet := valued_det_finComponent_eq_one hkK v
    rw [Matrix.det_fin_two, hent, hent, hent, hent] at hdet
    have ht1 : ((t₁ : (AdeleRing (𝓞 F) F))).2 v =
        (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2 v * ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v - ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1).2 v * ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 v) * (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v)⁻¹ := by
      show evalAt F v (((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0) = _
      rw [e00, map_add, map_mul, map_mul, map_one, map_neg, hkf00 v, hkf01 v, hγv, hγloc]
      dsimp only
      field_simp [hd_ne v]
      ring
    refine ⟨?_, ?_⟩
    · rw [ht1, map_mul, map_inv₀, hdet, hd_all v, inv_one, mul_one]
    · rw [ht2, hd_all v]

  have hinv_fst : ((((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F))).1 = 1 := by
    have h := congrArg Prod.fst (Units.inv_mul t₂)
    change ((((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F))).1 * ((t₂ : (AdeleRing (𝓞 F) F))).1 = (1 : (AdeleRing (𝓞 F) F)).1 at h
    rw [show ((t₂ : (AdeleRing (𝓞 F) F))).1 = 1 from h1arch 1, mul_one] at h
    exact h
  have hinv_snd : ∀ w : HeightOneSpectrum (𝓞 F),
      ((((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F))).2 w * ((t₂ : (AdeleRing (𝓞 F) F))).2 w = 1 := by
    intro w
    have h := congrArg (fun x : (AdeleRing (𝓞 F) F) => x.2 w) (Units.inv_mul t₂)
    exact h
  have ht2all : ∀ v : HeightOneSpectrum (𝓞 F), ((t₂ : (AdeleRing (𝓞 F) F))).2 v =
      ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v := by
    intro v
    have e11 : ((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 * 0 + ((kfin : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 * 1 := by
      rw [hβm, Units.val_mul, hlaminv_coe, Matrix.mul_apply, Fin.sum_univ_two]; simp
    show evalAt F v (((βm : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1) = _
    rw [e11, map_add, map_mul, map_mul, map_zero, map_one, hkf10 v, hkf11 v, mul_zero, zero_add, mul_one]
  refine ⟨t₁ * t₂⁻¹, t₂, βad, ?_, ?_, ?_, h1arch 1, fun w hw => h1off 1 w hw, fun v => (hval v).2, ht2all, hmain⟩
  · show ((t₁ : (AdeleRing (𝓞 F) F))).1 * ((((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F))).1 = 1
    rw [show ((t₁ : (AdeleRing (𝓞 F) F))).1 = 1 from h1arch 0, hinv_fst, mul_one]
  · intro w hw
    show ((t₁ : (AdeleRing (𝓞 F) F))).2 w * ((((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F))).2 w = 1
    have h := hinv_snd w
    rw [show ((t₂ : (AdeleRing (𝓞 F) F))).2 w = 1 from h1off 1 w hw, mul_one] at h
    rw [show ((t₁ : (AdeleRing (𝓞 F) F))).2 w = 1 from h1off 0 w hw, h, mul_one]
  · intro v
    show Valued.v (((t₁ : (AdeleRing (𝓞 F) F))).2 v * ((((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F))).2 v) = 1
    have h := congrArg Valued.v (hinv_snd v)
    rw [map_mul, (hval v).2, mul_one, map_one] at h
    rw [map_mul, (hval v).1, h, mul_one]

set_option maxHeartbeats 6400000 in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (D₀ : Set (AdelicGL2 (𝓞 K) K))

      (ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hων : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))

      (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
      (nb : ℕ) (_hnb : 0 < nb)
      (_hx₀cong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x₀ (g * k) = x₀ g)

      (t₀ : (AdeleRing (𝓞 K) K)ˣ) (_ht₀inf : ((t₀ : AdeleRing (𝓞 K) K)).1 = 1)
      (_ht₀ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1)
      (m : ℕ)
      (_ht₀box : ∀ v ∈ S, Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
        ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
      (k₀ : AdelicGL2 (𝓞 K) K) (_hk₀ : k₀ ∈ maximalCompactAt K S)
      (κ : AdelicGL2 (𝓞 K) K) (_hκ : κ = AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀))

      (r : ℕ) (u : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ)
      (_husupp : ∀ i, (u i).1 = 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (u i).2 v = 0)
      (_hWmult : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (u i) = unipotentGL2 (u i) * g') →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (u i) * κ)) 1
          (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * u i)) *
            whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => x₀ (g * κ)) 1
          (diagOne t * g'))
      (_hμball : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * u i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) *
                ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0)
      (_hboxvan : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ t : (AdeleRing (𝓞 K) K)ˣ,
          (∃ v ∈ S, ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) <
            Valued.v (((t : AdeleRing (𝓞 K) K)).2 v)) →
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * k * κ) = 0)

      (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * (unipotentGL2 (u i) * κ)))
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
      (_hxKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, x (g * k) = x g)
      (n : ℕ) (_hn : 0 < n)
      (_hxlow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        x (g * lowerUnipotentGL2 γ) = x g)

      (y : AdelicGL2 (𝓞 K) K → ℂ)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g)
      (_hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
      (_hyKS : ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, y (g * k) = y g)
      (_hycong : ∀ (g k : AdelicGL2 (𝓞 K) K), k ∈ finiteAdelicGL2Subgroup K →
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K k) = 1) →
        (∀ v ∈ S, ∀ i j : Fin 2,
          Valued.v ((((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
              (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
            ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        y (g * k) = y g)
      (_hylow : ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
        (∀ v ∈ S, Valued.v (γ.2 v) ≤
          ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        y (g * lowerUnipotentGL2 γ) = y g)

      (finf : AdelicGL2 (𝓞 K) K → ℂ)
      (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 K) K (etaFst 1 α hα s) (etaSnd ν α hα s) (φ s))
      (_hφKS : ∀ s, ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ s (g * k) = φ s g)
      (_hφsupp : ∀ (s : ℂ) (k : AdelicGL2 (𝓞 K) K),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        (∃ v ∈ S, ¬ Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = 0)
      (_hφval : ∀ (s : ℂ) (k kinf : AdelicGL2 (𝓞 K) K) (d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ),
        glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        glFin (𝓞 K) K kinf = 1 → glArch (𝓞 K) K kinf = glArch (𝓞 K) K k →
        (∀ v ∈ S, (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) = (d v : v.adicCompletion K)) →
        (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
            Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) *
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
          φ s k = (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) * finf kinf)
      (s : ℂ) (k : AdelicGL2 (𝓞 K) K) (_hk : k ∈ adelicMaximalCompact K),
    ∃ ρ : (AdeleRing (𝓞 K) K)ˣ, ((ρ : AdeleRing (𝓞 K) K)).1 = 1 ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((ρ : AdeleRing (𝓞 K) K)).2 v = 1) ∧
      (∀ v ∈ S, Valued.v (((ρ : AdeleRing (𝓞 K) K)).2 v) = 1) ∧
      ∀ t : (AdeleRing (𝓞 K) K)ˣ, (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((t : AdeleRing (𝓞 K) K)).2 v = 1) →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t * k) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne t * k)) *
            φ s (diagOne t * k) =
          (if (∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
              Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then
            ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) *
              finf (adelicArchGLIncl K (glArch (𝓞 K) K k)) *
              (if (∀ v ∈ S, Valued.v ((((t * ρ) : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) then
                whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * adelicArchGLIncl K (glArch (𝓞 K) K k) * (diagOne t₀ * κ)) *
                  (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
          (diagOne (NumberField.Idele.partAt K ∅ t) * adelicArchGLIncl K (glArch (𝓞 K) K k) * diagOne t₀))
               else 0)
           else 0) := by

  intro α hα S D₀ ωx ωy w ν hων x₀ nb hnb hx₀cong t₀ ht₀inf ht₀ m ht₀box k₀ hk₀ κ hκ r u cs husupp hWmult hμball hboxvan
    x hxsum hxG hxZ hxKS n hn hxlow y hyG hyZ hyKS hycong hylow finf φ hφ hφKS hφsupp hφval s k hk

  set pins := productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (adelicBox K) with hpins
  set ψ : AddChar (AdeleRing (𝓞 K) K) ℂ := NumberField.StandardAddChar.stdAddChar K with hψdef
  have hψG : IsGlobalAddChar K ψ := NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K
  set e : WithZero (Multiplicative ℤ) := ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    with he
  set eb : WithZero (Multiplicative ℤ) := ((Multiplicative.ofAdd (-(nb : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    with heb

  have hent : ∀ (g : AdelicGL2 (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2),
      ((finComponent (𝓞 K) K v (glFin (𝓞 K) K g) : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j = (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v :=
    fun _ _ _ _ => rfl

  obtain ⟨k₁, k₂, hk₁, hk₂, hk12⟩ := AutomorphicForm.exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq K S k hk
  obtain ⟨hk₂K, hk₂arch, hk₂S⟩ := mem_maximalCompactAway_iff.mp hk₂
  have hk₁K : k₁ ∈ adelicMaximalCompact K := (mem_maximalCompactAt_iff.mp hk₁).1
  have hentS : ∀ v ∈ S, ∀ i j : Fin 2, (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v =
      (((k₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v := by
    intro v hv i j
    rw [← hent, ← hent, hk12, map_mul, map_mul, hk₂S v hv, mul_one]
  have harchk : glArch (𝓞 K) K k = glArch (𝓞 K) K k₁ := by rw [hk12, map_mul, hk₂arch, mul_one]
  have hWk : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), (∀ k' ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, f (g * k') = f g) →
      ∀ t : (AdeleRing (𝓞 K) K)ˣ, whittakerCoefficient K pins ψ f 1 (diagOne t * k) = whittakerCoefficient K pins ψ f 1 (diagOne t * k₁) := by
    intro f hf t
    rw [hk12, ← mul_assoc]
    exact RS12W.whittakerCoefficient_mul_right_eq_of_forall K pins ψ f 1 _ k₂ (fun g => hf k₂ hk₂ g)
  have hφk : ∀ t : (AdeleRing (𝓞 K) K)ˣ, φ s (diagOne t * k) = φ s (diagOne t * k₁) := fun t => by
    rw [hk12, ← mul_assoc]; exact hφKS s k₂ hk₂ _

  have hsec : ∀ (g : AdelicGL2 (𝓞 K) K) (t : (AdeleRing (𝓞 K) K)ˣ),
      φ s (diagOne t * g) = ((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * φ s g := by
    intro g t
    have hB : (diagOne t : AdelicGL2 (𝓞 K) K) ∈ adelicBorel (𝓞 K) K := by
      show ((diagOne t : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0 = 0
      rw [diagOne_coe_apply]; simp
    have h := hφ s (diagOne t) hB g
    have h1 : borelDiagFst (⟨diagOne t, hB⟩ : ↥(adelicBorel (𝓞 K) K)) = t := by
      apply Units.ext; rw [borelDiagFst_apply_val]; show ((diagOne t : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 0 0 = _
      rw [diagOne_coe_apply]; simp
    have h2 : borelDiagSnd (⟨diagOne t, hB⟩ : ↥(adelicBorel (𝓞 K) K)) = 1 := by
      apply Units.ext; rw [borelDiagSnd_apply_val]; show ((diagOne t : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1 = _
      rw [diagOne_coe_apply]; simp
    rw [h, h1, h2, map_one, Units.val_one, mul_one, etaFst_apply, Units.val_mul, MonoidHom.one_apply, Units.val_one, one_mul,
      cpowChar_apply_val]
    rfl

  by_cases hsuppk : ∀ v ∈ S, Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
      Valued.v (((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * e
  swap
  ·
    refine ⟨1, by rw [Units.val_one]; rfl, fun v _ => by rw [Units.val_one]; rfl, fun v _ => by rw [Units.val_one]; exact map_one _, ?_⟩
    intro t _
    rw [if_neg hsuppk]
    have h0 : φ s k = 0 := by
      refine hφsupp s k hk.1 hk.2 ?_
      push_neg at hsuppk
      obtain ⟨v, hv, hlt⟩ := hsuppk
      exact ⟨v, hv, not_le.mpr hlt⟩
    rw [hsec k t, h0, mul_zero, mul_zero]

  have hsupp₁ : ∀ v ∈ S, Valued.v (((k₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v) ≤
      Valued.v (((k₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v) * e := by
    intro v hv; rw [← hentS v hv, ← hentS v hv]; exact hsuppk v hv
  obtain ⟨uu, D, β, hu1, huS, huv, hD1, hDS, hDv, hDk, hmain⟩ := RS27.torus_at_S' K S n k₁ hk₁ hsupp₁
  refine ⟨uu, hu1, huS, fun v _ => huv v, ?_⟩
  intro t htS
  rw [if_pos hsuppk]

  set karch : AdelicGL2 (𝓞 K) K := k₁ * (AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₁))⁻¹ with hkarchdef
  have hkarch_fin : glFin (𝓞 K) K karch = 1 := by
    rw [hkarchdef, map_mul, map_inv, AdelicDock.glFin_finEmbed, mul_inv_cancel]
  have hkarch_arch : glArch (𝓞 K) K karch = glArch (𝓞 K) K k₁ := by
    rw [hkarchdef, map_mul, map_inv, AdelicDock.glArch_finEmbed, inv_one, mul_one]
  have hkarch_iso : ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K karch)) := fun pl => by
    rw [hkarch_arch]; exact hk₁K.2 pl
  have hkarch_eq : adelicArchGLIncl K (glArch (𝓞 K) K k) = karch := by
    refine RS27.gl_ext K ?_ fun v => ?_
    · rw [glArch_adelicArchGLIncl, harchk, hkarch_arch]
    · rw [glFin_adelicArchGLIncl, hkarch_fin]
  rw [hkarch_eq]

  have hper : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      f (globalPoints (𝓞 K) K γ * g) = f g) → ∀ (g : AdelicGL2 (𝓞 K) K) (b : K) (uu' : AdeleRing (𝓞 K) K),
      f (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) b + uu') * g) = f (unipotentGL2 uu' * g) := by
    intro f hfG g b uu'
    rw [unipotentGL2_add, mul_assoc, RS37P4.unipotentGL2_algebraMap_eq_globalPoints, hfG]
  have hN : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
      f (globalPoints (𝓞 K) K γ * g) = f g) →
      ∀ (uu' : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), whittakerCoefficient K pins ψ f 1 (unipotentGL2 uu' * g) = ψ uu' * whittakerCoefficient K pins ψ f 1 g := by
    intro f hfG uu' g
    have h := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) ψ hψG.principalInvariant f g (hper f hfG g) 1 uu'
    rw [map_one, one_mul] at h
    exact h
  have hZ : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
      (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), f (centralScalar (𝓞 K) K z * g) = ((ω z : ℂˣ) : ℂ) * f g) →
      ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
        whittakerCoefficient K pins ψ f 1 (centralScalar (𝓞 K) K z * g) = ((ω z : ℂˣ) : ℂ) * whittakerCoefficient K pins ψ f 1 g := by
    intro f ω hf z g
    rw [← RS37P4.centralScalar_comm K z g]
    exact RS12W.whittakerCoefficient_mul_central K pins ψ f 1 g (centralScalar (𝓞 K) K z) _
      (fun h' => RS37P4.centralScalar_comm K z h') (hf z)
  have hL : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ), (∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) → (∀ v ∈ S, Valued.v (γ.2 v) ≤ e) → f (g * lowerUnipotentGL2 γ) = f g) →
      ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) → (∀ v ∈ S, Valued.v (γ.2 v) ≤ e) →
      whittakerCoefficient K pins ψ f 1 (g * lowerUnipotentGL2 γ) = whittakerCoefficient K pins ψ f 1 g := by
    intro f hf γ g h1 h2 h3
    exact RS12W.whittakerCoefficient_mul_right_eq_of_forall K pins ψ f 1 g _ (fun g' => hf γ g' h1 h2 h3)
  have hWx := hmain (fun g => whittakerCoefficient K pins ψ x 1 g) ψ ωx (hN x hxG) (hZ x ωx hxZ) (hL x hxlow) t
  have hWy := hmain (fun g => whittakerCoefficient K pins ψ y 1 g) ψ ωy (hN y hyG) (hZ y ωy hyZ) (hL y hylow) t

  have hDne : ∀ v : HeightOneSpectrum (𝓞 K), ((D : AdeleRing (𝓞 K) K)).2 v ≠ 0 := fun v h0 => by
    have h1 := hDv v; rw [h0, map_zero] at h1; exact zero_ne_one h1
  set d : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ := fun v => Units.mk0 (((D : AdeleRing (𝓞 K) K)).2 v) (hDne v)
    with hddef
  have hφ₁ : φ s k₁ = (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) * finf karch := by
    refine hφval s k₁ karch d hk₁K.1 hk₁K.2 hkarch_fin hkarch_arch (fun v hv => ?_) hsupp₁
    rw [← hDk v]; rfl

  have hDprod : (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) = ((ν D : ℂˣ) : ℂ) := by
    set ι : HeightOneSpectrum (𝓞 K) → (AdeleRing (𝓞 K) K)ˣ := fun v => Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (d v))
      with hιdef
    have hι1 : ∀ v, ((ι v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := fun v => rfl
    have hιself : ∀ v, ((ι v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = (d v : v.adicCompletion K) := fun v =>
      localUnit_apply_self (𝓞 K) K v (d v)
    have hιne : ∀ v w : HeightOneSpectrum (𝓞 K), w ≠ v → ((ι v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w = 1 :=
      fun v w hw => localUnit_apply_of_ne (𝓞 K) K v (d v) hw

    set E₁ : (AdeleRing (𝓞 K) K)ˣ →* InfiniteAdeleRing K := (MonoidHom.fst _ _).comp (Units.coeHom (AdeleRing (𝓞 K) K))
      with hE₁
    set E₂ : (w : HeightOneSpectrum (𝓞 K)) → (AdeleRing (𝓞 K) K)ˣ →* w.adicCompletion K := fun w =>
      (RS27.evalAt K w).toMonoidHom.comp (Units.coeHom (AdeleRing (𝓞 K) K)) with hE₂
    have hE₁a : ∀ z : (AdeleRing (𝓞 K) K)ˣ, E₁ z = ((z : AdeleRing (𝓞 K) K)).1 := fun _ => rfl
    have hE₂a : ∀ (w : HeightOneSpectrum (𝓞 K)) (z : (AdeleRing (𝓞 K) K)ˣ), E₂ w z = ((z : AdeleRing (𝓞 K) K)).2 w :=
      fun _ _ => rfl
    have hDeq : D = ∏ v ∈ S, ι v := by
      apply Units.ext
      apply Prod.ext
      · show E₁ D = E₁ (∏ v ∈ S, ι v)
        rw [map_prod, hE₁a, hD1]
        exact (Finset.prod_eq_one fun v _ => (hE₁a (ι v)).trans (hι1 v)).symm
      · refine RestrictedProduct.ext _ _ fun w' => ?_
        show ((D : AdeleRing (𝓞 K) K)).2 w' = (((∏ v ∈ S, ι v : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 w'
        rw [← hE₂a, ← hE₂a, map_prod]
        simp only [hE₂a]
        by_cases hw' : w' ∈ S
        · rw [Finset.prod_eq_single_of_mem w' hw' (fun v _ hv => hιne v w' (Ne.symm hv)), hιself]
          rfl
        · rw [hDS w' hw', Finset.prod_eq_one]
          intro v hv
          exact hιne v w' (fun h => hw' (h ▸ hv))
    rw [hDeq, map_prod, Units.coe_prod]
    exact Finset.prod_congr rfl fun v _ => rfl
  have hchar : ((ωx D : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy D : ℂˣ) : ℂ) * (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)) = 1 := by
    rw [hDprod, hων D]
    have hnorm : NumberField.TateGlobal.ideleNorm K D = 1 := by
      refine NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K D hD1 ⟨fun v => ?_, fun v => ?_⟩
      · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, NumberField.AdeleRing.val_finitePartUnits]
        exact (hDv v).le
      · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← map_inv, NumberField.AdeleRing.val_finitePartUnits]
        have h := congrArg (fun x : AdeleRing (𝓞 K) K => Valued.v (x.2 v)) (Units.inv_mul D)
        rw [show ((((D⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K) * (D : AdeleRing (𝓞 K) K)).2 v =
          (((D⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v * ((D : AdeleRing (𝓞 K) K)).2 v from rfl, map_mul, hDv v,
          mul_one, show (1 : AdeleRing (𝓞 K) K).2 v = 1 from rfl, map_one] at h
        exact h.le
    rw [hnorm, Real.one_rpow, Complex.ofReal_one]

  have hphase : ψ ((t : AdeleRing (𝓞 K) K) * β) * (starRingEnd ℂ) (ψ ((t : AdeleRing (𝓞 K) K) * β)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar K hψG]
    simp

  set p : (AdeleRing (𝓞 K) K)ˣ := NumberField.Idele.partAt K ∅ t with hpdef
  have hp1 : ((p : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = ((t : AdeleRing (𝓞 K) K)).1 :=
    NumberField.Idele.partAt_fst K ∅ t
  have hp2 : ∀ v : HeightOneSpectrum (𝓞 K), ((p : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 := fun v =>
    NumberField.Idele.partAt_snd_of_not_mem K ∅ t (Finset.notMem_empty v)

  set ε : (AdeleRing (𝓞 K) K)ˣ := t₀⁻¹ * (p⁻¹ * (t * uu)) with hεdef
  have hfst_mul : ∀ a b : AdeleRing (𝓞 K) K, (a * b).1 = a.1 * b.1 := fun _ _ => rfl
  have hsnd_mul : ∀ (a b : AdeleRing (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K)), (a * b).2 v = a.2 v * b.2 v := fun _ _ _ => rfl
  have hinv_fst : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K)).1 * ((z : AdeleRing (𝓞 K) K)).1 = 1 :=
    fun z => by rw [← hfst_mul, Units.inv_mul]; rfl
  have hinv_snd : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      ((((z⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K)).2 v * ((z : AdeleRing (𝓞 K) K)).2 v = 1 :=
    fun z v => by rw [← hsnd_mul, Units.inv_mul]; rfl
  have hq1 : ((((p⁻¹ * (t * uu) : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K)).1 = 1 := by
    rw [Units.val_mul, Units.val_mul, hfst_mul, hfst_mul, hu1, mul_one, ← hp1, hinv_fst]
  have hε1 : ((ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
    rw [hεdef, Units.val_mul, hfst_mul, hq1, mul_one]
    have h := hinv_fst t₀
    rwa [ht₀inf, mul_one] at h
  have hε2 : ∀ v : HeightOneSpectrum (𝓞 K), ((ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v =
      ((((t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K)).2 v * (((t : AdeleRing (𝓞 K) K)).2 v * ((uu : AdeleRing (𝓞 K) K)).2 v) := by
    intro v
    rw [hεdef, Units.val_mul, hsnd_mul, Units.val_mul, hsnd_mul, Units.val_mul, hsnd_mul]
    have h := hinv_snd p v
    rw [hp2 v, mul_one] at h
    rw [h, one_mul]
  have hε_off : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ((ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = 1 := by
    intro v hv
    rw [hε2 v, htS v hv, huS v hv, mul_one, mul_one]
    have h := hinv_snd t₀ v
    rwa [ht₀ v hv, mul_one] at h

  have heb1 : eb < 1 := by
    rw [heb, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]; omega
  have hε_S : (∀ v ∈ S, Valued.v ((((t : AdeleRing (𝓞 K) K) * (uu : AdeleRing (𝓞 K) K))).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * eb) → ∀ v ∈ S,
      Valued.v (((ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v - 1) ≤ eb ∧
      Valued.v (((ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v) = 1 := by
    intro hb v hv
    have ht0ne : Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; intro h0
      have h := hinv_snd t₀ v; rw [h0, mul_zero] at h; exact zero_ne_one h
    have hi : Valued.v ((((t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v) = (Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v))⁻¹ := by
      have h := congrArg Valued.v (hinv_snd t₀ v)
      rw [map_mul, map_one] at h
      exact eq_inv_of_mul_eq_one_left h
    have hsub : ((ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v - 1 =
        ((((t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K)).2 v *
          ((((t : AdeleRing (𝓞 K) K) * (uu : AdeleRing (𝓞 K) K))).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) := by
      rw [hε2 v, hsnd_mul, mul_sub, hinv_snd t₀ v]
    have h1 : Valued.v (((ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v - 1) ≤ eb := by
      rw [hsub, map_mul, hi]
      calc (Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v))⁻¹ *
            Valued.v (((((t : AdeleRing (𝓞 K) K) * (uu : AdeleRing (𝓞 K) K))).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v))
          ≤ (Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v))⁻¹ * (Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * eb) :=
            mul_le_mul_right (hb v hv) _
        _ = eb := by rw [← mul_assoc, inv_mul_cancel₀ ht0ne, one_mul]
    refine ⟨h1, ?_⟩
    have h := Valuation.map_one_add_of_lt Valued.v (lt_of_le_of_lt h1 heb1)
    rwa [add_sub_cancel] at h

  have hεK : (∀ v ∈ S, Valued.v ((((t : AdeleRing (𝓞 K) K) * (uu : AdeleRing (𝓞 K) K))).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * eb) →
      (diagOne ε : AdelicGL2 (𝓞 K) K) ∈ finiteAdelicGL2Subgroup K ∧
      glFin (𝓞 K) K (diagOne ε) ∈ finiteIntegralGL2 (𝓞 K) K ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K (diagOne ε)) = 1) ∧
      (∀ v ∈ S, ∀ i j : Fin 2,
        Valued.v (((((diagOne ε : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j -
            (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
          ((Multiplicative.ofAdd (-((nb + 2 * 0 : ℕ) : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) := by
    intro hb
    have hval1 : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((ε : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v) = 1 := by
      intro v; by_cases hv : v ∈ S
      · exact (hε_S hb v hv).2
      · rw [hε_off v hv, map_one]
    have hval1' : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((((ε⁻¹ : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v) = 1 := by
      intro v
      have h := congrArg Valued.v (hinv_snd ε v)
      rwa [map_mul, hval1 v, mul_one, map_one] at h
    have hdiag : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (i j : Fin 2),
        (((diagOne z : AdelicGL2 (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
          if i = j then (if i = 0 then (z : AdeleRing (𝓞 K) K) else 1) else 0 := by
      intro z i j
      rw [diagOne_coe_apply]
      fin_cases i <;> fin_cases j <;> simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (mem_finiteAdelicGL2Subgroup_iff K _).mpr (RS37P4.glArch_diagOne_of_fst_eq_one K ε hε1)
    · rw [mem_finiteIntegralGL2_iff]
      constructor
      · intro i j v
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, glFin_apply, hdiag]
        split_ifs
        · exact (hval1 v).le
        · show Valued.v ((1 : AdeleRing (𝓞 K) K).2 v) ≤ 1; rw [show (1 : AdeleRing (𝓞 K) K).2 v = 1 from rfl, map_one]
        · show Valued.v ((0 : AdeleRing (𝓞 K) K).2 v) ≤ 1; rw [show (0 : AdeleRing (𝓞 K) K).2 v = 0 from rfl, map_zero]; exact zero_le'
      · intro i j v
        rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← map_inv, glFin_apply, ← map_inv, hdiag]
        split_ifs
        · exact (hval1' v).le
        · show Valued.v ((1 : AdeleRing (𝓞 K) K).2 v) ≤ 1; rw [show (1 : AdeleRing (𝓞 K) K).2 v = 1 from rfl, map_one]
        · show Valued.v ((0 : AdeleRing (𝓞 K) K).2 v) ≤ 1; rw [show (0 : AdeleRing (𝓞 K) K).2 v = 0 from rfl, map_zero]; exact zero_le'
    · intro v hv
      refine Units.ext (Matrix.ext fun i j => ?_)
      rw [hent, hdiag, Units.val_one, Matrix.one_apply]
      split_ifs
      · exact hε_off v hv
      · rfl
      · rfl
    · intro v hv i j
      rw [show ((nb + 2 * 0 : ℕ) : ℤ) = (nb : ℤ) by push_cast; ring, ← heb, hdiag, Matrix.one_apply]
      split_ifs
      · exact (hε_S hb v hv).1
      · show Valued.v (((1 : AdeleRing (𝓞 K) K) - 1).2 v) ≤ eb; rw [sub_self, show (0 : AdeleRing (𝓞 K) K).2 v = 0 from rfl, map_zero]; exact zero_le'
      · show Valued.v (((0 : AdeleRing (𝓞 K) K) - 0).2 v) ≤ eb; rw [sub_self, show (0 : AdeleRing (𝓞 K) K).2 v = 0 from rfl, map_zero]; exact zero_le'

  have hq_arch : glArch (𝓞 K) K (diagOne (p⁻¹ * (t * uu)) : AdelicGL2 (𝓞 K) K) = 1 :=
    RS37P4.glArch_diagOne_of_fst_eq_one K _ hq1
  have hcommq : karch * diagOne (p⁻¹ * (t * uu)) = diagOne (p⁻¹ * (t * uu)) * karch :=
    (RS27.mul_comm_of_glArch_eq_one_of_glFin_eq_one K hq_arch hkarch_fin).symm
  have hgy : diagOne (t * uu) * karch = diagOne p * karch * diagOne t₀ * diagOne ε := by
    have e1 : (diagOne t₀ : AdelicGL2 (𝓞 K) K) * diagOne ε = diagOne (p⁻¹ * (t * uu)) := by
      rw [← map_mul, hεdef, mul_inv_cancel_left]
    have e2 : (diagOne p : AdelicGL2 (𝓞 K) K) * diagOne (p⁻¹ * (t * uu)) = diagOne (t * uu) := by
      rw [← map_mul, mul_inv_cancel_left]
    calc diagOne (t * uu) * karch = diagOne p * diagOne (p⁻¹ * (t * uu)) * karch := by rw [e2]
      _ = diagOne p * (karch * diagOne (p⁻¹ * (t * uu))) := by rw [hcommq, mul_assoc]
      _ = diagOne p * karch * diagOne t₀ * diagOne ε := by rw [← e1, ← mul_assoc, ← mul_assoc]
  have hgx : diagOne (t * uu) * karch * κ = diagOne p * karch * (diagOne t₀ * κ) * (κ⁻¹ * diagOne ε * κ) := by
    rw [hgy]; group

  have hκint : glFin (𝓞 K) K κ ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [hκ, AdelicDock.glFin_finEmbed]; exact (mem_maximalCompactAt_iff.mp hk₀).1.1
  have hκ0 : ∀ v ∈ S, ∀ i j : Fin 2,
      Valued.v ((((κ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd ((0 : ℕ) : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
      Valued.v (((((κ⁻¹ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)).2 v) ≤
        ((Multiplicative.ofAdd ((0 : ℕ) : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro v _ i j
    obtain ⟨h1, h2⟩ := (mem_finiteIntegralGL2_iff).mp hκint
    rw [show ((Multiplicative.ofAdd ((0 : ℕ) : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = 1 by
      rw [Nat.cast_zero, ofAdd_zero]; rfl]
    exact ⟨by rw [← hent]; exact valued_apply_le_one (h1 i j) v, by rw [← hent, map_inv]; exact valued_apply_le_one (h2 i j) v⟩

  have hcommU : ∀ i, karch * unipotentGL2 (u i) = unipotentGL2 (u i) * karch := fun i =>
    (RS27.mul_comm_of_glArch_eq_one_of_glFin_eq_one K (RS37P4.glArch_unipotentGL2_eq_one K (u i) (husupp i).1) hkarch_fin).symm
  have hxfun : x = fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (u i) * κ) := by
    funext g; rw [hxsum g]; simp only [mul_assoc]
  have hballx : whittakerCoefficient K pins ψ x 1 (diagOne (t * uu) * karch) =
      (if (∀ v ∈ S, Valued.v ((((t : AdeleRing (𝓞 K) K) * (uu : AdeleRing (𝓞 K) K))).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * eb) then whittakerCoefficient K pins ψ x₀ 1 (diagOne (NumberField.Idele.partAt K ∅ t) * karch * (diagOne t₀ * κ)) else 0) := by
    have hW1 : whittakerCoefficient K pins ψ x 1 (diagOne (t * uu) * karch) =
        (∑ i, cs i * ψ ((((t * uu : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K) * u i)) * whittakerCoefficient K pins ψ x₀ 1 (diagOne (t * uu) * karch * κ) := by
      rw [hxfun, hWmult (t * uu) karch hcommU, RS12W.whittakerCoefficient_mul_right K pins ψ x₀ 1 _ κ]
    by_cases hbox : ∀ v ∈ S, Valued.v ((((t * uu : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v) ≤
        ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    · rw [hW1, hμball (t * uu) hbox]
      by_cases hb : (∀ v ∈ S, Valued.v ((((t : AdeleRing (𝓞 K) K) * (uu : AdeleRing (𝓞 K) K))).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * eb)
      · have hb' : ∀ v ∈ S, Valued.v ((((t * uu : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
            Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * eb := hb
        rw [if_pos hb', if_pos hb, one_mul, hgx]
        obtain ⟨h1, h2, h3, h4⟩ := RS37.conj_cong K S κ 0 hκ0 nb (diagOne ε) (hεK hb).1 (hεK hb).2.1 (hεK hb).2.2.1 (hεK hb).2.2.2
        exact RS12W.whittakerCoefficient_mul_right_eq_of_forall K pins ψ x₀ 1 _ _ (fun g => hx₀cong g _ h1 h2 h3 h4)
      · have hb' : ¬ ∀ v ∈ S, Valued.v ((((t * uu : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
            Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * eb := hb
        rw [if_neg hb', if_neg hb, zero_mul]
    · push_neg at hbox
      obtain ⟨v, hv, hlt⟩ := hbox
      have hb : ¬ (∀ v ∈ S, Valued.v ((((t : AdeleRing (𝓞 K) K) * (uu : AdeleRing (𝓞 K) K))).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * eb) := by
        intro hb
        have h1 := hb v hv
        have ht0ne : Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ≠ 0 := by
          rw [Valuation.ne_zero_iff]; intro h0
          have h := hinv_snd t₀ v; rw [h0, mul_zero] at h; exact zero_ne_one h
        have hlt1 : Valued.v (((((t : AdeleRing (𝓞 K) K) * (uu : AdeleRing (𝓞 K) K))).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v)) <
            Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) := by
          refine lt_of_le_of_lt h1 ?_
          rw [← WithZero.coe_unzero ht0ne, heb, ← WithZero.coe_mul, WithZero.coe_lt_coe]
          exact mul_lt_of_lt_one_right' _ (by rw [← ofAdd_zero, Multiplicative.ofAdd_lt]; omega)
        have heq : Valued.v ((((t : AdeleRing (𝓞 K) K) * (uu : AdeleRing (𝓞 K) K))).2 v) = Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) := by
          have h := Valuation.map_add_eq_of_lt_left Valued.v hlt1
          rwa [add_sub_cancel] at h
        have : Valued.v ((((t * uu : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
          rw [Units.val_mul, heq]; exact ht₀box v hv
        exact absurd this (not_le.mpr hlt)
      rw [if_neg hb, hW1, hboxvan karch hkarch_fin hkarch_iso (t * uu) ⟨v, hv, hlt⟩, mul_zero]

  have hbally : (∀ v ∈ S, Valued.v ((((t : AdeleRing (𝓞 K) K) * (uu : AdeleRing (𝓞 K) K))).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * eb) →
      whittakerCoefficient K pins ψ y 1 (diagOne (t * uu) * karch) = whittakerCoefficient K pins ψ y 1 (diagOne (NumberField.Idele.partAt K ∅ t) * karch * diagOne t₀) := by
    intro hb
    rw [hgy]
    exact RS12W.whittakerCoefficient_mul_right_eq_of_forall K pins ψ y 1 _ _
      (fun g => hycong g _ (hεK hb).1 (hεK hb).2.1 (hεK hb).2.2.1
        (fun v hv i j => by have h := (hεK hb).2.2.2 v hv i j; rwa [show ((nb + 2 * 0 : ℕ) : ℤ) = (nb : ℤ) by push_cast; ring] at h))

  rw [hWk x hxKS t, hWk y hyKS t, hφk t, hsec k₁ t, hφ₁, hWx, hWy, hballx]
  by_cases hball : (∀ v ∈ S, Valued.v ((((t : AdeleRing (𝓞 K) K) * (uu : AdeleRing (𝓞 K) K))).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * eb)
  · rw [if_pos hball, if_pos hball, hbally hball, map_mul (starRingEnd ℂ), map_mul (starRingEnd ℂ)]
    linear_combination
      ((((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * finf karch * (whittakerCoefficient K pins ψ x₀ 1 (diagOne (NumberField.Idele.partAt K ∅ t) * karch * (diagOne t₀ * κ)) * (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 (diagOne (NumberField.Idele.partAt K ∅ t) * karch * diagOne t₀)))) *
        (((ωx D : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy D : ℂˣ) : ℂ) * (∏ v ∈ S, ((localChar ν v (d v) : ℂˣ) : ℂ)))) * hphase +
      (((NumberField.TateGlobal.ideleNorm K t : ℝ) : ℂ) ^ (s + 1 / 2) * finf karch * (whittakerCoefficient K pins ψ x₀ 1 (diagOne (NumberField.Idele.partAt K ∅ t) * karch * (diagOne t₀ * κ)) * (starRingEnd ℂ) (whittakerCoefficient K pins ψ y 1 (diagOne (NumberField.Idele.partAt K ∅ t) * karch * diagOne t₀)))) * hchar
  · rw [if_neg hball, if_neg hball]; simp

end

end S_AutomorphicForm_RankinSelberg_whittakerCoefficient_mul_conj_mul_section_diagOne_mul_eq_of_ball_surgery
end P2MW
export P2MW.S_AutomorphicForm_RankinSelberg_whittakerCoefficient_mul_conj_mul_section_diagOne_mul_eq_of_ball_surgery (solution)
