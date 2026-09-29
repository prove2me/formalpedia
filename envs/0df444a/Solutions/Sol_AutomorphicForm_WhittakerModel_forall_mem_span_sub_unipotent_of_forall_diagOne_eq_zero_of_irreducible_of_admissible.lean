-- Prove2me | solution 1 for AutomorphicForm.WhittakerModel.forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/395e66d4-ce4f-5255-a89a-81e015fc09e8

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_WhittakerModel_eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne
import Theorems.Thm_AutomorphicForm_WhittakerModel_exists_forall_diagOne_eq_zero_of_lt_modulus
import Theorems.Thm_AutomorphicForm_LocalFunctionSpace_exists_finset_forall_eq_sum_mul_char_mul
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one
import Theorems.Thm_AdelicDock_isCompact_and_isOpen_localLevelOne
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_WhittakerModel_forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "WhittakerModel.eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne WhittakerModel.exists_forall_diagOne_eq_zero_of_lt_modulus LocalFunctionSpace.exists_finset_forall_eq_sum_mul_char_mul"
namespace WhittakerModel
p2m_export "AutomorphicForm.WhittakerModel" "eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne exists_forall_diagOne_eq_zero_of_lt_modulus"
namespace JacquetVanish
p2m_open "AutomorphicForm.WhittakerModel AutomorphicForm"

open scoped Classical

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => p.adicCompletion ℚ
local notation "Mat" => Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)
local notation "G2" => GL (Fin 2) (p.adicCompletion ℚ)

theorem unipotent_coe (x : F) : ((unipotent x : G2) : Mat) = !![1, x; 0, 1] := rfl

theorem diagOne_coe (a : (F)ˣ) : ((diagOne a : G2) : Mat) = !![(a : F), 0; 0, 1] := by
  ext i j
  rw [NumberField.AdelicLevel.diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem gl_eq_of_entries {g h : G2}
    (h00 : (g : Mat) 0 0 = (h : Mat) 0 0) (h01 : (g : Mat) 0 1 = (h : Mat) 0 1)
    (h10 : (g : Mat) 1 0 = (h : Mat) 1 0) (h11 : (g : Mat) 1 1 = (h : Mat) 1 1) : g = h := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem mul_coe_apply (g h : G2) (i j : Fin 2) :
    ((g * h : G2) : Mat) i j = (g : Mat) i 0 * (h : Mat) 0 j + (g : Mat) i 1 * (h : Mat) 1 j := by
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagOne_mul_unipotent (a : (F)ˣ) (x : F) :
    (diagOne a : G2) * unipotent x = unipotent ((a : F) * x) * diagOne a := by
  apply gl_eq_of_entries <;> simp [mul_coe_apply, unipotent_coe, diagOne_coe]

def qR : ℝ := ((Ideal.absNorm p.asIdeal : NNReal) : ℝ)

theorem one_lt_qR : 1 < qR p := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal p
  unfold qR; exact_mod_cast this

theorem norm_eq_qR_zpow (y : F) (j : ℤ) (hy : Valued.v y = WithZero.exp (-j)) : ‖y‖ = qR p ^ (-j) := by
  rw [NumberField.FinitePlace.norm_def, hy, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, NNReal.coe_zpow]
  unfold qR
  congr 1

theorem qR_zpow_le_norm {y : F} {n : ℤ} (h : WithZero.exp n ≤ Valued.v y) : qR p ^ n ≤ ‖y‖ := by
  have hvy : Valued.v y ≠ 0 := by
    intro h0; rw [h0] at h; exact absurd h (not_le.2 (zero_lt_iff.2 WithZero.exp_ne_zero))
  set m : ℤ := WithZero.log (Valued.v y) with hm
  have hy : Valued.v y = WithZero.exp m := (WithZero.exp_log hvy).symm
  rw [norm_eq_qR_zpow p y (-m) (by rw [neg_neg]; exact hy), neg_neg]
  rw [hy, WithZero.exp_le_exp] at h
  exact zpow_le_zpow_right₀ (one_lt_qR p).le h

theorem coe_modulus_eq_norm (x : F) : ((modulus x : NNReal) : ℝ) = ‖x‖ := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm]

section Span
variable {G : Type*} [Group G]

theorem comp_mul_mem_span (w : G → ℂ) {w' : G → ℂ}
    (hw' : w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) (h : G) :
    (fun g => w' (g * h)) ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h)) := by
  let R : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun f g => f (g * h), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hR : R w' ∈ (Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))).map R :=
    Submodule.mem_map_of_mem hw'
  rw [Submodule.map_span] at hR
  refine (Submodule.span_mono ?_) hR
  rintro _ ⟨_, ⟨h', rfl⟩, rfl⟩
  exact ⟨h * h', by funext g; simp [R, mul_assoc]⟩

theorem law_of_mem_span (w : G → ℂ) (a : G) (c : ℂ) (hw : ∀ g : G, w (a * g) = c * w g) {w' : G → ℂ}
    (hw' : w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) :
    ∀ g : G, w' (a * g) = c * w' g := by
  induction hw' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    intro g
    show w (a * g * h) = c * w (g * h)
    rw [mul_assoc, hw]
  | zero => intro g; simp
  | add x y _ _ hx hy => intro g; simp only [Pi.add_apply, hx, hy, mul_add]
  | smul r x _ hx => intro g; simp only [Pi.smul_apply, smul_eq_mul, hx]; ring

theorem smooth_of_mem_span [TopologicalSpace G] [ContinuousMul G] (w : G → ℂ)
    (hwsm : ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w (g * k) = w g) {w' : G → ℂ}
    (hw' : w' ∈ Submodule.span ℂ (Set.range fun h : G => fun g : G => w (g * h))) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ k ∈ U, ∀ g : G, w' (g * k) = w' g := by
  induction hw' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    obtain ⟨U, hUo, hU⟩ := hwsm
    refine ⟨U.comap (MulAut.conj h⁻¹).toMonoidHom, ?_, ?_⟩
    · have hc : Continuous fun k : G => h⁻¹ * k * h⁻¹⁻¹ := (continuous_const.mul continuous_id).mul continuous_const
      have : ((U.comap (MulAut.conj h⁻¹).toMonoidHom : Subgroup G) : Set G) = (fun k : G => h⁻¹ * k * h⁻¹⁻¹) ⁻¹' (U : Set G) := by
        ext k; simp [Subgroup.coe_comap]
      rw [this]
      exact hUo.preimage hc
    · intro k hk g
      have hk' : h⁻¹ * k * h ∈ U := by simpa [Subgroup.mem_comap, MulAut.conj_apply] using hk
      show w (g * k * h) = w (g * h)
      have := hU _ hk' (g * h)
      rw [← this]
      congr 1
      group
  | zero => exact ⟨⊤, by simp, fun _ _ _ => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, h₁o, h₁⟩ := hx
    obtain ⟨U₂, h₂o, h₂⟩ := hy
    refine ⟨U₁ ⊓ U₂, ?_, fun k hk g => ?_⟩
    · rw [Subgroup.coe_inf]; exact h₁o.inter h₂o
    · simp only [Pi.add_apply, h₁ k (Subgroup.mem_inf.1 hk).1 g, h₂ k (Subgroup.mem_inf.1 hk).2 g]
  | smul r x _ hx =>
    obtain ⟨U, ho, hU⟩ := hx
    exact ⟨U, ho, fun k hk g => by simp only [Pi.smul_apply, hU k hk g]⟩

end Span

theorem main
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))

    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      W ∈ Submodule.span ℂ {D : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ W' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ t : p.adicCompletion ℚ, D = fun g : GL (Fin 2) (p.adicCompletion ℚ) => W' (g * unipotent t) - W' g} := by
  intro W hW

  set V : Submodule ℂ (G2 → ℂ) := Submodule.span ℂ (Set.range fun h : G2 => fun g : G2 => w₂base (g * h)) with hV

  have hWlaw : ∀ (x : F) (g : G2), W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g :=
    fun x => law_of_mem_span w₂base (unipotent x) _ (hw₂law x) hW
  have hWsm : ∃ U : Subgroup G2, IsOpen (U : Set G2) ∧ ∀ k ∈ U, ∀ g : G2, W (g * k) = W g :=
    smooth_of_mem_span w₂base ⟨AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N,
      (AdelicDock.isCompact_and_isOpen_localLevelOne ℚ p N hN).2, hw₂K⟩ hW

  obtain ⟨N₀, hN₀⟩ := hcusp W hW
  obtain ⟨c, hc0, hc⟩ := AutomorphicForm.WhittakerModel.exists_forall_diagOne_eq_zero_of_lt_modulus p W hWlaw hWsm
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt c (one_lt_qR p)
  have hupper : ∀ y : (F)ˣ, WithZero.exp (n : ℤ) ≤ Valued.v (y : F) → W (diagOne y) = 0 := by
    intro y hy
    refine hc y ?_
    have h1 : qR p ^ (n : ℤ) ≤ ‖(y : F)‖ := qR_zpow_le_norm p hy
    rw [zpow_natCast] at h1
    have : c < ‖(y : F)‖ := lt_of_lt_of_le hn h1
    rwa [← coe_modulus_eq_norm] at this

  have hψadd : ∀ x y : F, NumberField.StandardAddChar.psiLocal ℚ p (x + y) =
      NumberField.StandardAddChar.psiLocal ℚ p x * NumberField.StandardAddChar.psiLocal ℚ p y :=
    fun x y => AddChar.map_add_eq_mul _ x y
  have hψ1 : ∃ γ₀ : (WithZero (Multiplicative ℤ))ˣ,
      ∀ x : F, Valued.v x < (γ₀ : WithZero (Multiplicative ℤ)) → NumberField.StandardAddChar.psiLocal ℚ p x = 1 := by
    refine ⟨1, fun x hx => LanglandsTunnell.TateLocal.psiLocal_eq_one_of_mem_integers ℚ p x ?_⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact le_of_lt (by simpa using hx)
  have hψ2 : ∃ x₀ : F, NumberField.StandardAddChar.psiLocal ℚ p x₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact LanglandsTunnell.TateLocal.psiLocal_ne_one ℚ p (AddChar.ext _ _ (fun x => by rw [h x, AddChar.one_apply]))
  set f : F → ℂ := fun x => if Valued.v x ≤ WithZero.exp N₀ then 1 else 0 with hf
  have hflc : ∀ x y : F, Valued.v (x - y) < ((Units.mk0 (WithZero.exp N₀) WithZero.exp_ne_zero : (WithZero (Multiplicative ℤ))ˣ) :
      WithZero (Multiplicative ℤ)) → f x = f y := by
    intro x y hxy
    rw [Units.val_mk0] at hxy
    have key : ∀ {a b : F}, Valued.v (a - b) < WithZero.exp N₀ → Valued.v b ≤ WithZero.exp N₀ → Valued.v a ≤ WithZero.exp N₀ := by
      intro a b hab hb
      have : a = b + (a - b) := by ring
      rw [this]
      exact le_trans (Valuation.map_add _ _ _) (max_le hb hab.le)
    have hyx : Valued.v (y - x) < WithZero.exp N₀ := by rwa [← Valuation.map_neg, neg_sub] at hxy
    by_cases hx : Valued.v x ≤ WithZero.exp N₀
    · have hy : Valued.v y ≤ WithZero.exp N₀ := key hyx hx
      simp only [hf, hx, hy]
    · have hy : ¬ Valued.v y ≤ WithZero.exp N₀ := fun hy => hx (key hxy hy)
      simp only [hf, hx, hy]
  obtain ⟨T, cf, hT⟩ := AutomorphicForm.LocalFunctionSpace.exists_finset_forall_eq_sum_mul_char_mul p
    (NumberField.StandardAddChar.psiLocal ℚ p) hψadd hψ1 hψ2 f _ hflc
    (Units.mk0 (WithZero.exp ((n : ℤ))) WithZero.exp_ne_zero)

  set S : G2 → ℂ := fun g => ∑ t ∈ T, cf t * W (g * unipotent t) with hS
  have hSeq : S = ∑ t ∈ T, cf t • (fun g : G2 => W (g * unipotent t)) := by
    funext g
    simp only [hS, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hSV : S ∈ V := by
    rw [hSeq]
    refine Submodule.sum_mem _ (fun t _ => ?_)
    exact Submodule.smul_mem _ (cf t) (comp_mul_mem_span w₂base hW (unipotent t))
  have hSkir : ∀ y : (F)ˣ, S (diagOne y) = 0 := by
    intro y
    have e : S (diagOne y) = (∑ t ∈ T, cf t * NumberField.StandardAddChar.psiLocal ℚ p ((y : F) * t)) * W (diagOne y) := by
      simp only [hS, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [diagOne_mul_unipotent, hWlaw]; ring
    rw [e]
    by_cases hWy : W (diagOne y) = 0
    · rw [hWy, mul_zero]
    ·
      have hlo : ¬ Valued.v (y : F) ≤ WithZero.exp N₀ := fun h => hWy (hN₀ y h)
      have hhi : Valued.v (y : F) < WithZero.exp (n : ℤ) := lt_of_not_ge (fun h => hWy (hupper y h))
      have := hT (y : F) (by rw [Units.val_mk0]; exact hhi)
      rw [← this]
      simp only [hf, hlo, if_false, zero_mul]
  have hS0 : S = 0 :=
    AutomorphicForm.WhittakerModel.eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne p N hN w₂base
      hw₂law hw₂K hw₂ne hw₂irr hw₂adm S hSV hSkir

  have hsum : ∑ t ∈ T, cf t = 1 := by
    have h0 := hT 0 (by rw [Valuation.map_zero, Units.val_mk0]; exact zero_lt_iff.2 WithZero.exp_ne_zero)
    simp only [hf, Valuation.map_zero, zero_le', if_true, zero_mul, AddChar.map_zero_eq_one, mul_one] at h0
    exact h0.symm

  have hWeq : W = ∑ t ∈ T, (-cf t) • (fun g : G2 => W (g * unipotent t) - W g) := by
    funext g
    have hSg : S g = 0 := by rw [hS0]; rfl
    simp only [hS] at hSg
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, neg_mul, mul_sub, Finset.sum_neg_distrib, Finset.sum_sub_distrib,
      hSg, ← Finset.sum_mul, hsum, one_mul]
    ring
  rw [hWeq]
  refine Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact ⟨W, hW, t, rfl⟩

end AutomorphicForm.WhittakerModel.JacquetVanish

end

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ))
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))

    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      W ∈ Submodule.span ℂ {D : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ W' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ t : p.adicCompletion ℚ, D = fun g : GL (Fin 2) (p.adicCompletion ℚ) => W' (g * unipotent t) - W' g} :=
  AutomorphicForm.WhittakerModel.JacquetVanish.main p N hN w₂base hw₂law hw₂K hw₂ne hw₂irr hw₂adm hcusp

end S_AutomorphicForm_WhittakerModel_forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible
end P2MW
export P2MW.S_AutomorphicForm_WhittakerModel_forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible (solution)
