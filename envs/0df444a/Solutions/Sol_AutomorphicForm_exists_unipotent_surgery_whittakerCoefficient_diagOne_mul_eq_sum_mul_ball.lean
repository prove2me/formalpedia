-- Prove2me | solution 1 for AutomorphicForm.exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_ball
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/bfe90578-d97a-5757-a6cd-0f237bd14b38

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_NumberField_StandardAddChar_exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_ball
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm IsDedekindDomain
open scoped Classical

noncomputable section

namespace SURGBALL

attribute [local instance] Fintype.ofFinite

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private def dil (u : v.adicCompletion K) : AdeleRing (𝓞 K) K :=
  (0, AdelicDock.splice (𝓞 K) K v 0 u)

private theorem dil_fst (u : v.adicCompletion K) : (dil K v u).1 = 0 := rfl
private theorem dil_snd_self (u : v.adicCompletion K) : (dil K v u).2 v = u := AdelicDock.splice_apply_self _ _ _ _ _
private theorem dil_snd_of_ne (u : v.adicCompletion K) {v' : HeightOneSpectrum (𝓞 K)} (h : v' ≠ v) : (dil K v u).2 v' = 0 := by
  change AdelicDock.splice (𝓞 K) K v 0 u v' = 0
  rw [AdelicDock.splice_apply_of_ne _ _ _ _ _ h]; rfl

private theorem inv_mul_le_iff (g : Multiplicative ℤ) (X Y : WithZero (Multiplicative ℤ)) :
    ((g : WithZero (Multiplicative ℤ)))⁻¹ * X ≤ Y ↔ X ≤ (g : WithZero (Multiplicative ℤ)) * Y := by
  constructor
  · intro h
    calc X = (g : WithZero (Multiplicative ℤ)) * (((g : WithZero (Multiplicative ℤ)))⁻¹ * X) := by
            rw [← mul_assoc, mul_inv_cancel₀ WithZero.coe_ne_zero, one_mul]
      _ ≤ (g : WithZero (Multiplicative ℤ)) * Y := mul_le_mul_right h _
  · intro h
    calc ((g : WithZero (Multiplicative ℤ)))⁻¹ * X ≤ ((g : WithZero (Multiplicative ℤ)))⁻¹ * ((g : WithZero (Multiplicative ℤ)) * Y) :=
            mul_le_mul_right h _
      _ = Y := by rw [← mul_assoc, inv_mul_cancel₀ WithZero.coe_ne_zero, one_mul]

private theorem ball_expansion (m : ℕ) (t₀ : v.adicCompletion K) (ht₀ : t₀ ≠ 0) (n : ℕ) (hn : 0 < n) :
    ∃ (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (c : Fin r → ℂ),
      (∀ i, (y i).1 = 0 ∧ ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → (y i).2 v' = 0) ∧
      ∀ a : AdeleRing (𝓞 K) K,
        Valued.v (a.2 v) ≤ ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
        (∑ i, c i * NumberField.StandardAddChar.stdAddChar K (a * y i)) =
          if Valued.v (a.2 v - t₀) ≤ Valued.v t₀ * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0 := by
  have hv0 : Valued.v t₀ ≠ 0 := (Valuation.ne_zero_iff _).mpr ht₀
  set g : Multiplicative ℤ := WithZero.unzero hv0 with hg_def
  have hg : Valued.v t₀ = (g : WithZero (Multiplicative ℤ)) := (WithZero.coe_unzero hv0).symm
  obtain ⟨r, y, c, hsupp, hid⟩ :=
    NumberField.StandardAddChar.exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow K v
      (((m : ℤ) - Multiplicative.toAdd g).toNat) n hn
  refine ⟨r, fun i => dil K v t₀⁻¹ * y i, c, fun i => ⟨?_, fun v' hv' => ?_⟩, fun a ha => ?_⟩
  · change (dil K v _).1 * (y i).1 = 0
    rw [dil_fst, zero_mul]
  · change ((dil K v _).2 * (y i).2) v' = 0
    rw [show ((dil K v _).2 * (y i).2) v' = (dil K v _).2 v' * (y i).2 v' from rfl, (hsupp _).2 v' hv', mul_zero]
  · set b : AdeleRing (𝓞 K) K := dil K v t₀⁻¹ * a with hb
    have hbv : b.2 v = t₀⁻¹ * a.2 v := by
      change ((dil K v _).2 * a.2) v = _
      rw [show ((dil K v _).2 * a.2) v = (dil K v _).2 v * a.2 v from rfl, dil_snd_self]
    have hvb : Valued.v (b.2 v) = ((g : WithZero (Multiplicative ℤ)))⁻¹ * Valued.v (a.2 v) := by
      rw [hbv, Valuation.map_mul, map_inv₀, hg]
    have hval : Valued.v (b.2 v) ≤
        ((Multiplicative.ofAdd ((((m : ℤ) - Multiplicative.toAdd g).toNat : ℕ) : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      rw [hvb]
      calc ((g : WithZero (Multiplicative ℤ)))⁻¹ * Valued.v (a.2 v)
          ≤ ((g : WithZero (Multiplicative ℤ)))⁻¹ * ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := mul_le_mul_right ha _
        _ = ((Multiplicative.ofAdd ((m : ℤ) - Multiplicative.toAdd g) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
            rw [← WithZero.coe_inv, ← WithZero.coe_mul]
            congr 1
            rw [show g = Multiplicative.ofAdd (Multiplicative.toAdd g) from (ofAdd_toAdd g).symm, ← ofAdd_neg, ← ofAdd_add,
              toAdd_ofAdd]
            congr 1; ring
        _ ≤ _ := by
            rw [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
            exact Int.self_le_toNat _
    have hre : ∀ i, a * (dil K v t₀⁻¹ * y i) = b * y i := fun i => by rw [hb, mul_left_comm, ← mul_assoc]
    have hsub : b.2 v - 1 = t₀⁻¹ * (a.2 v - t₀) := by
      rw [hbv, mul_sub, inv_mul_cancel₀ ht₀]
    have hiff : Valued.v (b.2 v - 1) ≤ ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ↔
        Valued.v (a.2 v - t₀) ≤ Valued.v t₀ * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      rw [hsub, Valuation.map_mul, map_inv₀, hg]
      exact inv_mul_le_iff g _ _
    simp_rw [hre]
    rw [hid b hval]
    by_cases h : Valued.v (a.2 v - t₀) ≤ Valued.v t₀ * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]

private theorem ball_expansion_finset (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (t₀ : (AdeleRing (𝓞 K) K)ˣ)
    (ht₀ : ∀ w : HeightOneSpectrum (𝓞 K), ((t₀ : AdeleRing (𝓞 K) K)).2 w ≠ 0) (n : ℕ) (hn : 0 < n) :
    ∃ (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (c : Fin r → ℂ),
      (∀ i, (y i).1 = 0 ∧ ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → (y i).2 w = 0) ∧
      ∀ a : AdeleRing (𝓞 K) K,
        (∀ v ∈ S, Valued.v (a.2 v) ≤ ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, c i * NumberField.StandardAddChar.stdAddChar K (a * y i)) =
          if ∀ v ∈ S, Valued.v (a.2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤ Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0 := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ => 0, fun _ => 1, fun _ => ⟨rfl, fun _ _ => rfl⟩, fun a _ => ?_⟩
    simp [AddChar.map_zero_eq_one]
  | @insert v S hvS ih =>
    obtain ⟨r, y, c, hs, hid⟩ := ih
    obtain ⟨r', y', c', hs', hid'⟩ := ball_expansion K v m (((t₀ : AdeleRing (𝓞 K) K)).2 v) (ht₀ v) n hn
    set eqv := (finProdFinEquiv (m := r) (n := r')).symm with heqv
    refine ⟨r * r', fun j => y (eqv j).1 + y' (eqv j).2, fun j => c (eqv j).1 * c' (eqv j).2,
      fun j => ⟨?_, fun w hw => ?_⟩, fun a ha => ?_⟩
    · change (y (eqv j).1).1 + (y' (eqv j).2).1 = 0
      rw [(hs _).1, (hs' _).1, add_zero]
    · rw [Finset.mem_insert, not_or] at hw
      change ((y (eqv j).1).2 + (y' (eqv j).2).2) w = 0
      rw [show ((y (eqv j).1).2 + (y' (eqv j).2).2) w = (y (eqv j).1).2 w + (y' (eqv j).2).2 w from rfl,
        (hs _).2 w hw.2, (hs' _).2 w hw.1, add_zero]
    · have hre : (∑ j : Fin (r * r'), c (eqv j).1 * c' (eqv j).2 *
          NumberField.StandardAddChar.stdAddChar K (a * (y (eqv j).1 + y' (eqv j).2))) =
          ∑ p : Fin r × Fin r', c p.1 * c' p.2 * NumberField.StandardAddChar.stdAddChar K (a * (y p.1 + y' p.2)) :=
        Equiv.sum_comp eqv (fun p : Fin r × Fin r' => c p.1 * c' p.2 * NumberField.StandardAddChar.stdAddChar K (a * (y p.1 + y' p.2)))
      rw [hre, Fintype.sum_prod_type]
      have hsplit : ∀ i j, c i * c' j * NumberField.StandardAddChar.stdAddChar K (a * (y i + y' j)) =
          (c i * NumberField.StandardAddChar.stdAddChar K (a * y i)) * (c' j * NumberField.StandardAddChar.stdAddChar K (a * y' j)) := by
        intro i j
        rw [mul_add, AddChar.map_add_eq_mul]; ring
      simp_rw [hsplit, ← Finset.mul_sum, ← Finset.sum_mul]
      rw [hid a fun w hw => ha w (Finset.mem_insert_of_mem hw), hid' a (ha v (Finset.mem_insert_self v S))]
      by_cases h1 : ∀ w ∈ S, Valued.v (a.2 w - ((t₀ : AdeleRing (𝓞 K) K)).2 w) ≤ Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 w) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) <;>
        by_cases h2 : Valued.v (a.2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤ Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      · rw [if_pos h1, if_pos h2, one_mul, if_pos ((Finset.forall_mem_insert v S
          (fun w => Valued.v (a.2 w - ((t₀ : AdeleRing (𝓞 K) K)).2 w) ≤ Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 w) * ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))).mpr ⟨h2, h1⟩)]
      · rw [if_pos h1, if_neg h2, mul_zero, if_neg (fun h => h2 (h v (Finset.mem_insert_self v S)))]
      · rw [if_neg h1, zero_mul, if_neg (fun h => h1 fun w hw => h w (Finset.mem_insert_of_mem hw))]
      · rw [if_neg h1, zero_mul, if_neg (fun h => h1 fun w hw => h w (Finset.mem_insert_of_mem hw))]

private theorem gl_ext {g h : AdelicGL2 (𝓞 K) K} (h₁ : glArch (𝓞 K) K g = glArch (𝓞 K) K h)
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

private theorem finComponent_unipotentGL2_eq_one {y : AdeleRing (𝓞 K) K} {u : HeightOneSpectrum (𝓞 K)} (hy : y.2 u = 0) :
    finComponent (𝓞 K) K u (glFin (𝓞 K) K (unipotentGL2 y)) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [finComponent_apply, glFin_apply, unipotentGL2_coe, Units.val_one]
  fin_cases i <;> fin_cases j
  · rfl
  · exact hy
  · rfl
  · rfl

private theorem commute_placeEmbed {y : AdeleRing (𝓞 K) K} {v : HeightOneSpectrum (𝓞 K)} (hy : y.2 v = 0)
    (xv : GL (Fin 2) (v.adicCompletion K)) :
    unipotentGL2 y * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * unipotentGL2 y := by
  have hP : UnramifiedWhittaker.placeEmbed K v xv = AdelicDock.finEmbed (𝓞 K) K (AdelicDock.localEmbed (𝓞 K) K v xv) := rfl
  refine gl_ext K ?_ fun u => ?_
  · rw [map_mul, map_mul, hP, AdelicDock.glArch_finEmbed, mul_one, one_mul]
  · rw [map_mul, map_mul, map_mul, map_mul]
    by_cases hu : u = v
    · subst hu
      rw [finComponent_unipotentGL2_eq_one K hy, one_mul, mul_one]
    · rw [hP, AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_of_ne _ _ _ _ hu, mul_one, one_mul]

private theorem snd_apply_ne_zero (t₀ : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    ((t₀ : AdeleRing (𝓞 K) K)).2 w ≠ 0 := by
  have h : ((t₀ : AdeleRing (𝓞 K) K)).2 w * (((t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 w = 1 := by
    rw [show ((t₀ : AdeleRing (𝓞 K) K)).2 w * (((t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 w =
      (((t₀ : AdeleRing (𝓞 K) K)) * ((t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 w from rfl, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
    rfl
  exact left_ne_zero_of_mul_eq_one h

private theorem main
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (G : AdelicGL2 (𝓞 K) K → ℂ)
    (hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K),
      G (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * h) = G (unipotentGL2 u * h))
    (hint : ∀ (α : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) G α g)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (t₀ : (AdeleRing (𝓞 K) K)ˣ) (n : ℕ) (hn : 0 < n) :
    ∃ (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ),
      (∀ i, (y i).1 = 0 ∧ ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → (y i).2 w = 0) ∧
      (∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
        unipotentGL2 (y i) * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * unipotentGL2 (y i)) ∧
      (∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (y i) = unipotentGL2 (y i) * g') →
        whittakerCoefficient K
            (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
            (fun g => ∑ i, cs i * G (g * unipotentGL2 (y i))) 1 (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) *
            whittakerCoefficient K
              (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) G 1 (diagOne t * g')) ∧
      (∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) *
                ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0) := by
  obtain ⟨r, y, cs, hs, hid⟩ := ball_expansion_finset K S m t₀ (snd_apply_ne_zero K t₀) n hn
  refine ⟨r, y, cs, hs, fun i v hv xv => commute_placeEmbed K ((hs i).2 v hv) xv, fun t g' hcomm => ?_, fun t ht => hid _ ht⟩

  set ι : Finset (AdeleRing (𝓞 K) K) := Finset.univ.image y with hι
  set c : AdeleRing (𝓞 K) K → ℂ := fun z => ∑ i ∈ Finset.univ.filter (fun i => y i = z), cs i with hc
  have hagg : ∀ (f : AdeleRing (𝓞 K) K → ℂ), (∑ i, cs i * f (y i)) = ∑ z ∈ ι, c z * f z := by
    intro f
    rw [← Finset.sum_fiberwise_of_maps_to (g := y) (t := ι) (fun i _ => Finset.mem_image_of_mem y (Finset.mem_univ i))]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [hi.2]
  have hψ : IsPrincipalInvariantAddChar K (NumberField.StandardAddChar.stdAddChar K) :=
    fun α => (NumberField.StandardAddChar.adelicTraceData K).psiK_algebraMap α
  have hcomm' : ∀ z ∈ ι, g' * unipotentGL2 z = unipotentGL2 z * g' := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact hcomm i
  have hint' : ∀ z ∈ ι, WhittakerCoefficientIntegrable K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) (fun x => G (x * unipotentGL2 z)) 1 (diagOne t * g') := by
    intro z _
    have := hint 1 (diagOne t * g' * unipotentGL2 z)
    simpa [WhittakerCoefficientIntegrable, mul_assoc] using this
  have hW := AutomorphicForm.whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul K D
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (NumberField.StandardAddChar.stdAddChar K) hψ G hper ι c 1 t g' hcomm' hint'
  have hfun : (fun g => ∑ i, cs i * G (g * unipotentGL2 (y i))) = fun x => ∑ z ∈ ι, c z * G (x * unipotentGL2 z) := by
    funext x; exact hagg (fun z => G (x * unipotentGL2 z))
  rw [hfun, hW, hagg (fun z => NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * z))]
  simp only [map_one, one_mul]

end SURGBALL

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (G : AdelicGL2 (𝓞 K) K → ℂ)
    (hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K) (h : AdelicGL2 (𝓞 K) K),
      G (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * h) = G (unipotentGL2 u * h))
    (hint : ∀ (α : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) G α g)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ℕ) (t₀ : (AdeleRing (𝓞 K) K)ˣ) (n : ℕ) (hn : 0 < n) :
    ∃ (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (cs : Fin r → ℂ),
      (∀ i, (y i).1 = 0 ∧ ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → (y i).2 w = 0) ∧
      (∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
        unipotentGL2 (y i) * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * unipotentGL2 (y i)) ∧
      (∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (y i) = unipotentGL2 (y i) * g') →
        whittakerCoefficient K
            (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
            (fun g => ∑ i, cs i * G (g * unipotentGL2 (y i))) 1 (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) *
            whittakerCoefficient K
              (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
                (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) G 1 (diagOne t * g')) ∧
      (∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v - ((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
              Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) *
                ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0) :=
  open scoped Classical in SURGBALL.main K D G hper hint S m t₀ n hn

end S_AutomorphicForm_exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_ball
end P2MW
export P2MW.S_AutomorphicForm_exists_unipotent_surgery_whittakerCoefficient_diagOne_mul_eq_sum_mul_ball (solution)
