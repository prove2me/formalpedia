-- Prove2me | solution 1 for AutomorphicForm.exists_linearMap_resolvent_integral_comp_sigmaTensor_sub_mul_eq_integral_mul_comp_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/2430d35b-f765-5b74-baf6-8c0918051e34

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

import Theorems.Thm_AutomorphicForm_sigmaTensor_twistedResolvent_sub_mul_eq_one_sub_norm_smul_and_twistedResolvent_sigmaTensor_sub_mul_eq
import Theorems.Thm_AutomorphicForm_map_mul_sigmaTensor_sub_mul_addHaar_infiniteAdeleRing_eq_inv_prod_norm_archEval_algebraNorm_sub_pow_mult_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_linearMap_resolvent_integral_comp_sigmaTensor_sub_mul_eq_integral_mul_comp_smul

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped ENNReal Classical

noncomputable section

namespace TwR3

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] (σ : L ≃ₐ[K] L)

local notation "E" => (L ⊗[K] InfiniteAdeleRing K)
local notation "A" => (InfiniteAdeleRing K)

def gLin (g : L ≃ₐ[K] L) : E →ₗ[A] E where
  toFun := AutomorphicForm.sigmaTensor K L A g
  map_add' := map_add _
  map_smul' := by
    intro c y
    have h1 : AutomorphicForm.sigmaTensor K L A g ((1 : L) ⊗ₜ[K] c) = (1 : L) ⊗ₜ[K] c := by
      show (Algebra.TensorProduct.map (g : L →ₐ[K] L) (AlgHom.id K A)) ((1 : L) ⊗ₜ[K] c) = (1 : L) ⊗ₜ[K] c
      rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
    rw [AutomorphicForm.rightActions_smul_eq, map_mul, h1, AutomorphicForm.rightActions_smul_eq, RingHom.id_apply]

theorem gLin_apply (g : L ≃ₐ[K] L) (y : E) : gLin K L g y = AutomorphicForm.sigmaTensor K L A g y := rfl

theorem gLin_pow_apply (g : L ≃ₐ[K] L) (n : ℕ) (y : E) :
    (gLin K L g ^ n) y = (AutomorphicForm.sigmaTensor K L A g)^[n] y := by
  induction n generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, gLin_apply, Function.iterate_succ_apply']

def Mlin (r : E) : E →ₗ[A] E :=
  ∑ j ∈ Finset.range (Module.finrank K L),
    (Algebra.lmul A E (∏ i ∈ Finset.range j, (AutomorphicForm.sigmaTensor K L A σ.symm)^[i + 1] r) : E →ₗ[A] E) *
      gLin K L σ.symm ^ (j + 1)

theorem Mlin_apply (r y : E) :
    Mlin K L σ r y = ∑ j ∈ Finset.range (Module.finrank K L),
      (∏ i ∈ Finset.range j, (AutomorphicForm.sigmaTensor K L A σ.symm)^[i + 1] r) *
        (AutomorphicForm.sigmaTensor K L A σ.symm)^[j + 1] y := by
  unfold Mlin
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Module.End.mul_apply, gLin_pow_apply]; rfl

def Tlin (r : E) : E →ₗ[A] E := gLin K L σ - (Algebra.lmul A E r : E →ₗ[A] E)

theorem Tlin_apply (r y : E) : Tlin K L σ r y = AutomorphicForm.sigmaTensor K L A σ y - r * y := by
  simp [Tlin, gLin_apply, Algebra.coe_lmul_eq_mul]

end TwR3

end

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (r : L ⊗[K] InfiniteAdeleRing K) (c : (InfiniteAdeleRing K)ˣ)
    (hc : (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) r) :
    ∃ M : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K), Continuous M ∧
      (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y) ∧
      (∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y) ∧
      (∀ g : (L ⊗[K] InfiniteAdeleRing K) → ℂ,
        Integrable (fun y => g (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y)) lam ↔ Integrable g lam) ∧
      ∀ F G : (L ⊗[K] InfiniteAdeleRing K) → ℂ,
        ((∏ v : NumberField.InfinitePlace K, ‖NumberField.AdelicLevel.archEval K v (c : InfiniteAdeleRing K)‖ ^ v.mult : ℝ) : ℂ) *
            ∫ y, F (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) * G y ∂lam =
          ∫ y, F y * G (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M y) ∂lam := by
  classical
  haveI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  have hC1 := fun y => AutomorphicForm.sigmaTensor_twistedResolvent_sub_mul_eq_one_sub_norm_smul_and_twistedResolvent_sigmaTensor_sub_mul_eq
    K L σ hgen (InfiniteAdeleRing K) r y
  set M := TwR3.Mlin K L σ r with hM
  have hMy : ∀ y, M y = ∑ j ∈ Finset.range (Module.finrank K L),
      (∏ i ∈ Finset.range j, (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ.symm)^[i + 1] r) *
        (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ.symm)^[j + 1] y := fun y => by
    rw [hM, TwR3.Mlin_apply]
  have hcsmul : ∀ y : L ⊗[K] InfiniteAdeleRing K,
      (c : InfiniteAdeleRing K) • y = algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) (1 - Algebra.norm (InfiniteAdeleRing K) r) * y := by
    intro y; rw [AutomorphicForm.rightActions_smul_eq, ← TensorProduct.RightActions.algebraMap_eval, hc]
  have h2 : ∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y := by
    intro y; rw [hMy, hcsmul]; exact (hC1 y).1
  have h3 : ∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y := by
    intro y; rw [hMy, hcsmul]; exact (hC1 y).2

  have hMc : Continuous M := IsModuleTopology.continuous_of_linearMap M
  have hTc : Continuous (TwR3.Tlin K L σ r) := IsModuleTopology.continuous_of_linearMap _

  have hunit : IsUnit ((c : InfiniteAdeleRing K)) := c.isUnit
  let Minv : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K) :=
    ((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M
  have hMinv : ∀ y, Minv y = ((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M y := fun y => rfl
  have hleft : ∀ y, Minv (TwR3.Tlin K L σ r y) = y := by
    intro y
    rw [hMinv, TwR3.Tlin_apply, h3, smul_smul, Units.inv_mul, one_smul]
  have hright : ∀ y, TwR3.Tlin K L σ r (Minv y) = y := by
    intro y
    rw [hMinv, LinearMap.map_smul, TwR3.Tlin_apply, h2, smul_smul, Units.inv_mul, one_smul]
  let eT : (L ⊗[K] InfiniteAdeleRing K) ≃ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K) :=
    { TwR3.Tlin K L σ r with
      invFun := Minv
      left_inv := hleft
      right_inv := hright }
  have heT : ∀ y, eT y = AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y := fun y => TwR3.Tlin_apply K L σ r y
  let eTc : (L ⊗[K] InfiniteAdeleRing K) ≃L[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K) :=
    { eT with
      continuous_toFun := hTc
      continuous_invFun := by
        have hc' : Continuous fun y => ((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M y :=
          hMc.const_smul ((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)
        exact hc' }
  let eM : (L ⊗[K] InfiniteAdeleRing K) ≃ᵐ (L ⊗[K] InfiniteAdeleRing K) := eTc.toHomeomorph.toMeasurableEquiv
  have heM : ∀ y, eM y = AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y := heT

  have hab : IsUnit (Algebra.norm (InfiniteAdeleRing K) (1 : L ⊗[K] InfiniteAdeleRing K) - Algebra.norm (InfiniteAdeleRing K) r) := by
    rw [map_one, ← hc]; exact c.isUnit
  obtain ⟨hmap, hint⟩ := AutomorphicForm.map_mul_sigmaTensor_sub_mul_addHaar_infiniteAdeleRing_eq_inv_prod_norm_archEval_algebraNorm_sub_pow_mult_smul K L σ hgen hdeg lam 1 r hab
  simp only [one_mul, map_one] at hmap hint
  rw [← hc] at hmap hint
  set P : ℝ := ∏ w : NumberField.InfinitePlace K, ‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ ^ w.mult with hP
  have hPpos : 0 < P := by
    rw [hP]
    refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr ?_) _
    exact ((Pi.isUnit_iff.mp c.isUnit) w).ne_zero
  have hmapE : Measure.map eM lam = ENNReal.ofReal P⁻¹ • lam := by
    rw [← hmap]; congr 1
  refine ⟨M, hMc, h2, h3, ?_, ?_⟩
  · intro g
    have e1 : (fun y => g (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y)) = g ∘ eM := by
      funext y; simp [heM]
    rw [e1, ← integrable_map_equiv eM g, hmapE]
    exact integrable_smul_measure (by simp [hPpos]) ENNReal.ofReal_ne_top
  · intro F G
    have key := hint (fun z => F z * G (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M z))
    have e2 : (fun y => F (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) *
        G (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y))) =
        fun y => F (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) * G y := by
      funext y; rw [h3, smul_smul, Units.inv_mul, one_smul]
    rw [e2] at key
    rw [key, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hPpos.ne', Complex.ofReal_one, one_mul]

end S_AutomorphicForm_exists_linearMap_resolvent_integral_comp_sigmaTensor_sub_mul_eq_integral_mul_comp_smul
end P2MW
export P2MW.S_AutomorphicForm_exists_linearMap_resolvent_integral_comp_sigmaTensor_sub_mul_eq_integral_mul_comp_smul (solution)
