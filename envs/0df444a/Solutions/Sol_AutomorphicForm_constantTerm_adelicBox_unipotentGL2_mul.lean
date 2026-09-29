-- Prove2me | solution 1 for AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9652346c-a4d2-5d3b-b55a-7f46225091c3

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul

set_option autoImplicit false

open MeasureTheory Set NumberField IsDedekindDomain
open AutomorphicForm NumberField.AdelicHaar NumberField.AdelicBox
open scoped ProbabilityTheory Pointwise

noncomputable section

namespace M4aP3B
namespace Rows

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

section FD

variable (K : Type) [Field K] [NumberField K]

theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 K) K) :=
  (Set.countable_range (algebraMap K (AdeleRing (𝓞 K) K))).to_subtype

theorem setIntegral_adelicBox_comp_add_right {f : AdeleRing (𝓞 K) K → ℂ}
    (hf : ∀ (k : K) (x : AdeleRing (𝓞 K) K), f (algebraMap K (AdeleRing (𝓞 K) K) k + x) = f x)
    (x₀ : AdeleRing (𝓞 K) K) :
    ∫ x in adelicBox K, f (x + x₀) ∂(adelicAddHaar (𝓞 K) K)
      = ∫ x in adelicBox K, f x ∂(adelicAddHaar (𝓞 K) K) := by
  haveI := countable_principalSubgroup K
  have hB := isAddFundamentalDomain_adelicBox_adelicAddHaar K
  have hBt : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) (x₀ +ᵥ adelicBox K)
      (adelicAddHaar (𝓞 K) K) := hB.vadd_of_comm x₀
  have hf' : ∀ (g : AdeleRing.principalSubgroup (𝓞 K) K) (x : AdeleRing (𝓞 K) K),
      f (g +ᵥ x) = f x := by
    rintro ⟨_, k, rfl⟩ x
    exact hf k x
  have himg : (fun x => x + x₀) '' adelicBox K = x₀ +ᵥ adelicBox K := by
    ext y
    simp only [Set.mem_image, Set.mem_vadd_set, vadd_eq_add]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, add_comm _ _⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, add_comm _ _⟩
  have hmp := (measurePreserving_add_right (adelicAddHaar (𝓞 K) K) x₀).setIntegral_image_emb
    (measurableEmbedding_addRight x₀) f (adelicBox K)
  rw [himg] at hmp
  rw [← hmp]
  exact hBt.setIntegral_eq hB hf'

theorem constantTerm_cond_adelicBox_eq {G : Type*} [Group G] (u : AdeleRing (𝓞 K) K → G)
    (φ : G → ℂ) (g : G) :
    constantTerm ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) u φ g
      = ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹.toReal
          • ∫ x in adelicBox K, φ (u x * g) ∂(adelicAddHaar (𝓞 K) K) := by
  unfold constantTerm constantTermIntegrand
  rw [ProbabilityTheory.cond, integral_smul_measure]

theorem globalPoints_unipotentGL2 (k : K) :
    globalPoints (𝓞 K) K (unipotentGL2 k) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change algebraMap K (AdeleRing (𝓞 K) K) ((unipotentGL2 k : Matrix (Fin 2) (Fin 2) K) i j)
    = (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) : Matrix (Fin 2) (Fin 2) _) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem constantTerm_adelicBox_unipotentGL2_mul' {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ (k : K) (h : AdelicGL2 (𝓞 K) K), φ (globalPoints (𝓞 K) K (unipotentGL2 k) * h) = φ h)
    (x₀ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K) :
    constantTerm ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) (fun x => unipotentGL2 x) φ
        (unipotentGL2 x₀ * g)
      = constantTerm ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) (fun x => unipotentGL2 x) φ g := by
  rw [constantTerm_cond_adelicBox_eq, constantTerm_cond_adelicBox_eq]
  congr 1
  have hshift : ∀ x : AdeleRing (𝓞 K) K,
      φ (unipotentGL2 x * (unipotentGL2 x₀ * g)) = φ (unipotentGL2 (x + x₀) * g) := by
    intro x
    rw [unipotentGL2_add, mul_assoc]
  simp only [hshift]
  refine setIntegral_adelicBox_comp_add_right K (f := fun x => φ (unipotentGL2 x * g)) ?_ x₀
  intro k x
  show φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k + x) * g) = φ (unipotentGL2 x * g)
  rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hφ]

end FD

end M4aP3B.Rows

end

theorem M4aP3B.Rows.constantTerm_adelicBox_unipotentGL2_mul_impl (K : Type) [Field K] [NumberField K]
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K → ℂ}
    (hφ : ∀ (k : K) (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K),
      φ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers K) K
        (AutomorphicForm.unipotentGL2 k) * h) = φ h)
    (x₀ : NumberField.AdeleRing (NumberField.RingOfIntegers K) K)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K) :
    @AutomorphicForm.constantTerm _
        (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K) _ _
        (@ProbabilityTheory.cond _
          (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K)
          (NumberField.AdelicHaar.adelicAddHaar (NumberField.RingOfIntegers K) K)
          (NumberField.AdelicBox.adelicBox K))
        (fun x => AutomorphicForm.unipotentGL2 x) φ (AutomorphicForm.unipotentGL2 x₀ * g)
      = @AutomorphicForm.constantTerm _
          (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K) _ _
          (@ProbabilityTheory.cond _
            (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K)
            (NumberField.AdelicHaar.adelicAddHaar (NumberField.RingOfIntegers K) K)
            (NumberField.AdelicBox.adelicBox K))
          (fun x => AutomorphicForm.unipotentGL2 x) φ g :=
  M4aP3B.Rows.constantTerm_adelicBox_unipotentGL2_mul' K hφ x₀ g

#print axioms M4aP3B.Rows.constantTerm_adelicBox_unipotentGL2_mul_impl

theorem solution (K : Type) [Field K] [NumberField K]
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K → ℂ}
    (hφ : ∀ (k : K) (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K),
      φ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers K) K
        (AutomorphicForm.unipotentGL2 k) * h) = φ h)
    (x₀ : NumberField.AdeleRing (NumberField.RingOfIntegers K) K)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers K) K) :
    @AutomorphicForm.constantTerm _
        (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K) _ _
        (@ProbabilityTheory.cond _
          (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K)
          (NumberField.AdelicHaar.adelicAddHaar (NumberField.RingOfIntegers K) K)
          (NumberField.AdelicBox.adelicBox K))
        (fun x => AutomorphicForm.unipotentGL2 x) φ (AutomorphicForm.unipotentGL2 x₀ * g)
      = @AutomorphicForm.constantTerm _
          (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K) _ _
          (@ProbabilityTheory.cond _
            (NumberField.AdelicHaar.adeleBorel (NumberField.RingOfIntegers K) K)
            (NumberField.AdelicHaar.adelicAddHaar (NumberField.RingOfIntegers K) K)
            (NumberField.AdelicBox.adelicBox K))
          (fun x => AutomorphicForm.unipotentGL2 x) φ g := by
  apply M4aP3B.Rows.constantTerm_adelicBox_unipotentGL2_mul_impl <;> assumption

end S_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul
end P2MW
export P2MW.S_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul (solution)
