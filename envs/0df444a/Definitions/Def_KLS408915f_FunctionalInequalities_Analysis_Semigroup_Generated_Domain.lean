-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Domain
-- name    : KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Domain
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:17:18.729738+00:00
-- url     : https://prove2.me/theorems/65056960-a3d4-43ae-a728-7be0c3c7ff20
-- title:
--   Invariance and characterization of the generator domain
-- statement:
--   `mem_domain_of_generator_limit` states that a right derivative limit of $P_hy$ identifies $y$ as an element of $D(T^\dagger T)$ and identifies the operator value. For $f\in D(T^\dagger T)$ and $t\ge0$, `preserves_domain` states that $P_tf$ remains in this domain, and `generator_comm` states $T^\dagger T(P_tf)=P_t(T^\dagger Tf)$. `generator_limit_apply` records the corresponding transported right-derivative estimate.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Domain.lean#L15-L98 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Domain`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Domain`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Generator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace LinearPMap
namespace FunctionalInequalities
namespace Analysis
namespace Semigroup
namespace Generated
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
/-- The right generator limit implies domain membership and `Ay = -z`. -/
theorem mem_domain_of_generator_limit (y z : H₀)
    (hz : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ‖h⁻¹ • (apply T hT hd h y - y) - z‖ < ε) :
    ∃ hy : y ∈ (adjointComp T).domain, adjointComp T ⟨y, hy⟩ = -z := by
  have hi : ∀ x : (adjointComp T).domain, ⟪-z, (x : H₀)⟫ = ⟪y, adjointComp T x⟫ := by
    intro x
    have key : ∀ ε : ℝ, 0 < ε →
        |⟪z, (x : H₀)⟫ + ⟪y, adjointComp T x⟫| ≤ ε * (‖(x : H₀)‖ + ‖y‖) := by
      intro ε hε
      obtain ⟨δ₁, hδ₁, h₁⟩ := hz ε hε
      obtain ⟨δ₂, hδ₂, h₂⟩ :=
        generator_limit T hT hd x hε
      let h := min δ₁ δ₂ / 2
      have hp : 0 < h := by dsimp [h]; positivity
      have hm : h < min δ₁ δ₂ := by dsimp [h]; have := lt_min hδ₁ hδ₂; linarith
      have e₁ := h₁ h hp (lt_of_lt_of_le hm (min_le_left _ _))
      have e₂ := h₂ h hp (lt_of_lt_of_le hm (min_le_right _ _))
      have heq : ⟪h⁻¹ • (apply T hT hd h y - y), (x : H₀)⟫ =
          ⟪y, h⁻¹ • (apply T hT hd h (x : H₀) - (x : H₀))⟫ := by
        simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right,
          symmetric T hT hd hp.le]
      have hdec : ⟪z, (x : H₀)⟫ + ⟪y, adjointComp T x⟫ =
          -⟪h⁻¹ • (apply T hT hd h y - y) - z, (x : H₀)⟫ +
          ⟪y, h⁻¹ • (apply T hT hd h (x : H₀) - (x : H₀)) + adjointComp T x⟫ := by
        rw [inner_sub_left, inner_add_right, heq]; ring
      have b₁ := abs_real_inner_le_norm
        (h⁻¹ • (apply T hT hd h y - y) - z) (x : H₀)
      have b₂ := abs_real_inner_le_norm y
        (h⁻¹ • (apply T hT hd h (x : H₀) - (x : H₀)) + adjointComp T x)
      have m₁ := mul_le_mul_of_nonneg_right e₁.le (norm_nonneg (x : H₀))
      have m₂ := mul_le_mul_of_nonneg_left e₂.le (norm_nonneg y)
      have ha := abs_add_le
        (-⟪h⁻¹ • (apply T hT hd h y - y) - z, (x : H₀)⟫)
        (⟪y, h⁻¹ • (apply T hT hd h (x : H₀) - (x : H₀)) + adjointComp T x⟫)
      rw [abs_neg] at ha
      rw [hdec]
      nlinarith
    have he := abs_eq_zero.mp (eq_zero_of_forall_le_mul (abs_nonneg _) key)
    rw [inner_neg_left]
    linarith
  have hy := LinearPMap.mem_adjoint_domain_of_exists (T := adjointComp T) y ⟨-z, hi⟩
  have hv := LinearPMap.adjoint_apply_eq (dense_adjointComp_domain T hT hd) ⟨y, hy⟩ hi
  have hself := LinearPMap.isSelfAdjoint_def.mp (isSelfAdjoint_adjointComp T hT hd)
  revert hy hv
  rw [hself]
  exact fun hy hv => ⟨hy, hv⟩
/-- Transport the right generator limit along the contraction semigroup. -/
theorem generator_limit_apply (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ‖h⁻¹ • (apply T hT hd h (apply T hT hd t f) -
        apply T hT hd t f) + apply T hT hd t (adjointComp T f)‖ < ε := by
  obtain ⟨δ, hδ, he⟩ :=
    generator_limit T hT hd f hε
  refine ⟨δ, hδ, fun h hh hhδ => ?_⟩
  have hc : apply T hT hd h (apply T hT hd t f) =
      apply T hT hd t (apply T hT hd h f) := by
    rw [← add_time T hT hd hh.le ht, add_comm h t,
      add_time T hT hd ht hh.le]
  rw [hc, ← map_sub T hT hd ht,
    ← map_smul T hT hd ht, ← map_add T hT hd ht]
  exact lt_of_le_of_lt (norm_apply_le T hT hd ht _) (he h hh hhδ)
/-- `D(T†T)` is invariant at every nonnegative time. -/
theorem preserves_domain (f : (adjointComp T).domain)
    {t : ℝ} (ht : 0 ≤ t) : apply T hT hd t f ∈ (adjointComp T).domain := by
  apply (mem_domain_of_generator_limit T hT hd
    (apply T hT hd t f) (-apply T hT hd t (adjointComp T f)) ?_).choose
  intro ε hε
  simpa only [sub_neg_eq_add] using generator_limit_apply T hT hd f ht hε
/-- The nonnegative operator commutes with the semigroup on its domain. -/
theorem generator_comm (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t) :
    adjointComp T ⟨apply T hT hd t f,
      preserves_domain T hT hd f ht⟩ =
      apply T hT hd t (adjointComp T f) := by
  obtain ⟨hy, he⟩ := mem_domain_of_generator_limit T hT hd
    (apply T hT hd t f) (-apply T hT hd t (adjointComp T f))
    (fun ε hε => by simpa only [sub_neg_eq_add] using
      generator_limit_apply T hT hd f ht hε)
  simpa only [neg_neg] using he
end Generated
end Semigroup
end Analysis
end FunctionalInequalities


