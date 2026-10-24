-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
-- name    : KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:13:50.525186+00:00
-- url     : https://prove2.me/theorems/aef5d5f7-6254-41cf-9df6-698992b17f31
-- title:
--   Exponential limits for Yosida approximations
-- statement:
--   `yosida_cauchy_on_adjointComp_domain` states that, for $v\in D(T^\dagger T)$, the family $L_sv$ is Cauchy as $s\downarrow0$. For a closed densely defined $T$, `exists_limit_exp_neg_smul_yosida` then states that for every $f\in H_0$ and $t\ge0$ there exists $g\in H_0$ such that $\exp(-tL_s)f\to g$ as $s\downarrow0$. The limit is asserted only as an existence statement and is not named as a semigroup here.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Limit.lean#L35-L68 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Yosida.Limit`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
/-- On `D(T†T)` the Yosida approximations `L_s f` are Cauchy as `s ↓ 0`: they converge to
`T†T f` (`Y5`). -/
theorem yosida_cauchy_on_adjointComp_domain (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (v : H₀) (hv : v ∈ ((adjointComp T).domain : Set H₀))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {s r : ℝ} (hs : 0 < s) (hr : 0 < r), s < δ → r < δ →
      ‖yosida T hT hs v - yosida T hT hr v‖ < ε := by
  obtain ⟨δ, hδ, h⟩ :=
    exists_delta_norm_yosida_sub_adjointComp_lt T hT hd ⟨v, hv⟩ (half_pos hε)
  refine ⟨δ, hδ, fun {s r} hs hr hsδ hrδ => ?_⟩
  have h1 : ‖yosida T hT hs v - adjointComp T ⟨v, hv⟩‖ < ε / 2 := h hs hsδ
  have h2 : ‖yosida T hT hr v - adjointComp T ⟨v, hv⟩‖ < ε / 2 := h hr hrδ
  calc ‖yosida T hT hs v - yosida T hT hr v‖
      = ‖(yosida T hT hs v - adjointComp T ⟨v, hv⟩)
          - (yosida T hT hr v - adjointComp T ⟨v, hv⟩)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ ‖yosida T hT hs v - adjointComp T ⟨v, hv⟩‖
          + ‖yosida T hT hr v - adjointComp T ⟨v, hv⟩‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := add_halves ε
/-- **the adjoint-product identification for the Yosida approximation** (`Y8`). For `T` closed and densely defined, every
`t ≥ 0` and every `f : H₀`, the vectors `exp (-t • L_s) f` converge as `s ↓ 0`, in the `ε`–`δ`
sense forced by the proof argument `0 < s` carried by `L_s`. -/
theorem exists_limit_exp_neg_smul_yosida (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : H₀) {t : ℝ} (ht : 0 ≤ t) :
    ∃ g : H₀, ∀ {ε : ℝ}, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ {s : ℝ} (hs : 0 < s), s < δ → ‖NormedSpace.exp (-t • yosida T hT hs) f - g‖ < ε := by
  obtain ⟨g, hg⟩ := exists_limit_exp_neg_smul (fun s hs => yosida T hT hs)
    (fun s hs v => yosida_nonneg T hT hs v) (fun s r hs hr => yosida_comp_comm T hT hs hr)
    ((adjointComp T).domain : Set H₀) (dense_adjointComp_domain T hT hd)
    (fun v hv ε hε => yosida_cauchy_on_adjointComp_domain T hT hd v hv hε) f ht
  refine ⟨g, fun {ε} hε => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hg ε hε
  exact ⟨δ, hδ, fun {s} hs hsδ => h s hs hsδ⟩
end Semigroup
end Analysis
end FunctionalInequalities


