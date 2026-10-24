-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
-- name    : KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:14:24.03475+00:00
-- url     : https://prove2.me/theorems/64db1f63-57c6-4ce8-a7a9-4ba2defef6dd
-- title:
--   Naming the strong Yosida exponential limit
-- statement:
--   `Generated.apply T hT hd t f` chooses a limit of $\exp(-tL_s)f$ for $t\ge0$, using the existence result for the Yosida exponentials, and returns $f$ itself when $t<0$. `Generated.yosida_limit` states the corresponding $\varepsilon$–$\delta$ convergence for every $t\ge0$ and $f\in H_0$. No linearity, contraction, semigroup law, or generator identity is included in this bundle.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Basic.lean#L30-L43 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Basic`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Semigroup_Generated_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_AdjointComp
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Limit
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_VonNeumann
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Approximation
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Laws
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
namespace FunctionalInequalities
namespace Analysis
namespace Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
namespace Generated
/-- `P_t f`: the strong limit of `exp (-t • L_s) f` as `s ↓ 0` for `t ≥ 0` (chosen from the adjoint-product identification), and
`f` for `t < 0`. Formally `exp (-t T†T) f`. -/
def apply (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
    (t : ℝ) (f : H₀) : H₀ :=
  if ht : 0 ≤ t then Classical.choose (exists_limit_exp_neg_smul_yosida T hT hd f ht) else f
/-- The defining property of `P_t f` for `t ≥ 0`: `exp (-t • L_s) f → P_t f` as `s ↓ 0`. -/
theorem yosida_limit (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
    {t : ℝ} (ht : 0 ≤ t) (f : H₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ →
      ‖NormedSpace.exp (-t • yosida T hT hs) f - Generated.apply T hT hd t f‖ < ε := by
  unfold Generated.apply
  rw [dif_pos ht]
  exact Classical.choose_spec (exists_limit_exp_neg_smul_yosida T hT hd f ht) hε
end Generated
end Semigroup
end Analysis
end FunctionalInequalities


