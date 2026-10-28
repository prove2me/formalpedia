-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
-- name    : KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:14:45.521907+00:00
-- url     : https://prove2.me/theorems/7707da62-8003-4b5c-8964-af18be8f9082
-- title:
--   Naming the strong Yosida exponential limit
-- statement:
--   `Generated.apply T hT hd t f` chooses a limit of $\exp(-tL_s)f$ for $t\ge0$, using the existence result for the Yosida exponentials, and returns $f$ itself when $t<0$. `Generated.yosida_limit` states the corresponding $\varepsilon$–$\delta$ convergence for every $t\ge0$ and $f\in H_0$. No linearity, contraction, semigroup law, or generator identity is included in this bundle.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Semigroup.Yosida.Limit
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def apply (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))
--       (t : ℝ) (f : H₀) : H₀ :=
--     if ht : 0 ≤ t then Classical.choose (exists_limit_exp_neg_smul_yosida T hT hd f ht) else f
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Semigroup/Yosida/Limit`](https://prove2.me/theorems/4470bc63-b548-404f-94f9-ce9afe299423).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Basic.lean) · `FunctionalInequalities.Analysis.Semigroup.Generated.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Basic.lean#L30-L43 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Generated.Basic`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Yosida_Limit

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


