-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_Form_Dirichlet
-- name    : KLSModular_FunctionalInequalities_Energy_Form_Dirichlet
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:12:12.232443+00:00
-- url     : https://prove2.me/theorems/0025f099-fed1-4255-868b-7850dd566303
-- title:
--   Normal contractions for Dirichlet-form structures
-- statement:
--   `Energy.NormalContraction` is a structure consisting of a function $\varphi:\mathbb R\to\mathbb R$, a Lipschitz bound `LipschitzWith 1 φ`, and the normalization $\varphi(0)=0$. Its coercion lets such a contraction be used as a real-valued function. This bundle defines the contraction object only; it does not state a Dirichlet form or a Markov inequality.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.Form.ClosedQuadratic
--   import Mathlib.MeasureTheory.Function.LpSpace.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure NormalContraction where
--     /-- The underlying real function. -/
--     toFun : ℝ → ℝ
--     /-- The contraction estimate. -/
--     lipschitz : LipschitzWith 1 toFun
--     /-- Normalization at zero. -/
--     map_zero : toFun 0 = 0
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/Form/ClosedQuadratic`](https://prove2.me/theorems/8c7616b5-8863-420d-8e08-678985cac4e9).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Form/Dirichlet.lean) · `FunctionalInequalities.Energy.Form.Dirichlet` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Form/Dirichlet.lean#L19-L31 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Form.Dirichlet`, definition bundle `KLSModular_FunctionalInequalities_Energy_Form_Dirichlet`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Form_ClosedQuadratic
import Mathlib.MeasureTheory.Function.LpSpace.Basic

noncomputable section
open MeasureTheory
namespace FunctionalInequalities
namespace Energy
/-- A normal contraction of the real line: it fixes zero and has Lipschitz constant at most one. -/
structure NormalContraction where
  /-- The underlying real function. -/
  toFun : ℝ → ℝ
  /-- The contraction estimate. -/
  lipschitz : LipschitzWith 1 toFun
  /-- Normalization at zero. -/
  map_zero : toFun 0 = 0
namespace NormalContraction
instance : CoeFun NormalContraction fun _ ↦ ℝ → ℝ :=
  ⟨NormalContraction.toFun⟩
end NormalContraction
end Energy
end FunctionalInequalities


