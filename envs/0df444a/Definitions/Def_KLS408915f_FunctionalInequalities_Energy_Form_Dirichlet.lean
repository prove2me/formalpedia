-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Dirichlet
-- name    : KLS408915f_FunctionalInequalities_Energy_Form_Dirichlet
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:20:39.783136+00:00
-- url     : https://prove2.me/theorems/eee785a9-ec5a-4723-92b3-ca7b12a34d3c
-- title:
--   Normal contractions for Dirichlet-form structures
-- statement:
--   `Energy.NormalContraction` is a structure consisting of a function $\varphi:\mathbb R\to\mathbb R$, a Lipschitz bound `LipschitzWith 1 φ`, and the normalization $\varphi(0)=0$. Its coercion lets such a contraction be used as a real-valued function. This bundle defines the contraction object only; it does not state a Dirichlet form or a Markov inequality.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Form/Dirichlet.lean#L19-L31 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Form.Dirichlet`, definition bundle `KLS408915f_FunctionalInequalities_Energy_Form_Dirichlet`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Semicontinuity.Basic

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


