-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
-- name    : KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T04:59:32.918993+00:00
-- url     : https://prove2.me/theorems/f59321ed-31fb-44ff-92dd-678b8e08ea01
-- title:
--   Carré du champ definitions
-- statement:
--   For functions on a complete real inner-product space, `gamma f g x` is the pointwise carré du champ $\Gamma(f,g)(x)=\langle\nabla f(x),\nabla g(x)\rangle$. In finite dimension, `gammaTwo U f x` is the iterated carré du champ in the diffusion convention $\Gamma_2(f)=\frac12\mathcal L(\Gamma(f,f))-\Gamma(f,\mathcal Lf)$, where $\mathcal L$ is `weightedLaplacian` and the final pairing is interpreted geometrically through `gamma`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Gamma.lean#L27-L95 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Gamma`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gamma
variable [CompleteSpace E]
/-- The **carré du champ** `Γ(f, g)(x) = ⟪∇f(x), ∇g(x)⟫`, defined geometrically. -/
def gamma (f g : E → ℝ) (x : E) : ℝ := ⟪gradient f x, gradient g x⟫
variable [FiniteDimensional ℝ E]
/-- The **iterated carré du champ** in the diffusion convention,
`Γ₂(f) = ℒ(Γ(f, f)) / 2 - Γ(f, ℒf)`, with `Γ(f, ℒf) = ⟪∇f, ∇(ℒf)⟫` read geometrically. -/
def gammaTwo (U f : E → ℝ) (x : E) : ℝ :=
  weightedLaplacian U (fun y => gamma f f y) x / 2 - gamma f (weightedLaplacian U f) x
end Gamma
end BakryEmery
end Analysis
end FunctionalInequalities


