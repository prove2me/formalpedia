-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_Target
-- name    : OAI_Analysis_Cotype_Target
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:22:01.230995+00:00
-- url     : https://prove2.me/theorems/653060b2-1559-42ed-b09c-50156a0f301e
-- title:
--   Fixed-dimension cotype bounds and the forward target
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $E$ be a real normed space.
--
--   1. **Fixed cotype-2 bound.** For $m\in\mathbb N$ and $D\ge0$, every $x_1,\dots,x_m\in E$ satisfies
--   $$
--   \Bigl(\sum_i\|x_i\|^2\Bigr)^{1/2}\le D\,\Bigl\|\sum_i\varepsilon_ix_i\Bigr\|_{L_2} .
--   $$
--   2. **Forward target.** For a nontrivial Banach space $E$: if $E$ is K-convex, then $E$ and $E^*$ have finite cotype.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/Target.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/Target.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube

namespace OAI

noncomputable section
open scoped BigOperators
universe u
namespace Cotype

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

def FixedCotypeBound (m : ℕ) (D : ℝ) : Prop := 0 ≤ D ∧
  ∀ x : Fin m → E,
    Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ D * cubeL2 E (rademacherSum E x)

def ForwardTarget [CompleteSpace E] [Nontrivial E] : Prop :=
  KConvex E → FiniteCotype E ∧ FiniteCotype (E →L[ℝ] ℝ)

end Cotype

end

end OAI


