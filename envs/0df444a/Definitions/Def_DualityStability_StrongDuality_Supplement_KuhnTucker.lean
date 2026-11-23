-- Prove2me | Definitions.Def_DualityStability_StrongDuality_Supplement_KuhnTucker
-- name    : DualityStability_StrongDuality_Supplement_KuhnTucker
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:43:52.895903+00:00
-- url     : https://prove2.me/theorems/45ab15b0-8009-4757-9000-3e03adc5af4a
-- title:
--   Kuhn–Tucker function and its saddle-points (9.1), p. 185
-- statement:
--   In the standing setting of §3, the **Kuhn–Tucker function** of (P) and (P\*) is the finite-valued function on $C\times D^*$
--
--   $$
--   K(x,y^*)=f(x)+g^*(y^*)-\langle Ax,y^*\rangle .
--   $$
--
--   A pair $(\bar x,\bar y^*)$ is a **saddle-point** of $K$ if $\bar x\in C$, $\bar y^*\in D^*$ and
--
--   $$
--   K(\bar x,\bar y^*)=\min_{x\in C}K(x,\bar y^*)=\max_{y^*\in D^*}K(\bar x,y^*),
--   $$
--
--   and the real number $K(\bar x,\bar y^*)$ is then the **minimax** of $K$.
--
--   **Formalization Note** $K$ is written with `EReal` values on all of $E\times F^*$, but it is finite on $C\times D^*$ and the saddle-point condition only evaluates it there: both quantifiers range over $C$ and $D^*$ only.
-- source:
--   Rockafellar, Duality and Stability in Extremum Problems Involving Convex Functions, Pacific J. Math. 21 (1967), p. 185, §9, (9.1)

import Definitions.Def_DualityStability_StrongDuality_Supplement_EffectiveDomains

namespace DualityStability.StrongDuality.Supplement

open DualityStability.StrongDuality

variable {E E' F F' : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

/-- The Kuhn–Tucker function of §9, p. 185: `K(x, y*) = f(x) + g*(y*) - ⟨Ax, y*⟩`.
The paper defines it on `C × D*`, where it is finite; it is only ever evaluated there. -/
noncomputable def kuhnTucker (p : Program E E' F F') (x : E) (y' : F') : EReal :=
  p.f x + p.gstar y' - (p.fPair.pair (p.A x) y' : EReal)

/-- `(x̄, ȳ*)` is a saddle-point of `K` (9.1), p. 185: `x̄ ∈ C`, `ȳ* ∈ D*`,
`K(x̄, ȳ*) = min_{x ∈ C} K(x, ȳ*) = max_{y* ∈ D*} K(x̄, y*)`. -/
def IsSaddlePoint (p : Program E E' F F') (xb : E) (yb : F') : Prop :=
  xb ∈ effDomF p ∧ yb ∈ effDomGstar p ∧
    (∀ x ∈ effDomF p, kuhnTucker p xb yb ≤ kuhnTucker p x yb) ∧
    (∀ y' ∈ effDomGstar p, kuhnTucker p xb y' ≤ kuhnTucker p xb yb)

end DualityStability.StrongDuality.Supplement


