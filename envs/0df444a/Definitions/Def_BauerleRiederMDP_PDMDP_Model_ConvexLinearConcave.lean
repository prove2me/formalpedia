-- Prove2me | Definitions.Def_BauerleRiederMDP_PDMDP_Model_ConvexLinearConcave
-- name    : BauerleRiederMDP_PDMDP_Model_ConvexLinearConcave
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:19.556611+00:00
-- url     : https://prove2.me/theorems/0f5b90fc-17dd-413b-9e72-0d82fc5c8345
-- title:
--   Second alternative of Theorem 8.2.7: $U$ convex, $\mu$ linear in $u$, objective concave
-- statement:
--   The second alternative of Theorem 8.2.7 says that $U$ is convex, $\mu(x,u)$ is linear in $u$ and
--   $$
--   u\mapsto r(x,u)+\lambda\int J^{rel}_\infty(z)\,Q(dz|x,u)
--   $$
--   is concave on $U$.
--
--   **Formalization Note** The book does not name the vector space holding $U$; its proof integrates $u$ against $\alpha_t(du)$. Here $\iota$ embeds $U$ into a real topological vector space, with convex image, and "linear" is read as continuous and affine along convex combinations in $U$. That covers $\mu(x,u)=L_xu$ with $L_x$ continuous and linear, and in $\mathbb R^m$ continuity is automatic. Concavity is in $[-\infty,\infty)$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.2.7, p.253

import Mathlib
import Definitions.Def_BauerleRiederMDP_PDMDP_JumpModel_relaxedStage
import Definitions.Def_BauerleRiederMDP_PDMDP_Model

open MeasureTheory ProbabilityTheory
open MDPFinance.PDMDP (erealIntegral)

namespace BauerleRiederMDP.PDMDP

/-- The function `u ↦ r(x,u) + λ ∫ J^{rel}_∞(z) Q(dz|x,u)` of Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.2.7, p.253, PDF 264. -/
noncomputable def JumpModel.jumpObjective {E U : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [MeasurableSpace U] (M : JumpModel E U) (x : E) (u : U) : EReal :=
  ((M.r (x, u) : ℝ) : EReal) + (M.lam : EReal) * erealIntegral (M.Q (x, u)) M.JinfRelaxed

/-- The second alternative of Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 8.2.7, p.253, PDF 264: "`U` is convex, `μ(x,u)` is
linear in `u` and `u ↦ r(x,u) + λ ∫ J^{rel}_∞(z) Q(dz|x,u)` is concave on `U`".

**Formalization Note** The book does not name the vector space that holds `U`; the proof of the
theorem integrates `u` against `α_t(du)`. Here `ι` embeds `U` into a real topological vector space
`V`, with convex image. "Linear" is read as continuous and affine along convex combinations in
`U`: this covers `μ(x,u) = L_x u` with `L_x` continuous and linear, and in `V = ℝ^m` the continuity
is automatic. -/
structure Model.ConvexLinearConcave {d : ℕ} {E : Set (EuclideanSpace ℝ (Fin d))} {U V : Type*}
    [TopologicalSpace U] [MeasurableSpace U] [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (M : Model E U) (ι : U → V) : Prop where
  embedding : Topology.IsEmbedding ι
  convex : Convex ℝ (Set.range ι)
  drift_continuous : ∀ x, Continuous fun u => M.μ (x, u)
  drift_affine : ∀ x (u v w : U) (a c : ℝ), 0 ≤ a → 0 ≤ c → a + c = 1 →
    ι w = a • ι u + c • ι v → M.μ (x, w) = a • M.μ (x, u) + c • M.μ (x, v)
  concave : ∀ x (u v w : U) (a c : ℝ), 0 ≤ a → 0 ≤ c → a + c = 1 →
    ι w = a • ι u + c • ι v →
      (a : EReal) * M.toJumpModel.jumpObjective x u + (c : EReal) * M.toJumpModel.jumpObjective x v ≤
        M.toJumpModel.jumpObjective x w

end BauerleRiederMDP.PDMDP


