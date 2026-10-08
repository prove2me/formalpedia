-- Prove2me | Definitions.Def_DiaconisStroock_OddPaths_IotaTilde
-- name    : DiaconisStroock_OddPaths_IotaTilde
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:13.070991+00:00
-- url     : https://prove2.me/theorems/e059d86e-a00f-4411-a4ca-e9ee32841f6f
-- title:
--   Remark 1.3, p. 41 — odd paths σ_xy between all pairs and the quantity ι̃
-- statement:
--   Let $P$ be a transition matrix on a finite set $X$ with stationary distribution $\pi$ and $Q(x,y)=\pi(x)P(x,y)$. For each ordered pair $(x,y)\in X\times X$, including $x=y$, let $\sigma_{xy}$ be a path from $x$ to $y$ along edges with $Q>0$, with an odd number of edges and no directed edge traversed twice. Remark 1.3 sets
--
--   $$
--   \tilde\iota=\max_e\sum_{\sigma_{xy}\ni e}|\sigma_{xy}|_Q\,\pi(x)\pi(y),
--   $$
--
--   the maximum over directed edges $e$ with $Q(e)>0$, the sum over the ordered pairs whose path traverses $e$.
--
--   $\tilde\iota$ is the analogue of $\iota$ for paths joining every pair of points, and gives the variant bound $\beta_{\min}\ge-1+1/\tilde\iota$ of Remark 1.3.
--
--   **Formalization Note** The no-repetition rule is read for directed edges, as for $\iota$. The maximum is a real supremum over a finite index set, $0$ when the chain has no edge.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 41, Remark 1.3, https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_DiaconisStroock_OddPaths_Iota

namespace DiaconisStroock.OddPaths

open MarkovMixing

/-- `p` is an odd path from `x` to `y` (Remark 1.3, Diaconis and Stroock, Geometric bounds for
eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 41): a walk from `x` to `y` along
edges with `Q > 0`, with an odd number of edges, no directed edge traversed twice. -/
def IsOddPathBetween {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ) (π : V → ℝ)
    (x y : V) (p : List V) : Prop :=
  DiaconisStroock.Poincare.IsWalk P π x y p ∧ (DiaconisStroock.Poincare.pathEdges p).Nodup ∧ Odd (DiaconisStroock.Poincare.pathEdges p).length

/-- `ι̃ = max_e ∑_{σ_xy ∋ e} |σ_xy|_Q π(x) π(y)` of Remark 1.3 (p. 41), the maximum over directed
edges `e` with `Q(e) > 0`, the sum over all ordered pairs `(x, y)` (`x = y` included) whose path
`σ_xy` traverses `e`. -/
noncomputable def iotaTilde {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ)
    (π : V → ℝ) (S : V → V → List V) : ℝ :=
  ⨆ e : {e : V × V // 0 < edgeMeasure P π e.1 e.2},
    ∑ x, ∑ y, if e.1 ∈ DiaconisStroock.Poincare.pathEdges (S x y) then DiaconisStroock.Poincare.qLength P π (S x y) * π x * π y else 0

end DiaconisStroock.OddPaths


