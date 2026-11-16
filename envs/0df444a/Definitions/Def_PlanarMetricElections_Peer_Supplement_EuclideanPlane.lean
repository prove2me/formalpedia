-- Prove2me | Definitions.Def_PlanarMetricElections_Peer_Supplement_EuclideanPlane
-- name    : PlanarMetricElections_Peer_Supplement_EuclideanPlane
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:42:06.030422+00:00
-- url     : https://prove2.me/theorems/135f5603-4f0f-468a-9528-710a1edbb19e
-- title:
--   Euclidean distance on the plane and the no-equidistant-voter convention
-- statement:
--   On the plane $\mathbb R^2$ (the published type `Plane` $=\mathbb R\times\mathbb R$) the Euclidean distance is
--
--   $$d_2(x,y)=\sqrt{(x_1-y_1)^2+(x_2-y_2)^2}.$$
--
--   For a distance $d$, finite voters $V$ and finite candidates $C$, the election has **no equidistant voter** if no voter $v\in V$ satisfies $d(v,a)=d(v,b)$ for two distinct candidates $a,b\in C$. This is the paper's standing convention for finite-candidate metric elections (Section 2), which makes each voter's preference over $C$ a strict total order.
--
--   **Formalization Note** The distance is written in coordinates because Mathlib's default distance on $\mathbb R\times\mathbb R$ is the sup distance $\ell_\infty$, not $\ell_2$.
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Section 2 (Metric elections; ℓ2 norm), p. 3 (PDF p. 4)

import Definitions.Def_PlanarMetricElections_Peer_Geometry

set_option autoImplicit false
noncomputable section

namespace PlanarMetricElections.Peer.Supplement

/-- The Euclidean (ℓ₂) distance on `Plane = ℝ × ℝ`, written in coordinates.
(Mathlib's default `dist` on `ℝ × ℝ` is the sup distance, so it is not used.) -/
def dTwo (x y : Plane) : ℝ := Real.sqrt ((x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)

/-- No voter of `V` is equidistant (for `d`) from two distinct candidates of `C`:
the paper's standing convention for finite-candidate metric elections. -/
def NoEquidistantVoter (d : Plane → Plane → ℝ) (V C : Finset Plane) : Prop :=
  ∀ v ∈ V, ∀ a ∈ C, ∀ b ∈ C, a ≠ b → d v a ≠ d v b

end PlanarMetricElections.Peer.Supplement


