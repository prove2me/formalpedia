-- Prove2me | Definitions.Def_SweepingDesing_IsACOrbit
-- name    : SweepingDesing_IsACOrbit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:51.948+00:00
-- url     : https://prove2.me/theorems/b962b204-7686-4768-a556-dd7fa33ecb3f
-- title:
--   Definition 2, (3) — absolutely continuous orbits $\mathcal{AC}(S,I)$
-- statement:
--   Throughout, $S:\mathbb R\rightrightarrows\mathbb R^n$ is a set-valued map with graph $\mathcal S=\operatorname{gph}S=\{(t,x)\in\mathbb R\times\mathbb R^n: x\in S(t)\}$, and $N_C$ denotes the limiting (Mordukhovich) normal cone of §2: the outer limit of Fréchet normal cones $\hat N_C(y)$ as $y\to x$ within $C$.
--
--   Let $I$ be a nonempty interval. An absolutely continuous curve $\gamma:I\to\mathbb R^n$ is an **orbit** of the sweeping process defined by $S$ if
--
--   $$
--   \begin{cases}-\dot\gamma(t)\in N_{S(t)}(\gamma(t)) & \text{for almost every }t\in I,\\ \gamma(t)\in S(t) & \text{for every }t\in I.\end{cases}
--   $$
--
--   $\mathcal{AC}(S,I)$ denotes the set of these orbits. The moving set pushes the point along its inner normals, and the point stays at rest while it is in the interior of $S(t)$.
--
--   **Formalization Note** Absolute continuity on $I$ is read on compact subintervals; the normal cone is the published `StrictCQ.CAKKT.limNormal` on $\mathbb R^n$.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Definition 2, display (3), p.4

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_SweepingDesing_IsLocallyAC
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Definition 2, display (3), p.4, and the notation `𝒜𝒞(S, I)`: `γ` is an absolutely
continuous orbit of the sweeping process defined by `S` on the nonempty interval `I`:
`-γ̇(t) ∈ N_{S(t)}(γ(t))` for almost every `t ∈ I` and `γ(t) ∈ S(t)` for every `t ∈ I`.

**Formalization Note** `N_{S(t)}` is the limiting normal cone of §2, p.4 (published
`StrictCQ.CAKKT.limNormal`). Absolute continuity on `I` is read as on every compact subinterval
(`IsLocallyAC`). `I ⊂ dom(S)` follows from `γ(t) ∈ S(t)`. -/
def IsACOrbit {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (γ : ℝ → EuclideanSpace ℝ (Fin n))
    (I : Set ℝ) : Prop :=
  I.Nonempty ∧ I.OrdConnected ∧ IsLocallyAC γ I ∧ (∀ t ∈ I, γ t ∈ S t) ∧
    ∀ᵐ t, t ∈ I → ∃ v : EuclideanSpace ℝ (Fin n), HasDerivAt γ v t ∧
      -v ∈ StrictCQ.CAKKT.limNormal (S t) (γ t)

end SweepingDesing


