-- Prove2me | Definitions.Def_BorelRobustMDP_weakStarTopology
-- name    : BorelRobustMDP_weakStarTopology
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:57.390214+00:00
-- url     : https://prove2.me/theorems/58dc828f-217d-4835-8d32-d48767889d85
-- title:
--   The weak* topology $\sigma(L^q,L^p)$ on a set of measures
-- statement:
--   For a set $S$ of measures, the weak* topology on $S$ is the coarsest topology making every map $Q\mapsto\int f\,dQ$, $f\in L^p(P)$, continuous. A subset $S$ of $\mathcal M^q(P)$ is **weak* closed** if it is closed in this topology on $\mathcal M^q(P)$.
--
--   The paper identifies $Q$ with its density $dQ/dP$ and takes the trace of $\sigma(L^q,L^p)$. Since $\int f\,dQ=\mathbb E[f\,dQ/dP]$ for $Q\in\mathcal M^q(P)$, this is the same topology.
--
--   **Formalization Note.** The definition uses induced maps and does not need the identification of $L^q$ with the dual of $L^p$. The set of densities of $\mathcal M^q(P)$ is itself weak* closed in $L^q(P)$ (test against indicators), so closedness in $\mathcal M^q(P)$ is the paper's closedness in $L^q(P)$.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, (2.2) and §2, p.4

import Mathlib
import Definitions.Def_BorelRobustMDP_Mq

open MeasureTheory Topology
open scoped ENNReal

namespace BorelRobustMDP

universe v

variable {Z : Type v} [MeasurableSpace Z]

/-- The weak* topology `σ(L^q, L^p)` on a set `S` of measures, viewed through their densities
(Bäuerle & Glauner, arXiv:2007.13103v1, (2.2) and p.4): the coarsest topology on `S` making every
map `Q ↦ ∫ f dQ`, `f ∈ L^p(P)`, continuous.

**Formalization Note.** For `Q ∈ 𝓜^q(P)` one has `∫ f dQ = E[f · dQ/dP]`, so these are exactly the
evaluation functionals of `L^p` on the densities: this is the trace of `σ(L^q, L^p)`, stated with
induced maps and without the Lp–Lq duality. The value does not depend on the representative of
the class `f`, since `Q ≪ P`. The topology is meant for `S ⊆ 𝓜^q(P)`. -/
@[reducible] noncomputable def weakStarTopology (P : Measure Z) (p : ℝ≥0∞) (S : Set (Measure Z)) : TopologicalSpace S :=
  ⨅ f : Lp ℝ p P,
    TopologicalSpace.induced (fun Q : S => ∫ z, (f : Z → ℝ) z ∂(Q : Measure Z)) inferInstance

/-- `S` is weak* closed (Bäuerle & Glauner, arXiv:2007.13103v1, Lemma 2.3, p.4).

**Formalization Note.** "Closed" is closedness in `weakStarTopology` on all of `𝓜^q(P)`. The set
`𝓜^q(P)` of densities is itself weak* closed in `L^q(P)` (test against indicators, which lie in
`L^p`), so this is the paper's closedness in `L^q(P)` for subsets of `𝓜^q(P)`. -/
def IsWeakStarClosed (P : Measure Z) (p q : ℝ≥0∞) (S : Set (Measure Z)) : Prop :=
  IsClosed[weakStarTopology P p (Mq P q)] {Q : Mq P q | (Q : Measure Z) ∈ S}

end BorelRobustMDP


