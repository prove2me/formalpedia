-- Prove2me | Definitions.Def_SweepingDesing_IsPACOrbit
-- name    : SweepingDesing_IsPACOrbit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:16:35.359481+00:00
-- url     : https://prove2.me/theorems/0edd1317-6cdd-4382-b073-8927d8764a81
-- title:
--   §2.1 — piecewise absolutely continuous orbits $\mathcal{PAC}(S,I)$
-- statement:
--   For a set-valued map $S:\mathbb R\rightrightarrows\mathbb R^n$ and a nonempty interval $I$, $\mathcal{PAC}(S,I)$ is the set of piecewise absolutely continuous curves $\gamma:I\to\mathbb R^n$ that satisfy the sweeping-process relations
--
--   $$
--   -\dot\gamma(t)\in N_{S(t)}(\gamma(t))\ \text{for almost every }t\in I,\qquad \gamma(t)\in S(t)\ \text{for every }t\in I.
--   $$
--
--   Since the jumps lie in a countable set, the differential inclusion still makes sense almost everywhere.
--
--   **Formalization Note** As for absolutely continuous orbits, with `IsPAC` in place of `IsLocallyAC`.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §2.1, p.4

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_SweepingDesing_IsPAC
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §2.1, p.4, notation `𝒫𝒜𝒞(S, I)`: `γ` is a piecewise absolutely continuous orbit of
the sweeping process defined by `S` on the nonempty interval `I`: `γ` is piecewise absolutely
continuous on `I` (`IsPAC`), `γ(t) ∈ S(t)` for every `t ∈ I`, and `-γ̇(t) ∈ N_{S(t)}(γ(t))` for
almost every `t ∈ I` (display (3)).

**Formalization Note** As for `IsACOrbit`; the jump points form a countable, hence null, set. -/
def IsPACOrbit {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (γ : ℝ → EuclideanSpace ℝ (Fin n))
    (I : Set ℝ) : Prop :=
  I.Nonempty ∧ I.OrdConnected ∧ IsPAC γ I ∧ (∀ t ∈ I, γ t ∈ S t) ∧
    ∀ᵐ t, t ∈ I → ∃ v : EuclideanSpace ℝ (Fin n), HasDerivAt γ v t ∧
      -v ∈ StrictCQ.CAKKT.limNormal (S t) (γ t)

end SweepingDesing


