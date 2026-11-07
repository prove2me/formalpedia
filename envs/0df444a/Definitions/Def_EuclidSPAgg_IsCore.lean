-- Prove2me | Definitions.Def_EuclidSPAgg_IsCore
-- name    : EuclidSPAgg_IsCore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:46.07379+00:00
-- url     : https://prove2.me/theorems/5748b087-f464-49ce-acd9-fb81a644cb48
-- title:
--   Core of a ternary rule (Definition 3.4)
-- statement:
--   Let $H:E^3\to E$ be a ternary rule. A nonempty closed convex set $C\subseteq E$ is a **core** of $H$ if
--   $$
--   H(a,P_Cc,c)=P_Cc\qquad(a,c\in E),
--   $$
--   where $P_Cc$ is the nearest point of $C$ to $c$. In words, when one report is the projection of another onto $C$, the outcome is that projection, whatever the third report.
--
--   **Formalization Note** $P_Cc$ is expressed through the published nearest-point set `SuperPolyak.nearestPoints`; for a nonempty closed convex $C$ it has exactly one element. Definition 3.4 is stated for $H$ symmetric, continuous and strategyproof in each argument; those properties are hypotheses of the theorems that use cores.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Definition 3.4, display (3.3), p.13 (PDF p.15)

import Mathlib
import Definitions.Def_EuclidSPAgg_Mech
import Definitions.Def_SuperPolyak_solutionSet
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- A core of a ternary rule `H : E³ → E`, Definition 3.4 (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.13 (PDF p.15)): a nonempty
closed convex set `C ⊆ E` with `H(a, P_C c, c) = P_C c` for all `a, c ∈ E` (display (3.3)).

**Formalization Note** `P_C c` is the nearest point of `C` to `c`, a member of the published
nearest-point set `SuperPolyak.nearestPoints C c`; for nonempty closed convex `C` that set has
exactly one element. The argument order `(a, P_C c, c)` is kept. Definition 3.4's standing
hypotheses on `H` (symmetric, continuous, strategyproof in each argument) are hypotheses of the
theorems that use cores. -/
def IsCore {d : ℕ} (H : Mech 3 d) (C : Set (E d)) : Prop :=
  C.Nonempty ∧ IsClosed C ∧ Convex ℝ C ∧
    ∀ (a c p : E d), p ∈ SuperPolyak.nearestPoints C c → H ![a, p, c] = p

end EuclidSPAgg


