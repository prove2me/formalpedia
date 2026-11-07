-- Prove2me | Definitions.Def_EuclidSPAgg_HasBoundedInfluence
-- name    : EuclidSPAgg_HasBoundedInfluence
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:28.592904+00:00
-- url     : https://prove2.me/theorems/a74ede5a-b14e-4835-9fa9-a54e6b0bb3c2
-- title:
--   Bounded individual influence (Definition 1.5)
-- statement:
--   A mechanism has **bounded individual influence** if every unilateral menu $M_i(x_{-i})$ is a bounded subset of $E$: with the other reports fixed, one agent can induce only a bounded set of outcomes. The bound may depend on the fixed reports.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Definition 1.5, p.3 (PDF p.5); Section 2.4, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_EuclidSPAgg_menu
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- Bounded individual influence, Definition 1.5 (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.3 (PDF p.5); Section 2.4, p.11
(PDF p.13)): every unilateral menu `M_i(x₋ᵢ)` is bounded. -/
def HasBoundedInfluence {n d : ℕ} (f : Mech n d) : Prop :=
  ∀ (i : Fin n) (x : Fin n → E d), Bornology.IsBounded (menu f i x)

end EuclidSPAgg


