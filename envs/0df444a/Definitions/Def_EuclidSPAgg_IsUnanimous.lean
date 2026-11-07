-- Prove2me | Definitions.Def_EuclidSPAgg_IsUnanimous
-- name    : EuclidSPAgg_IsUnanimous
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:42.143865+00:00
-- url     : https://prove2.me/theorems/88a7ec3e-90ac-432b-8774-fc18df24c175
-- title:
--   Unanimity (Definition 1.2)
-- statement:
--   A mechanism $f$ is **unanimous** if $f(a,\dots,a)=a$ for every $a\in E$: when all agents report the same point, that point is selected.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Definition 1.2, p.3 (PDF p.5); Section 2.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_EuclidSPAgg_Mech
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- Unanimity, Definition 1.2 (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.3 (PDF p.5); Section 2.1, p.8 (PDF p.10)):
`f(a, …, a) = a` for every `a ∈ E`. -/
def IsUnanimous {n d : ℕ} (f : Mech n d) : Prop :=
  ∀ a : E d, f (fun _ => a) = a

end EuclidSPAgg


