-- Prove2me | Definitions.Def_EuclidSPAgg_IsAnonymous
-- name    : EuclidSPAgg_IsAnonymous
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:36.332246+00:00
-- url     : https://prove2.me/theorems/d7ed0849-594e-414d-8d12-e8e7702cb7e1
-- title:
--   Anonymity (Definition 1.1)
-- statement:
--   A mechanism $f$ is **anonymous** if
--   $$
--   f(x_{\pi(1)},\dots,x_{\pi(n)})=f(x_1,\dots,x_n)
--   $$
--   for every permutation $\pi$ of the agents: the outcome depends on the reported locations but not on who reported them. A symmetric binary or ternary rule (Lemma 3.1, Definition 3.4, Theorem 4.1) is an anonymous mechanism with two or three agents.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Definition 1.1, p.2 (PDF p.4); Section 2.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_EuclidSPAgg_Mech
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- Anonymity, Definition 1.1 (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.2 (PDF p.4); Section 2.1, p.8 (PDF p.10)):
`f(x_{π(1)}, …, x_{π(n)}) = f(x₁, …, xₙ)` for every permutation `π` of the agents.

**Formalization Note** `x ∘ π` is the permuted profile `i ↦ x (π i)`. A "symmetric" binary or
ternary rule (Lemma 3.1, Definition 3.4, Theorem 4.1) is an anonymous 2- or 3-agent mechanism. -/
def IsAnonymous {n d : ℕ} (f : Mech n d) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (x : Fin n → E d), f (x ∘ π) = f x

end EuclidSPAgg


