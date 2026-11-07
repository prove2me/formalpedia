-- Prove2me | Definitions.Def_EuclidSPAgg_IsStrategyproof
-- name    : EuclidSPAgg_IsStrategyproof
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:15.52995+00:00
-- url     : https://prove2.me/theorems/e9e42070-93f1-49e4-b578-69f86e800273
-- title:
--   Strategyproofness, display (2.1)
-- statement:
--   A mechanism $f:E^n\to E$ is **strategyproof** if no agent can move the outcome closer to its true ideal point by misreporting:
--   $$
--   \|a-f(a,x_{-i})\|\le\|a-f(b,x_{-i})\|\qquad(i\in[n],\ a,b\in E,\ x_{-i}\in E^{n-1}).
--   $$
--   Here $(a,x_{-i})$ is the profile in which agent $i$ reports $a$ and the others report $x_{-i}$.
--
--   For a ternary rule $H:E^3\to E$ this is the paper's notion "strategyproof in each argument".
--
--   **Formalization Note** $(a,x_{-i})$ is `Function.update x i a`; the value of `x` at `i` is overwritten, so `x` ranges over all reports of the other agents.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, display (2.1), p.8 (PDF p.10)

import Mathlib
import Definitions.Def_EuclidSPAgg_Mech
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- Strategyproofness, display (2.1) (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.8 (PDF p.10)):
`‖a − f(a, x₋ᵢ)‖ ≤ ‖a − f(b, x₋ᵢ)‖` for every agent `i`, every `a, b ∈ E` and every profile of
the other agents.

**Formalization Note** `Function.update x i a` is the profile `(a, x₋ᵢ)`; the value `x i` is
overwritten, so `x` ranges over all `x₋ᵢ`. For a ternary rule `H : E³ → E` this is the paper's
"strategyproof in each argument" (Lemma 3.1, Definition 3.4, Theorem 4.1). -/
def IsStrategyproof {n d : ℕ} (f : Mech n d) : Prop :=
  ∀ (i : Fin n) (x : Fin n → E d) (a b : E d),
    ‖a - f (Function.update x i a)‖ ≤ ‖a - f (Function.update x i b)‖

end EuclidSPAgg


