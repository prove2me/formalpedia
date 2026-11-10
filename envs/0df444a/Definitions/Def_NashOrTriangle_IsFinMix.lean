-- Prove2me | Definitions.Def_NashOrTriangle_IsFinMix
-- name    : NashOrTriangle_IsFinMix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:26.994796+00:00
-- url     : https://prove2.me/theorems/ca0997c9-fda3-467c-9e03-41ed239f1572
-- title:
--   Finite rational mixture
-- statement:
--   A **finite rational mixture** over a set $X$ is a finitely supported probability distribution $p$ on $X$ with rational weights: $p(x) \ge 0$ for all $x$, and
--   $$
--   \sum_{x} p(x) = 1 .
--   $$
--   The paper requires all mixed strategies in queries to the best-response oracle and in outputs to be of this form.
--
--   **Formalization Note** $p$ is a finitely supported function `X →₀ ℚ`; the sum runs over its support.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Definition 1.1, p.3 (PDF p.4); §1.1, p.4 (PDF p.5)

import Mathlib

namespace NashOrTriangle

/-- `p` is a **finite rational mixture**: a finitely supported probability distribution with
rational weights.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Definition 1.1, printed p. 3 (PDF p. 4): "Mixed strategies in inputs and outputs are
finitely supported and have rational probabilities", and §1.1, printed p. 4 (PDF p. 5): "a
finite rational mixture q of known columns".

**Formalization Note** The finite support is the support of the `Finsupp`; the weights are
nonnegative rationals summing to `1`. -/
def IsFinMix {α : Type*} (p : α →₀ ℚ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ p.sum (fun _ w => w) = 1

end NashOrTriangle


