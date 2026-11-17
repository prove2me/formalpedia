-- Prove2me | Definitions.Def_SharpConsist_Supplement_IsWeightedCoverage
-- name    : SharpConsist_Supplement_IsWeightedCoverage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:21:19.234465+00:00
-- url     : https://prove2.me/theorems/14af20b6-df23-42c3-833a-5081c9e8d3ff
-- title:
--   Nonnegative weighted coverage function
-- statement:
--   A set function $f$ on a finite ground set $V$ is a **nonnegative weighted coverage function** if there are a finite feature set $U$, nonnegative weights $w_a$ $(a\in U)$ and covering sets $C_a\subseteq V$ with
--   $$f(S)=\sum_{a\in U} w_a\,\mathbf 1\{S\cap C_a\neq\emptyset\}\qquad(S\subseteq V).$$
--   Such functions are normalized, monotone and submodular. In Theorem 7.1 only the existence of the representation is promised: the algorithm sees values of $f$, never $U$, $w$ or $C$.
--
--   **Formalization Note** The feature set is `Fin m`.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §2.1, p.4

import Mathlib

namespace SharpConsist.Supplement

/-- **Nonnegative weighted coverage function.** Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §2.1, p.4: "A weighted coverage
function has the form `f(S) = Σ_{a∈U} w_a 1{S ∩ C_a ≠ ∅}` for a finite feature set `U`, nonnegative
weights `w_a`, and covering sets `C_a ⊆ V`."

**Formalization Note.** The finite feature set is `Fin m` (any finite set is in bijection with one).
The predicate only asserts that such a representation exists; an algorithm never receives it. -/
def IsWeightedCoverage {V : Type} [Fintype V] [DecidableEq V] (f : Finset V → ℝ) : Prop :=
  ∃ (m : ℕ) (w : Fin m → ℝ) (C : Fin m → Finset V), (∀ a, 0 ≤ w a) ∧
    ∀ S : Finset V, f S = ∑ a, if (S ∩ C a).Nonempty then w a else 0

end SharpConsist.Supplement


