-- Prove2me | Definitions.Def_HypClass1_qf
-- name    : HypClass1_qf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:27:48.718288+00:00
-- url     : https://prove2.me/theorems/db672fdc-dfc2-4ad7-9d8f-f9fd88281cb4
-- title:
--   Fractional expectation-threshold $q_f(\mathcal B)$
-- statement:
--   A family $\mathcal B \subseteq 2^X$ is **weakly $p$-small** if there is $g : 2^X \to \mathbb R_{\ge 0}$ with
--   $$
--   \sum_{S \subseteq B} g(S) \ge 1 \quad \forall B \in \mathcal B \qquad\text{and}\qquad \sum_{S \subseteq X} g(S) p^{|S|} \le \tfrac12. \tag{27}
--   $$
--   The **fractional expectation-threshold** of $\mathcal B$ is the largest $p$ for which $\mathcal B$ is weakly $p$-small,
--   $$
--   q_f(\mathcal B) = \max\{p \in [0,1] : \mathcal B \text{ is weakly } p\text{-small}\}.
--   $$
--
--   **Formalization Note** $g$ is nonnegative with no upper bound. The maximum is written as a supremum of the bounded set; it is attained when $\emptyset \notin \mathcal B$, and the value is $0$ if the set is empty. The module also defines "weakly $p$-small".
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.43, display (27)

import Mathlib

namespace HypClass1

/-- **Weakly p-small family**, display (27). Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.43: "We say that B is weakly p-small if there
exists a function g : 2^X → R+ such that Σ_{S⊆B} g(S) ≥ 1, ∀B ∈ B and Σ_{S⊆X} g(S)p^{|S|} ≤ 1/2."

**Formalization Note.** `g` takes nonnegative real values (`R+ = [0, ∞)`, as in the proof of
Proposition 8.10, "g : 2^X → R_{≥0}"), with no upper bound. -/
def WeaklySmall {α : Type*} [Fintype α] (p : ℝ) (B : Finset (Finset α)) : Prop :=
  ∃ g : Finset α → ℝ, (∀ S, 0 ≤ g S) ∧ (∀ A ∈ B, 1 ≤ ∑ S ∈ A.powerset, g S) ∧
    ∑ S : Finset α, g S * p ^ S.card ≤ 1 / 2

/-- **Fractional expectation-threshold** `q_f(B)`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §8.4 p.43: "The fractional expectation-threshold
of B is defined as the maximum value of p such that B is weakly p-small,
q_f(B) := max{p ∈ [0, 1] : B is weakly p-small}."

**Formalization Note.** The maximum is written as `sSup` of the set `{p ∈ [0, 1] : B weakly p-small}`,
which is bounded; for `∅ ∉ B` the set is non-empty (it contains `0`) and closed, so the supremum is the
paper's maximum. If the set is empty (`∅ ∈ B`), the value is `0`. -/
noncomputable def qf {α : Type*} [Fintype α] (B : Finset (Finset α)) : ℝ :=
  sSup {p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧ WeaklySmall p B}

end HypClass1


