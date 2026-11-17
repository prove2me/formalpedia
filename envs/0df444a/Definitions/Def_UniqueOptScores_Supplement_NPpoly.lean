-- Prove2me | Definitions.Def_UniqueOptScores_Supplement_NPpoly
-- name    : UniqueOptScores_Supplement_NPpoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:53:45.09431+00:00
-- url     : https://prove2.me/theorems/6b40d761-7bde-4961-a93c-f45cd2548f09
-- title:
--   The class $\mathrm{NP}/\mathrm{poly}$
-- statement:
--   A language $L$ belongs to $\mathrm{NP}/\mathrm{poly}$ if there are a language $K\in\mathrm{NP}$, a polynomial $\ell$ and advice strings $a_0,a_1,\dots$ with $|a_n|\le\ell(n)$ such that for every $x$
--   $$x\in L\iff (x,a_{|x|})\in K .$$
--   The advice depends only on the input length and need not be computable.
--
--   Theorem 1.1 derives $\mathrm{coNP}\subseteq\mathrm{NP}/\mathrm{poly}$ from $\mathrm{UO_P}\subseteq\mathrm{DP}$.
--
--   **Formalization Note** $\mathrm{NP}$ is the base mission's class at the empty oracle and $(x,a)$ is the base pairing. The advice sequence is an arbitrary function of $n$.
-- source:
--   Ono, Seto, Unique Optimality with Polynomially Bounded Scores (manuscript, sha256 467bcf54…), §3.2, p.14 (PDF p.15), "Advice and symmetric alternation"

import Mathlib
import Definitions.Def_UniqueOptScores_pair
import Definitions.Def_UniqueOptScores_NP

namespace UniqueOptScores

namespace Supplement

/-- **The class NP/poly.**
Ono, Seto, *Unique Optimality with Polynomially Bounded Scores* (manuscript, sha256 467bcf54…), §3.2, p.14 (PDF p.15): "For a language class C, a language L belongs to C/poly if there are a
language K ∈ C and polynomial-length advice strings a_n such that x ∈ L ⇐⇒ (x, a_{|x|}) ∈ K. The
advice depends only on the input length and need not be computable. We use this notation for
NP/poly and coNP/poly."

`L ∈ NPpoly` if there are `K ∈ NP`, an advice function `a : ℕ → {0,1}*` and a polynomial `ℓ` with
`|a n| ≤ ℓ(n)` for every `n`, such that `x ∈ L` exactly when `⟨x, a_{|x|}⟩ ∈ K`.

**Formalization Note.** NP is the base mission's `NP ∅`; the pair `(x, a)` is the base `pair`. The
advice function is arbitrary (no computability requirement), as on the page. -/
def NPpoly : Set (Set (List Bool)) :=
  {L | ∃ K ∈ NP ∅, ∃ (a : ℕ → List Bool) (ℓ : Polynomial ℕ),
    (∀ n : ℕ, (a n).length ≤ ℓ.eval n) ∧ ∀ x : List Bool, x ∈ L ↔ pair x (a x.length) ∈ K}

end Supplement

end UniqueOptScores


