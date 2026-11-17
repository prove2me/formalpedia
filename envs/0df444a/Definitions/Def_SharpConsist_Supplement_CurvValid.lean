-- Prove2me | Definitions.Def_SharpConsist_Supplement_CurvValid
-- name    : SharpConsist_Supplement_CurvValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:22:45.399399+00:00
-- url     : https://prove2.me/theorems/76ec81ba-beae-42b8-b7aa-81fc0cffeec5
-- title:
--   Algorithm conditions on instances of curvature at most $\vartheta$
-- statement:
--   For a randomized algorithm on the stream $1,\dots,n,r$ (the published `SharpConsist.ConsistentAlg`), a curvature bound $\vartheta$, a capacity $k$ and a recourse budget $C$, the predicate requires: for every normalized monotone submodular objective $f$ on $X\cup\{r\}$ **with total curvature at most $\vartheta$** and every seed, the outputs before and after the final arrival have at most $k$ elements and differ in at most $C$ elements, and the output after the final arrival is a random variable.
--
--   This is the published `SharpConsist.ConsistentAlg.Valid` restricted to the instances named in Theorem 8.1 ("on every instance … with curvature at most ϑ"). Requiring the conditions on fewer instances admits more algorithms, so lower bounds stated with it are stronger.
--
--   **Formalization Note** The query budget is the $Q$ of the algorithm's type; the conditions are imposed only on $(n+1)$-element instances in the order $1,\dots,n,r$.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), Theorem 8.1, pp.24–25; Lemma D.1, p.39

import Mathlib
import Definitions.Def_SharpConsist_ConsistentAlg
import Definitions.Def_PolyContract_IsRankFunction
import Definitions.Def_SharpConsist_Supplement_HasCurvatureAtMost

universe u

namespace SharpConsist.Supplement

/-- **Capacity, recourse and measurability on every instance of curvature at most `ϑ`.**
Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held
version, sha256 874ec76c…), Theorem 8.1, pp.24–25 ("on every instance of at most dϑ,ζk elements with
curvature at most ϑ and every random outcome, makes at most … queries before the final arrival and at
most cϑ,ζk symmetric changes there"); Lemma D.1, p.39.

`CurvValid alg ϑ k C` is the published `SharpConsist.ConsistentAlg.Valid alg k C` with its
quantifier restricted to the instances the page names: for every normalized monotone submodular
objective `f` on `X ∪ {r}` with total curvature at most `ϑ` and every seed `ω`, the outputs before and
after the final arrival have at most `k` elements and differ in at most `C` elements, and the output
after the final arrival is a random variable.

**Formalization Note.** As in the published `Valid`, the query budget is the `Q` of the
`ConsistentAlg` type, and the conditions are imposed only on `(n+1)`-element instances in the order
`1, …, n, r`. Requiring the conditions on fewer instances allows more algorithms. -/
def CurvValid {n Q : ℕ} {Ω : Type u} [MeasurableSpace Ω] (alg : SharpConsist.ConsistentAlg n Q Ω)
    (ϑ : ℝ) (k C : ℕ) : Prop :=
  ∀ f : Finset (Fin (n + 1)) → ℝ, PolyContract.IsRankFunction f → HasCurvatureAtMost ϑ f →
    (∀ ω : Ω, (alg.preOut ω f).card ≤ k ∧ (alg.post ω f).card ≤ k ∧
      (symmDiff (alg.post ω f) (SharpConsist.embedX (alg.preOut ω f))).card ≤ C) ∧
    ∀ s : Finset (Fin (n + 1)), MeasurableSet {ω : Ω | alg.post ω f = s}

end SharpConsist.Supplement


