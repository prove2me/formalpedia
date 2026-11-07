-- Prove2me | Definitions.Def_KServerConj_cl
-- name    : KServerConj_cl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:42.052526+00:00
-- url     : https://prove2.me/theorems/05d95b57-6e53-4a3b-b0fe-d08d0b353157
-- title:
--   Clique weight $\mathrm{cl}(X)$ of a configuration
-- statement:
--   For a configuration $X=\{x_1,\dots,x_k\}$ in a (pseudo)metric space, its **clique weight** is the total distance between its pairs of distinct points,
--
--   $$\mathrm{cl}(X)=\sum_{1\le i<j\le k} d(x_i,x_j).$$
--
--   It is the additive constant in the main theorem, $\mathrm{WFA}_{C_0}(\varrho)\le k\,\mathrm{OPT}_{C_0}(\varrho)+\mathrm{cl}(C_0)$.
--
--   **Formalization Note** The sum over unordered pairs is computed as half the sum over ordered pairs $(x,y)$, $x\ne y$, of points of $X$ (`X.offDiag`), which counts each pair twice.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §1.1, p.2 (pdf p.3)

import Mathlib

namespace KServerConj

/-- **The clique weight of a configuration**, Coester, Koutsoupias, Zbysiński, *The k-server
conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §1.1, printed p.2
(PDF p.3):

"For a configuration X = {x₁, …, x_k}, define its clique weight by cl(X) = ∑_{1≤i<j≤k} d(x_i, x_j)."

**Formalization Note.** The sum over unordered pairs of distinct points is half the sum over the
ordered pairs `X.offDiag`, which counts each pair twice. -/
noncomputable def cl {M : Type*} [PseudoMetricSpace M] (X : Finset M) : ℝ := by
  classical
  exact (∑ p ∈ X.offDiag, dist p.1 p.2) / 2

end KServerConj


