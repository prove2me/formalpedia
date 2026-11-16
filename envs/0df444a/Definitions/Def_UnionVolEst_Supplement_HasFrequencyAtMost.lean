-- Prove2me | Definitions.Def_UnionVolEst_Supplement_HasFrequencyAtMost
-- name    : UnionVolEst_Supplement_HasFrequencyAtMost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:08:55.672217+00:00
-- url     : https://prove2.me/theorems/3a873c05-de51-4d88-9032-c26f84b5e934
-- title:
--   Streams of frequency at most $\tau$ (Definition 3)
-- statement:
--   A family of bodies $K_1,\dots,K_M\subseteq\mathbb R^n$ **has frequency at most $\tau$** if every point of $\mathbb R^n$ lies in at most $\tau$ of the bodies:
--   $$
--   \sum_{j=1}^M \mathbf 1_{K_j}(x)\;\le\;\tau\,\mathbf 1_{\bigcup_j K_j}(x)\qquad\text{for all }x\in\mathbb R^n .
--   $$
--   Every family has frequency at most $M$.
--
--   Bounded frequency is the special case of Section 7. In that case, sampling at $\beta=\varepsilon/(32\tau)$ instead of $\varepsilon/(32M)$ suffices (Theorem 23).
--
--   **Formalization Note** The left side is the number of indices $j$ with $x\in K_j$, and $\tau$ is a natural number. A point in no body gives $0\le0$, so the definition is the displayed inequality exactly. The remark $1\le\tau\le M$ is not bundled.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §7, Definition 3, p.34 (PDF p.36)

import Mathlib

namespace UnionVolEst.Supplement

open Classical in
/-- Definition 3, a `τ`-bounded frequency stream (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar,
*Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256
15de4f2e…26bd24), §7, printed p.34, PDF p.36): the bodies `K₁, …, K_M ⊆ ℝⁿ` have frequency at most
`τ` if every point lies in at most `τ` of them, `Σ_j 1_{K_j}(x) ≤ τ · 1_{∪_j K_j}(x)` for all `x`.

**Formalization Note** The count of bodies containing `x` is the cardinality of
`{j : x ∈ K_j}`; a point in no body gives `0 ≤ 0`, so this is the page's inequality exactly. `τ` is
a natural number; the page's remark `1 ≤ τ ≤ M` is not bundled. -/
def HasFrequencyAtMost {n M : ℕ} (K : Fin M → Set (EuclideanSpace ℝ (Fin n))) (τ : ℕ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n), (Finset.univ.filter (fun j => x ∈ K j)).card ≤ τ

end UnionVolEst.Supplement


