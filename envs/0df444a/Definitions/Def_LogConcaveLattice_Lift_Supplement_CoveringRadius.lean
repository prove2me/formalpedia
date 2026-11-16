-- Prove2me | Definitions.Def_LogConcaveLattice_Lift_Supplement_CoveringRadius
-- name    : LogConcaveLattice_Lift_Supplement_CoveringRadius
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:33:45.837456+00:00
-- url     : https://prove2.me/theorems/cf1b2c33-3e78-4a88-a7ba-80620218cb8a
-- title:
--   §1.1, p. 4 — covering radius $\mu(\Lambda,K)=\min\{r\ge0:\Lambda+rK=\mathbb R^n\}$
-- statement:
--   Let $\Lambda\subseteq\mathbb R^n$ be a lattice and $K\subseteq\mathbb R^n$ a set. The **covering radius** of $\Lambda$ with respect to $K$ is
--
--   $$\mu(\Lambda,K)=\min\{r\ge0:\ \Lambda+rK=\mathbb R^n\},$$
--
--   the least dilation factor $r\ge0$ for which the translates $\lambda+rK$, $\lambda\in\Lambda$, cover $\mathbb R^n$; here $\Lambda+rK=\{\lambda+rk:\lambda\in\Lambda,\ k\in K\}$.
--
--   It is the quantity bounded in Theorem 1.2. Together with the Minkowski functional $\|x\|_K=\inf\{r>0:x\in rK\}$ (Mathlib's `gauge K x`) it gives the lattice-geometric side of the covering-radius bound; for a convex body $K$ with $0\in\operatorname{int}K$ one also has $\mu(\Lambda,K)=\sup_x\min_{\lambda\in\Lambda}\|x-\lambda\|_K$, the form used in the proof on p. 15.
--
--   **Formalization Note** The minimum is encoded as the infimum (`sInf`) of the set $\{r\ge0:\forall x,\ \exists\lambda\in\Lambda,\ \exists k\in K,\ x=\lambda+rk\}$. For a full-rank lattice and a convex body with $0\in\operatorname{int}K$ this set is nonempty, bounded below by $0$, closed upward and closed, so the infimum is attained and equals the paper's minimum. On an empty set (e.g. a lower-rank lattice) Lean's `sInf` would return $0$; that case does not occur under the hypotheses of Theorem 1.2.
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, SHA-256 c2ca89e66a6221772830cc9470a9d1f7fb2afeb8fc716a1b283f35b2280c5eac, §1.1, p. 4 (definition of the covering radius µ(Λ, K) and of the Minkowski functional ∥x∥_K)

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice

namespace LogConcaveLattice.Lift.Supplement

variable {n : ℕ}

/-- **Covering radius** (Letwin–Reis–Rothvoss, p. 4):
`µ(Λ, K) = min {r ≥ 0 : Λ + r K = ℝⁿ}`, the least `r ≥ 0` such that every `x ∈ ℝⁿ` can be
written as `x = λ + r k` with `λ ∈ Λ` and `k ∈ K`. Encoded as the infimum of that set of radii;
for a full-rank lattice `Λ` and a convex body `K` with `0 ∈ int K` the set is nonempty, closed
upward and closed, so the infimum is the paper's minimum. -/
noncomputable def coveringRadius (Λ : Submodule ℤ (V n)) (K : Set (V n)) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∀ x : V n, ∃ l ∈ Λ, ∃ k ∈ K, x = l + r • k}

end LogConcaveLattice.Lift.Supplement


