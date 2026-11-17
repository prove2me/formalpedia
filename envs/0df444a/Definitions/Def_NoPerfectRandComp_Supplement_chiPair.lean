-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_chiPair
-- name    : NoPerfectRandComp_Supplement_chiPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:14:29.881127+00:00
-- url     : https://prove2.me/theorems/f77956c5-f5f2-45c1-9cd7-90789c13256e
-- title:
--   Conflict of a tree against a pair, $\chi(T,(\mu_0,\mu_1))$
-- statement:
--   Let $T$ be a deterministic decision tree, $q(v)$ the index queried at node $v$, and $d_T(v)$ the number of vertices on the root-to-$v$ path (the root has depth $1$). For distributions $\mu_0, \mu_1$ on inputs put $p_b(v) = \Pr_{\mu_b}[x_{q(v)} = 0\mid x \text{ at } v]$, $\Delta(v) = |p_0(v) - p_1(v)|$, $R(\mathrm{root}) = 1$ and $R(v) = R(\pi(v))\cdot\min_b\Pr_{\mu_b}[x\to v\mid x\text{ at }\pi(v)]$, where $\pi(v)$ is the parent of $v$. Then
--   $$
--   \chi\bigl(T,(\mu_0,\mu_1)\bigr) = \sum_{v\in T} d_T(v)\,\Delta(v)\,R(v).
--   $$
--
--   **Formalization Note** The sum runs over query nodes; a leaf queries nothing and contributes $0$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.3, (3), p.5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_Supplement_chiAux

namespace NoPerfectRandComp

namespace Supplement

/-- The conflict of a tree against a pair (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), (3), p.5):
`χ(T, (μ₀, μ₁)) = Σ_{v ∈ T} d_T(v) Δ(v) R(v)`, where `d_T(v)` is the number of vertices on the
root-to-`v` path (the root has depth `1`), `p_b(v) = Pr_{μ_b}[x_{q(v)} = 0 | x at v]`,
`Δ(v) = |p₀(v) − p₁(v)|`, `R(root) = 1` and
`R(v) = R(π(v)) · min_b Pr_{μ_b}[x → v | x at π(v)]`.

**Formalization Note** The sum runs over query nodes (a leaf queries nothing); `0` is `false`. -/
noncomputable def chiPair {ι : Type} (T : QAlgorithms.DecisionTree ι Bool Bool)
    (μ₀ μ₁ : PMF (ι → Bool)) : ℝ :=
  chiAux μ₀ μ₁ T Set.univ 1 1

end Supplement

end NoPerfectRandComp


