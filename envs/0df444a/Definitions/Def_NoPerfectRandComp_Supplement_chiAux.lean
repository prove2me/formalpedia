-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_chiAux
-- name    : NoPerfectRandComp_Supplement_chiAux
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:13:58.250936+00:00
-- url     : https://prove2.me/theorems/93ad1eb4-3aa0-414a-bce3-8a722463fae9
-- title:
--   Conflict-sum recursion for $\chi(T,(\mu_0,\mu_1))$
-- statement:
--   The recursion that evaluates the conflict sum (3). For a decision tree $T$ whose root is reached exactly by the inputs in a set $S$, at depth $d$ and with weight $r$: a leaf contributes $0$; a node querying $x_i$ contributes
--   $$
--   d\cdot\bigl|p_0 - p_1\bigr|\cdot r,\qquad p_b = \Pr_{\mu_b}[x_i = 0\mid x\in S],
--   $$
--   plus, for each answer $a$, the contribution of the child subtree with input set $S\cap\{x_i = a\}$, depth $d+1$ and weight $r\cdot\min_b\Pr_{\mu_b}[x_i = a\mid x\in S]$.
--
--   **Formalization Note** Conditional probabilities are computed in $\mathbb R$ with the convention $0/0 = 0$; a node whose input set has $\mu_b$-mass $0$ has weight $0$, so the convention does not affect the sum.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.3, (3), p.5

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical

namespace NoPerfectRandComp

namespace Supplement

/-- The recursion behind the conflict sum (3) of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.3, p.5.
`chiAux μ₀ μ₁ T S d r` is the sum `Σ_v d_T(v) Δ(v) R(v)` over the query nodes `v` of the subtree
`T`, when the root of `T` is reached exactly by the inputs in `S`, has depth `d` and weight
`R = r`. At a node querying `x_i`:
`p_b = Pr_{μ_b}[x_i = 0 | x ∈ S]`, `Δ = |p₀ − p₁|`, it contributes `d · Δ · r`, and its child on
answer `a` has depth `d + 1` and weight `r · min_b Pr_{μ_b}[x_i = a | x ∈ S]`. Leaves query
nothing and contribute `0`.

**Formalization Note** Conditional probabilities are ratios of `PMF.toOuterMeasure` masses,
computed in `ℝ`; on a set of `μ_b`-mass zero the ratio is `0`. Such a node has weight `R = 0` (the
minimum includes a zero factor at the first step that leaves the support), so the convention does
not affect the sum. -/
noncomputable def chiAux {ι : Type} (μ₀ μ₁ : PMF (ι → Bool)) :
    QAlgorithms.DecisionTree ι Bool Bool → Set (ι → Bool) → ℕ → ℝ → ℝ
  | .leaf _, _, _, _ => 0
  | .node i next, S, d, r =>
      let pr : PMF (ι → Bool) → Set (ι → Bool) → ℝ := fun μ A =>
        (μ.toOuterMeasure (A ∩ S)).toReal / (μ.toOuterMeasure S).toReal
      (d : ℝ) * |pr μ₀ {x | x i = false} - pr μ₁ {x | x i = false}| * r +
        ∑ a : Bool, chiAux μ₀ μ₁ (next a) (S ∩ {x | x i = a}) (d + 1)
          (r * min (pr μ₀ {x | x i = a}) (pr μ₁ {x | x i = a}))

end Supplement

end NoPerfectRandComp


