-- Prove2me | Definitions.Def_ApproxDegComp_blockExpect
-- name    : ApproxDegComp_blockExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:03.09028+00:00
-- url     : https://prove2.me/theorems/48ee1059-4d78-40df-bb11-1658d90e4b14
-- title:
--   Expectation over independent blocks $\mathbb E_{X^{(i)}\sim\mu_i}[Q(X^{(1)},\dots,X^{(n)})]$
-- statement:
--   Inputs of $\{0,1\}^{mn}$ are split into $n$ disjoint blocks $x^{(1)},\dots,x^{(n)}$ of $m$ bits each, bit $j$ of block $i$ being coordinate $(i,j)$. For weight vectors $\mu_1,\dots,\mu_n$ on $\{0,1\}^m$ and $Q:\{0,1\}^{mn}\to\mathbb R$,
--
--   $$\mathbb E_{X^{(i)}\sim\mu_i}\bigl[Q(X^{(1)},\dots,X^{(n)})\bigr]=\sum_{x\in\{0,1\}^{mn}}Q(x)\prod_{i=1}^n\mu_i\bigl(x^{(i)}\bigr).$$
--
--   When every $\mu_i$ is a probability measure this is the expectation of $Q$ when the blocks are drawn independently, $X^{(i)}\sim\mu_i$.
--
--   **Formalization Note** The block convention is the one of the reused block composition `OAI.Paper320.compose`. The formula is used as written also for signed weights.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 9, p.16; Lemma 22, p.22

import Mathlib

namespace ApproxDegComp

/-- **Expectation over independent blocks** `E_{X⁽ⁱ⁾∼μᵢ}[Q(X⁽¹⁾, …, X⁽ⁿ⁾)]` (Lemmas 9, 22,
pp.16, 22).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 9, p.16: "Let X⁽¹⁾, …, X⁽ⁿ⁾ be n disjoint blocks of m bits each and X⁽ⁱ⁾'s are
sampled independently from ρ_{θᵢ}. Let R be defined as R(θ₁, …, θₙ) = E_{X⁽ⁱ⁾∼ρ_{θᵢ}}[Q(X⁽¹⁾, …,
X⁽ⁿ⁾)]."

For weight vectors `μ i` on `{0,1}^m` and `Q` on `{0,1}^{mn}`,
`blockExpect μ Q = Σ_x Q(x) Π_i μᵢ(x⁽ⁱ⁾)`, where block `i` of `x` is `j ↦ x (i, j)`.

**Formalization Note** The expectation over independent blocks is the finite sum against the
product weights. Coordinate `(i, j)` is bit `j` of block `i`, the same convention as
`OAI.Paper320.compose`. When every `μ i` is a probability vector this is an expectation; the
definition itself is the multilinear extension and is used also for signed weights. -/
def blockExpect {n m : ℕ} (μ : Fin n → (Fin m → Bool) → ℝ) (Q : (Fin n × Fin m → Bool) → ℝ) : ℝ :=
  ∑ x : Fin n × Fin m → Bool, Q x * ∏ i, μ i (fun j => x (i, j))

end ApproxDegComp


