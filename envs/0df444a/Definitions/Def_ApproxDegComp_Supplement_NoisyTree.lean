-- Prove2me | Definitions.Def_ApproxDegComp_Supplement_NoisyTree
-- name    : ApproxDegComp_Supplement_NoisyTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:58:59.410415+00:00
-- url     : https://prove2.me/theorems/7bbd7793-afda-47a4-94fc-fadcc51c834e
-- title:
--   Noisy decision trees, their output probabilities and expected cost
-- statement:
--   In the **noisy oracle model** an input $x\in\{0,1\}^n$ is accessed through noisy queries. A noisy query names a coordinate $i\in[n]$ and a strength $\gamma\in[0,1]$; the oracle returns an independent bit $Y$ with
--
--   $$\Pr[Y=x_i]=\frac{1+\gamma}{2},\qquad \Pr[Y\ne x_i]=\frac{1-\gamma}{2},$$
--
--   and the query costs $\gamma^2$.
--
--   A **noisy decision tree** is a finite binary tree whose internal nodes are labelled by pairs $(i,\gamma)$ with $i\in[n]$, $\gamma\in[0,1]$ (labels may repeat along a path) and whose leaves are labelled $0$ or $1$. On input $x$ it starts at the root, makes the noisy query of the current node and moves to the child for the answer $Y$, until it reaches a leaf, whose label is the output. For each tree $t$ this defines
--
--   1. the probability $\Pr[t(x)=v]$, over the oracle's answers, that $t$ outputs $v$;
--   2. the expected cost $\mathbb E\big[\sum_{s\le T}\gamma_s^2\big]$ of the queries on the path followed.
--
--   These are the building blocks of noisy randomized query complexity.
--
--   **Formalization Note** Trees are an inductive type, so every tree is finite. The answer $0$ leads to the first child and $1$ to the second. Output probability and cost are defined by recursion on the tree: at a node the probability of answer $1$ is $(1+\gamma)/2$ if $x_i=1$ and $(1-\gamma)/2$ if $x_i=0$.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Definitions 6–7, p.12

import Mathlib

namespace ApproxDegComp

namespace Supplement

/-- **Noisy decision tree** (Definitions 6–7, p.12).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Definition 7,
p.12: "A noisy decision tree is a finite binary tree with internal nodes labeled as (i, γ) where
γ ∈ [0, 1] and i ∈ [n] and each leaf is labeled 0 or 1. Descendants can have same node label as
their ancestors."

At `node i γ t₀ t₁` the tree makes a noisy query to coordinate `i` with strength `γ`
(Definition 6: the oracle returns an independent `Y ∈ {0,1}` with `Pr[Y = x_i] = (1+γ)/2`,
`Pr[Y ≠ x_i] = (1−γ)/2`, at cost `γ²`) and continues in `t₀` if `Y = 0`, in `t₁` if `Y = 1`.

**Formalization Note** The inductive type contains exactly the finite trees; labels may repeat
along a path. The strength is an element of `unitInterval = [0,1]`. -/
inductive NoisyTree (ι : Type) where
  /-- a leaf labelled with the output bit -/
  | leaf (b : Bool)
  /-- a noisy query to coordinate `i` with strength `γ`; continue in `t₀` on answer `0`, in `t₁`
  on answer `1` -/
  | node (i : ι) (γ : unitInterval) (t₀ t₁ : NoisyTree ι)

namespace NoisyTree

variable {ι : Type}

/-- The probability that a noisy query to coordinate `i` with strength `γ` answers `1` on input
`x` (Definition 6, p.12): `(1+γ)/2` if `x_i = 1`, `(1−γ)/2` if `x_i = 0`. -/
noncomputable def probOne (x : ι → Bool) (i : ι) (γ : unitInterval) : ℝ :=
  if x i then (1 + (γ : ℝ)) / 2 else (1 - (γ : ℝ)) / 2

/-- The probability, over the independent noisy oracle answers, that the tree outputs `v` on
input `x` (Definitions 6–7, p.12). -/
noncomputable def outProb : NoisyTree ι → (ι → Bool) → Bool → ℝ
  | leaf b, _, v => if b = v then 1 else 0
  | node i γ t₀ t₁, x, v =>
      probOne x i γ * t₁.outProb x v + (1 - probOne x i γ) * t₀.outProb x v

/-- The expected cost `E[∑_{t ≤ T} γ_t²]` of running the tree on input `x`, over the noisy
oracle answers (Definitions 6–7, p.12): the strength squared of every query on the path taken,
summed, in expectation. -/
noncomputable def cost : NoisyTree ι → (ι → Bool) → ℝ
  | leaf _, _ => 0
  | node i γ t₀ t₁, x =>
      (γ : ℝ) ^ 2 + probOne x i γ * t₁.cost x + (1 - probOne x i γ) * t₀.cost x

end NoisyTree

end Supplement

end ApproxDegComp


