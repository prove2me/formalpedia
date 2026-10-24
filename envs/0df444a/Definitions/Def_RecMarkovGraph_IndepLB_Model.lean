-- Prove2me | Definitions.Def_RecMarkovGraph_IndepLB_Model
-- name    : RecMarkovGraph_IndepLB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:41:52.685747+00:00
-- url     : https://prove2.me/theorems/82117b92-316d-4815-be30-690c404637ba
-- title:
--   Definition 1, p. 3, (2), p. 8, (3)–(4), pp. 9–10 — the law of G^r_{n,p}, the recursion f_a, ℓ_n, average degree and the decay chain of Corollary 4.6
-- statement:
--   The shared objects of the mission.
--
--   1. **The recursion.** For $a,x\in\mathbb R$ let $f_a(x)=x(1-ax)$ (display (3), p. 9). For $x_1\in\mathbb R$ the recursion $x_{n+1}=f_a(x_n)$ generates the sequence $x_1,x_2,\dots$; in Lean, `recSeq a x₁ k` is $x_{k+1}$.
--   2. **The function $\ell_n$** of display (4), p. 10:
--   $$\ell_n(x)=\begin{cases}\dfrac{1}{(\sqrt n+1)^2}, & n\ge\left(\dfrac{1}{f_1(x)}-1\right)^2,\\[2mm] \dfrac{f_1(x)}{n}, & \text{otherwise.}\end{cases}$$
--   3. **The recursive Markov random graph $G^r_{n,p}$** (Definition 1, p. 3). The vertices are $v_1,\dots,v_n$. For each $i=2,\dots,n$ the edges $(v_1,v_i),\dots,(v_{i-1},v_i)$ form a row $X^i_1,\dots,X^i_{i-1}$ of Bernoulli variables; distinct rows are independent. Within a row, $X^i_1$ is Bernoulli$(p)$ and, writing $p^i_{j-1}$ for the probability that $X^i_{j-1}=1$, the transition from $X^i_{j-1}$ to $X^i_j$ has the matrix (2), p. 8:
--   $$\mathbf P^i_{j-1}=\begin{pmatrix}1-p^i_{j-1}& p^i_{j-1}\\ 1-r\,p^i_{j-1}& r\,p^i_{j-1}\end{pmatrix}.$$
--   The marginal of $X^i_{j}$ is the $j$-th term of the recursion with $a=\gamma=1-r$ and $x_1=p$, so the weight of a graph $G$ is the product over rows of the probability of its row pattern under this chain. The probability of an event $E$ is the sum of the weights of the graphs in $E$.
--   4. **Average degree** $d(G)=\frac1n\sum_i\deg(v_i)=2|E(G)|/n$ (p. 12).
--   5. **The decay chain** of Corollary 4.6, p. 11: random variables $Y_1,Y_2,\dots$ with values in $\{0,1\}$ on a probability space, forming a Markov chain, with $\mathbb P\{Y_{n+1}=1\mid Y_n=0\}=\mathbb P\{Y_n=1\}$ and $\mathbb P\{Y_{n+1}=1\mid Y_n=1\}=(1-\beta)\,\mathbb P\{Y_n=1\}$.
--
--   These are the objects every statement of the mission is about: the goal and Theorem 2.2 concern $G^r_{n,p}$ and $d$, Lemmas 4.1–4.3 the recursion, and Corollary 4.6 and §10 the decay chain.
--
--   **Formalization Note** Vertices are `Fin n`, the paper's $v_k$ being `k − 1`; row `i` is the list of edges from `i` to `0, …, i − 1` and the row law is `chainWeight p r i`, whose transition out of edge `j` uses the marginal `recSeq (1 - r) p j`. The law is the explicit finite weight `rmrgWeight` and `rmrgProb n p r E` sums it over all graphs on `Fin n` satisfying `E` (no measure is built; the weights sum to $1$, checked for $n=2,3$ in a separate sanity file). Definition 1's "independent of all other edges" is read through the generation process (rows independent, each a Markov chain), which is the only consistent reading; see the goal's differences. In `IsDecayChain` the paper's $Y_1,Y_2,\dots$ are `Y 0, Y 1, …`, and every conditional probability is written multiplicatively ($\mathbb P(A\cap B)=c\,\mathbb P(B)$ for $\mathbb P(A\mid B)=c$), which also covers conditioning events of probability zero.
-- source:
--   Gupte, Zhu, Large independent sets in recursive Markov random graphs, arXiv:2207.04514v4, p. 3, Definition 1; p. 4, Notation and (1); p. 8, (2); p. 9, (3); p. 10, (4); p. 11, Corollary 4.6; p. 12, d(G)

import Mathlib

namespace RecMarkovGraph.IndepLB

open Finset
open scoped Classical

/-- The map `f_a(x) = x (1 - a x)` of recursion (3), p. 9. -/
def fa (a x : ℝ) : ℝ := x * (1 - a * x)

/-- The terms of recursion (3), p. 9: `recSeq a x₁ k` is the paper's `x_{k+1}`, so
`recSeq a x₁ 0 = x₁` and `recSeq a x₁ (k + 1) = f_a (recSeq a x₁ k)`. -/
def recSeq (a x₁ : ℝ) : ℕ → ℝ
  | 0 => x₁
  | k + 1 => fa a (recSeq a x₁ k)

/-- `ℓ_n(x)` of display (4), p. 10: `1/(√n + 1)²` if `n ≥ (1/f_1(x) - 1)²`, and `f_1(x)/n`
otherwise. -/
noncomputable def ell (n : ℕ) (x : ℝ) : ℝ :=
  if (1 / fa 1 x - 1) ^ 2 ≤ (n : ℝ) then 1 / (Real.sqrt n + 1) ^ 2 else fa 1 x / n

/-- The transition matrix (2), p. 8: the probability that an edge takes the value `cur`
given that the previous edge of the same row takes the value `prev`, when the previous edge
has marginal probability `q` of being present. After an absent edge the next edge is present
with probability `q`; after a present edge, with probability `r * q`. -/
noncomputable def stepWeight (r q : ℝ) (prev cur : Prop) : ℝ :=
  if prev then (if cur then r * q else 1 - r * q) else (if cur then q else 1 - q)

/-- The law of one row of length `m`: `x j` says whether the `j`-th edge of the row
(0-based) is present. The first edge is present with probability `p`, and the transition
from edge `j` to edge `j + 1` uses the marginal `recSeq (1 - r) p j` of edge `j`. -/
noncomputable def chainWeight (p r : ℝ) (m : ℕ) (x : ℕ → Prop) : ℝ :=
  if m = 0 then 1 else
    (if x 0 then p else 1 - p) *
      ∏ j ∈ range (m - 1), stepWeight r (recSeq (1 - r) p j) (x j) (x (j + 1))

/-- The probability weight of the graph `G` on the vertex set `Fin n` under the recursive
Markov random graph `G^r_{n,p}` (Definition 1, p. 3). Vertex `v_k` of the paper is `k - 1`.
Row `i` consists of the edges from vertex `i` to the vertices `0, …, i - 1`, in this order;
the rows are independent, and each row is the Markov chain `chainWeight p r i`. -/
noncomputable def rmrgWeight (n : ℕ) (p r : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∏ i : Fin n, chainWeight p r i (fun j => ∃ h : j < n, G.Adj ⟨j, h⟩ i)

/-- The probability `ℙ{E}` of an event `E` under `G^r_{n,p}`: the sum of the weights of the
graphs on `Fin n` that satisfy `E`. -/
noncomputable def rmrgProb (n : ℕ) (p r : ℝ) (E : SimpleGraph (Fin n) → Prop) : ℝ :=
  ∑ G : SimpleGraph (Fin n), rmrgWeight n p r G * (if E G then 1 else 0)

/-- The average degree `d(G) = (1/n) Σ deg(v_i) = 2 |E(G)| / n` (p. 12). -/
noncomputable def avgDeg {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ :=
  2 * (G.edgeFinset.card : ℝ) / n

/-- A Markov chain `Y 0, Y 1, …` of Bernoulli random variables (the paper's `Y_1, Y_2, …`)
with the decay transitions of Corollary 4.6, p. 11, every conditional probability being
written multiplicatively:
1. each `Y n` is measurable and takes only the values `0` and `1`;
2. Markov property: `P{Y_{n+1} = y_{n+1} | Y_0 = y_0, …, Y_n = y_n} = P{Y_{n+1} = y_{n+1} | Y_n = y_n}`;
3. `P{Y_{n+1} = 1 | Y_n = 0} = P{Y_n = 1}`;
4. `P{Y_{n+1} = 1 | Y_n = 1} = (1 - β) P{Y_n = 1}`. -/
def IsDecayChain {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (Y : ℕ → Ω → ℝ) (β : ℝ) : Prop :=
  (∀ n, Measurable (Y n)) ∧ (∀ n ω, Y n ω = 0 ∨ Y n ω = 1) ∧
  (∀ n (y : ℕ → ℝ),
      P.real {ω | ∀ k ≤ n + 1, Y k ω = y k} * P.real {ω | Y n ω = y n} =
        P.real {ω | ∀ k ≤ n, Y k ω = y k} * P.real {ω | Y n ω = y n ∧ Y (n + 1) ω = y (n + 1)}) ∧
  (∀ n, P.real {ω | Y n ω = 0 ∧ Y (n + 1) ω = 1} =
      P.real {ω | Y n ω = 1} * P.real {ω | Y n ω = 0}) ∧
  (∀ n, P.real {ω | Y n ω = 1 ∧ Y (n + 1) ω = 1} = (1 - β) * P.real {ω | Y n ω = 1} ^ 2)

end RecMarkovGraph.IndepLB


