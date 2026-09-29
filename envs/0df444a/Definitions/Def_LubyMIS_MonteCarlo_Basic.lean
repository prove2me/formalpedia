-- Prove2me | Definitions.Def_LubyMIS_MonteCarlo_Basic
-- name    : LubyMIS_MonteCarlo_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:49:33.263382+00:00
-- url     : https://prove2.me/theorems/42ac4794-980b-4cab-b3f2-ecb11cadc803
-- title:
--   Neighbourhood N(W), eliminated edges, sum(i), and the select steps and laws of Algorithms A and B (§3.1–3.4)
-- statement:
--   This file fixes the objects of one round of Luby's Monte Carlo algorithms A and B for the maximal independent set problem. Throughout, $G' = (V', E')$ is the current graph, a finite simple undirected graph; $d(i)$ is the degree of $i$ and $\mathrm{adj}(i)$ its set of neighbours.
--
--   1. **Neighbourhood.** For $W \subseteq V'$, $N(W) = \{ i \in V' : \exists j \in W,\ (i,j) \in E' \}$.
--   2. **Eliminated edges.** For a selected set $I' \subseteq V'$, the loop body removes $Y = I' \cup N(I')$ and keeps the subgraph induced on $V' - Y$. The number of eliminated edges is
--   $$\mathrm{elim}(I') = \big|\{ \{i,j\} \in E' : i \in I' \cup N(I') \text{ or } j \in I' \cup N(I') \}\big|,$$
--   which is $Y_k - Y_{k+1}$ when $G'$ is the graph before the $k$-th execution of the loop body.
--   3. **The weight** $\mathrm{sum}(i) = \sum_{j \in \mathrm{adj}(i)} 1/d(j)$. The paper defines it for $d(i) \ge 1$; for $d(i) = 0$ it is the empty sum $0$ here.
--   4. **Algorithm A's select step.** Given priorities $\pi : V' \to \mathbb{N}$, $I' = \{ i : \pi(i) < \pi(j) \text{ for every } j \in \mathrm{adj}(i) \}$.
--   5. **Algorithm B's select step.** Given coins $c : V' \to \{0,1\}$ and $X = \{ i : c(i) = 1 \}$, $I' = \{ i \in X : d(j) < d(i) \text{ for every } j \in \mathrm{adj}(i) \cap X \}$.
--   6. **Algorithm A's law.** The priorities $\pi(i)$ are mutually independent and uniform on $\{1, \dots, n^4\}$, where $n$ is the number of vertices of the input graph. So $\Pr_A[P] = |\{\pi : P(\pi)\}| / (n^4)^{|V'|}$ and $E_A[f] = \sum_\pi f(\pi) / (n^4)^{|V'|}$.
--   7. **Algorithm B's law.** The coins are mutually independent, with $\Pr[c(i) = 1] = 1/(2d(i))$ if $d(i) \ge 1$ and $\Pr[c(i) = 1] = 1$ if $d(i) = 0$. So a coin vector $c$ has probability $\prod_i \Pr[c(i)]$, and $\Pr_B$ and $E_B$ are the corresponding finite sums.
--
--   These are the objects about which Theorem 1, Lemma A and Lemma B are stated.
--
--   **Formalization Note** The current graph is a `SimpleGraph V` on a finite type, with $V' = V$. Each undirected edge of $G'$ appears in the paper's $E'$ in both orientations, so ALGEDGE runs on $(i,j)$ and on $(j,i)$: in Algorithm A a vertex is removed as soon as some neighbour has priority at most its own, and in Algorithm B a vertex of $X$ is removed as soon as some neighbour in $X$ has degree at least its own. Algorithm B's $I'$ starts at $X$ (the page does not initialize $I'$ in §3.3; Algorithm D's code on p. 1047 has $I' \leftarrow X$). Algorithm A's priorities are drawn as `π₀ : V → Fin (n ^ 4)` and read as $\pi(i) = \pi_0(i) + 1 \in \{1, \dots, n^4\}$. Probabilities and expectations are explicit finite sums over the $(n^4)^{|V|}$ priority vectors or the $2^{|V|}$ coin vectors, which is exactly mutual independence.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, pp. 1038–1041, §3.1 (N(W), loop body), §3.2 (Algorithm A: ALGVERTEX, ALGEDGE, select step), §3.3 (Algorithm B: coin(i), select step), §3.4 (Y_k, sum(i))

import Mathlib

namespace LubyMIS.MonteCarlo

open Finset

/-- The neighbourhood `N(W) = {i ∈ V′ : ∃ j ∈ W, (i, j) ∈ E′}` of a vertex set `W` in the current
graph `H = G′` (Luby 1986, §3.1, p. 1038). -/
def nbhd {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (W : Finset V) :
    Finset V :=
  Finset.univ.filter (fun i => ∃ j ∈ W, H.Adj i j)

open Classical in
/-- The number of edges eliminated by one execution of the loop body that selects `I′`: the edges of
`H` with at least one endpoint in `Y = I′ ∪ N(I′)`. The induced subgraph on `V′ − Y` keeps exactly the
other edges, so this is `Y_k − Y_{k+1}` (§3.1, p. 1039; §3.4, p. 1040). -/
noncomputable def eliminated {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (I' : Finset V) : ℕ :=
  (H.edgeFinset.filter (fun e => ∃ v ∈ e, v ∈ I' ∪ nbhd H I')).card

/-- `sum(i) = ∑_{j ∈ adj(i)} 1 / d(j)` (§3.4, p. 1041). The page defines it only for `d(i) ≥ 1`; at
`d(i) = 0` this is the empty sum `0`. -/
noncomputable def sumInv {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i : V) : ℝ :=
  ∑ j ∈ H.neighborFinset i, 1 / (H.degree j : ℝ)

/-- Algorithm A's select step (§3.2, pp. 1039–1040) for the priorities `π`: ALGEDGE runs on both
orientations of every edge, so `i` survives iff `π(i) < π(j)` for every neighbour `j`. -/
def selectA {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (π : V → ℕ) :
    Finset V :=
  Finset.univ.filter (fun i => ∀ j, H.Adj i j → π i < π j)

/-- Algorithm B's select step (§3.3, p. 1040) for the coin values `c` (`X = {i : c i = true}`,
`I′` starting at `X`): `i ∈ X` survives iff every neighbour `j ∈ X` has `d(j) < d(i)`. -/
def selectB {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (c : V → Bool) :
    Finset V :=
  Finset.univ.filter (fun i => c i = true ∧ ∀ j, H.Adj i j → c j = true → H.degree j < H.degree i)

/-- Algorithm A's priority values: `π(i) = (π₀ i : ℕ) + 1 ∈ {1, …, n⁴}` for `π₀ : V → Fin (n ^ 4)`. -/
def prioA {V : Type*} {n : ℕ} (π₀ : V → Fin (n ^ 4)) : V → ℕ :=
  fun i => (π₀ i : ℕ) + 1

open Classical in
/-- Probability of an event `P` of the priority vector under Algorithm A's law: the priorities are
mutually independent and uniform on `{1, …, n⁴}`, i.e. the uniform law on the `(n⁴)^{|V|}` vectors. -/
noncomputable def probA {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (P : (V → ℕ) → Prop) : ℝ :=
  ((Finset.univ.filter (fun π₀ : V → Fin (n ^ 4) => P (prioA π₀))).card : ℝ) /
    ((n : ℝ) ^ 4) ^ Fintype.card V

/-- Expectation of a real function of the priority vector under Algorithm A's law. -/
noncomputable def expA {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) (f : (V → ℕ) → ℝ) : ℝ :=
  (∑ π₀ : V → Fin (n ^ 4), f (prioA π₀)) / ((n : ℝ) ^ 4) ^ Fintype.card V

/-- `Pr[coin(i) = 1]` in Algorithm B (§3.3, p. 1040): `1/(2 d(i))` if `d(i) ≥ 1`, and `1` if `d(i) = 0`. -/
noncomputable def coinProb {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (i : V) : ℝ :=
  if 1 ≤ H.degree i then 1 / (2 * (H.degree i : ℝ)) else 1

/-- The probability of the coin vector `c` in Algorithm B: the coins are mutually independent, so the
law is the product of the marginals. -/
noncomputable def lawB {V : Type*} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (c : V → Bool) : ℝ :=
  ∏ i, if c i then coinProb H i else 1 - coinProb H i

open Classical in
/-- Probability of an event `P` of the coin vector under Algorithm B's law. -/
noncomputable def probB {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (P : (V → Bool) → Prop) : ℝ :=
  ∑ c : V → Bool, if P c then lawB H c else 0

/-- Expectation of a real function of the coin vector under Algorithm B's law. -/
noncomputable def expB {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (f : (V → Bool) → ℝ) : ℝ :=
  ∑ c : V → Bool, lawB H c * f c

end LubyMIS.MonteCarlo


