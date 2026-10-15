-- Prove2me | Definitions.Def_StrictCompatLB_RegularDegree_RandomServerRegular
-- name    : StrictCompatLB_RegularDegree_RandomServerRegular
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:11.936935+00:00
-- url     : https://prove2.me/theorems/791a395a-192e-4f4f-a6f8-7f984b60287a
-- title:
--   Theorem 3.5's random compatibility graph: each server picks c(N) dispatchers uniformly without replacement; the sets $B_N(X)$ (A.3) and $A_N$ (A.7)
-- statement:
--   Fix sequences $M(N)$ and $c(N)$ of natural numbers. A graph $G_N$ between $V_N=\{1,\dots,N\}$ and $W_N=\{1,\dots,M(N)\}$ is encoded by its adjacency matrix $a\in\{0,1\}^{N\times M(N)}$, with edge set $E_N=\{(v,w):a_{vw}=1\}$.
--
--   **The random graph of Theorem 3.5.** Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and, for each $N$, let $A_N:\Omega\to\{0,1\}^{N\times M(N)}$ be a random adjacency matrix. The family is *server-regular random* with degree $c(N)$ if each $A_N$ is measurable and, for every matrix $a$,
--   $$\mathbb P(A_N=a)=\begin{cases}\binom{M(N)}{c(N)}^{-N}&\text{if every row of }a\text{ has exactly }c(N)\text{ ones},\\[2pt] 0&\text{otherwise.}\end{cases}$$
--   Equivalently, each server $v$ chooses its neighbourhood $\mathcal N_v$ uniformly among the $c(N)$-subsets of $W_N$ (sampling without replacement), independently over $v$. Only the law of each $G_N$ is prescribed. Nothing is assumed about the joint law of graphs with different $N$, matching the paper's convention that almost-sure statements hold for any coupling $\mathbb P_0$ on $\prod_N\{0,1\}^{N\times M(N)}$ with these marginals. The random graph sequence is $G_N(\omega)$, with adjacency matrix $A_N(\omega)$.
--
--   **The sets of Appendix A.** For a graph sequence, $\varepsilon\in\mathbb R$ and $X\subseteq W_N$:
--   $$B_N(X)=\Big\{v\in V_N:\Big||\mathcal N_v\cap X|-\frac{c(N)|X|}{M(N)}\Big|\ge\frac{\varepsilon\,c(N)|X|}{M(N)}\Big\}\quad\text{(A.3)},$$
--   $$A_N=\Big\{w\in W_N:|\mathcal N_w|\le(1-\varepsilon)\,\frac{N\,c(N)}{M(N)}\Big\}\quad\text{(A.7)}.$$
--   $B_N(X)$ is the set of servers whose number of neighbours in $X$ deviates from its mean. $A_N$ is the set of dispatchers whose degree falls well below its mean $\mathbb E|\mathcal N_w|=Nc(N)/M(N)$.
--
--   **Formalization Note** The adjacency-matrix encoding follows p. 13, which places the graphs in $\{0,1\}^{N\times M(N)}$. The construction is printed as "select $c(N)$ edges from $\{(v,w)\in V_N\times W_N\mid v\in V_N\}$". The set should be $\{(v,w):w\in W_N\}$ for the fixed server $v$, as §3.2 ("all the servers have degree exactly equal to $c(N)$") and Appendix A (hypergeometric $|\mathcal N_v\cap X|$, independence over $v$) confirm. In (A.7) the expectation $\mathbb E|\mathcal N_w|$ is written out as its value $Nc(N)/M(N)$ under this law.
-- source:
--   Rutten & Mukherjee, Load Balancing Under Strict Compatibility Constraints, arXiv:2008.07562v2, p. 13, §3.2 and Theorem 3.5 (construction); p. 31, Lemma A.2, (A.3); p. 32, Lemma A.3, (A.7)

import Mathlib
import Definitions.Def_StrictCompatLB_RegularDegree_GraphConditions

open Finset MeasureTheory

namespace StrictCompatLB.RegularDegree

/-! The random compatibility graphs of Theorem 3.5 of Rutten & Mukherjee,
arXiv:2008.07562v2 (p. 13): each server picks `c(N)` of the `M(N)` dispatchers uniformly
at random without replacement, independently over servers. A graph `G_N` is encoded by its
adjacency matrix `a : Fin N → Fin (M N) → Bool`, an element of `{0,1}^{N × M(N)}` as on
p. 13. Only the law of each `G_N` is prescribed; nothing is assumed about the joint law of
different `N`. -/

/-- The edge set `E_N ⊆ V_N × W_N` of the adjacency matrix `a`. -/
def edgeSetOf {N m : ℕ} (a : Fin N → Fin m → Bool) : Finset (Fin N × Fin m) :=
  Finset.univ.filter (fun p => a p.1 p.2 = true)

/-- Every server (row of `a`) has exactly `k` neighbours. -/
def IsServerRegular {N m : ℕ} (k : ℕ) (a : Fin N → Fin m → Bool) : Prop :=
  ∀ v : Fin N, (Finset.univ.filter (fun w => a v w = true)).card = k

open Classical in
/-- `adj N : Ω → {0,1}^{N × M(N)}` is a random adjacency matrix whose law is that of
Theorem 3.5: it is measurable, and every matrix in which each server has exactly `c(N)`
neighbours has probability `C(M(N), c(N))^{-N}`, every other matrix probability `0`. This is
the product over servers of the uniform law on `c(N)`-subsets of `W_N`. -/
def IsRandomServerRegular {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M c : ℕ → ℕ)
    (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool) : Prop :=
  ∀ N : ℕ, Measurable (adj N) ∧
    ∀ a : Fin N → Fin (M N) → Bool,
      P (adj N ⁻¹' {a}) =
        if IsServerRegular (c N) a then (((Nat.choose (M N) (c N) : ℕ) : ENNReal) ^ N)⁻¹ else 0

/-- The random graph sequence `G_N(ω)` of the adjacency matrices `adj N ω`. -/
def randomGraph {Ω : Type*} (M : ℕ → ℕ) (adj : (N : ℕ) → Ω → Fin N → Fin (M N) → Bool)
    (ω : Ω) : (N : ℕ) → Finset (Fin N × Fin (M N)) :=
  fun N => edgeSetOf (adj N ω)

/-- The set `B_N(X)` of (A.3), p. 31: servers whose number of neighbours in `X ⊆ W_N`
deviates from `c(N)|X|/M(N)` by at least `ε c(N)|X|/M(N)`. -/
noncomputable def badServers (M c : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (ε : ℝ) (N : ℕ)
    (X : Finset (Fin (M N))) : Finset (Fin N) :=
  Finset.univ.filter (fun v =>
    ε * (c N : ℝ) * (X.card : ℝ) / (M N : ℝ) ≤
      |((StrictCompatLB.MeanField.nbrV M G N v ∩ X).card : ℝ) - (c N : ℝ) * (X.card : ℝ) / (M N : ℝ)|)

/-- The set `A_N` of (A.7), p. 32: dispatchers with `|𝒩_w| ≤ (1 − ε) E[|𝒩_w|]`, where
`E[|𝒩_w|] = N c(N)/M(N)` in the model of Theorem 3.5. -/
noncomputable def lowDegreeDispatchers (M c : ℕ → ℕ) (G : (N : ℕ) → Finset (Fin N × Fin (M N))) (ε : ℝ)
    (N : ℕ) : Finset (Fin (M N)) :=
  Finset.univ.filter (fun w =>
    ((StrictCompatLB.MeanField.nbrW M G N w).card : ℝ) ≤ (1 - ε) * ((N : ℝ) * (c N : ℝ) / (M N : ℝ)))

end StrictCompatLB.RegularDegree


