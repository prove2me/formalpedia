-- Prove2me | Definitions.Def_HiringLP_Parallel_GKPS
-- name    : HiringLP_Parallel_GKPS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:36.689685+00:00
-- url     : https://prove2.me/theorems/d61a28b3-efb0-4f1f-a471-e7caae9b92f8
-- title:
--   App. A.2, p. ec2 — properties (P1)–(P3) of the GKPS dependent rounding on a complete bipartite graph
-- statement:
--   Dependent rounding on a bipartite graph, after Gandhi, Khuller, Parthasarathy and Srinivasan (2006), described by the three properties Epstein and Ma list in their Appendix A.2.
--
--   Let $A$ and $B$ be finite sets and consider the complete bipartite graph with edge set $A\times B$ and edge weights $x_{ab}\in[0,1]$. A rounding outputs a random edge set $Y\subseteq A\times B$; write $X_{ab}=1$ if $(a,b)\in Y$ and $X_{ab}=0$ otherwise. For a vertex $a\in A$ let $\ell_a=\sum_{b}x_{ab}$ be its fractional degree, and for $b\in B$ let $\ell_b=\sum_a x_{ab}$. A probability distribution $\mu$ on edge sets is a **GKPS rounding** of $x$ if
--
--   1. **(P1) marginals:** $\mathbb E(X_{ab})=x_{ab}$ for every edge $(a,b)$;
--   2. **(P2) degree preservation:** with probability $1$, $\sum_b X_{ab}\in\{\lfloor\ell_a\rfloor,\lceil\ell_a\rceil\}$ for every $a\in A$ and $\sum_a X_{ab}\in\{\lfloor\ell_b\rfloor,\lceil\ell_b\rceil\}$ for every $b\in B$;
--   3. **(P3) negative correlation:** for every vertex $u\in A\cup B$, every set $S$ of edges incident to $u$, and every $c\in\{0,1\}$,
--   $$\mathbb P\Big(\bigcap_{e\in S}\{X_e=c\}\Big)\le\prod_{e\in S}\mathbb P(X_e=c).$$
--
--   The file also defines $\mathbb P(\bigcap_{e\in S}\{X_e=c\})$ under $\mu$ and the degrees of a vertex in a given edge set.
--
--   The definition is generic in the two vertex sets so that any result about dependent rounding on bipartite graphs can use it; in this mission $A$ is the set of candidates and $B$ the set of positions.
--
--   **Formalization Note** The rounding scheme is not constructed: a distribution $\mu:\mathcal P(A\times B)\to\mathbb R$ with $\mu\ge0$ and $\sum_Y\mu(Y)=1$ is a GKPS rounding when it has (P1)–(P3), which are the only properties of the scheme the paper uses. Gandhi et al. show that their procedure produces such a distribution for every $x\in[0,1]^{A\times B}$. "With probability 1" in (P2) is "for every $Y$ with $\mu(Y)\neq0$". The graph is complete bipartite, as in the paper's use; an edge of weight $0$ is never selected by (P1).
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. ec2 (PDF p. 34), App. A.2, properties (P1)–(P3)

import Mathlib

namespace HiringLP.Parallel

open Finset

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- `ℙ(X_e = c for every e ∈ S)` when the rounded edge set `Y = {e : X_e = 1}` of the complete
bipartite graph `A × B` has law `μ` (`X_e = 1` iff `e ∈ Y`). -/
def probAll (μ : Finset (A × B) → ℝ) (S : Finset (A × B)) (c : Bool) : ℝ :=
  ∑ Y ∈ univ.filter (fun Y : Finset (A × B) => ∀ e ∈ S, decide (e ∈ Y) = c), μ Y

/-- The degree `Σ_{b} X_{ab}` of the vertex `a ∈ A` in the rounded edge set `Y`. -/
def degLeft (Y : Finset (A × B)) (a : A) : ℕ := (Y.filter (fun e => e.1 = a)).card

/-- The degree `Σ_{a} X_{ab}` of the vertex `b ∈ B` in the rounded edge set `Y`. -/
def degRight (Y : Finset (A × B)) (b : B) : ℕ := (Y.filter (fun e => e.2 = b)).card

/-- The properties (P1)–(P3) of the dependent rounding scheme of Gandhi, Khuller, Parthasarathy
and Srinivasan (2006), App. A.2 of Epstein–Ma, on the complete bipartite graph with vertex sides
`A`, `B` and edge weights `x a b ∈ [0, 1]`: `μ` is a probability distribution on rounded edge sets
`Y ⊆ A × B` such that
* (P1) `E(X_ab) = x_ab` for every edge;
* (P2) with probability 1 every vertex keeps its fractional degree up to rounding:
  `Σ_b X_ab ∈ {⌊ℓ_a⌋, ⌈ℓ_a⌉}` with `ℓ_a = Σ_b x_ab`, and likewise at every `b ∈ B`;
* (P3) for every vertex, every set `S` of edges incident to it and every `c ∈ {0, 1}`,
  `ℙ(∩_{e ∈ S} {X_e = c}) ≤ ∏_{e ∈ S} ℙ(X_e = c)`. -/
structure IsGKPS (x : A → B → ℝ) (μ : Finset (A × B) → ℝ) : Prop where
  nonneg : ∀ Y, 0 ≤ μ Y
  sum_one : ∑ Y, μ Y = 1
  /-- (P1) marginal distribution -/
  marginal : ∀ a b, ∑ Y ∈ univ.filter (fun Y : Finset (A × B) => (a, b) ∈ Y), μ Y = x a b
  /-- (P2) degree preservation at the vertices of `A` -/
  degree_left : ∀ Y, μ Y ≠ 0 → ∀ a,
    ((degLeft Y a : ℤ) = ⌊∑ b, x a b⌋ ∨ (degLeft Y a : ℤ) = ⌈∑ b, x a b⌉)
  /-- (P2) degree preservation at the vertices of `B` -/
  degree_right : ∀ Y, μ Y ≠ 0 → ∀ b,
    ((degRight Y b : ℤ) = ⌊∑ a, x a b⌋ ∨ (degRight Y b : ℤ) = ⌈∑ a, x a b⌉)
  /-- (P3) negative correlation at the vertices of `A` -/
  negcorr_left : ∀ (a : A) (S : Finset (A × B)), (∀ e ∈ S, e.1 = a) → ∀ c : Bool,
    probAll μ S c ≤ ∏ e ∈ S, probAll μ {e} c
  /-- (P3) negative correlation at the vertices of `B` -/
  negcorr_right : ∀ (b : B) (S : Finset (A × B)), (∀ e ∈ S, e.2 = b) → ∀ c : Bool,
    probAll μ S c ≤ ∏ e ∈ S, probAll μ {e} c

end HiringLP.Parallel


