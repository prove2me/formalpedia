-- Prove2me | Definitions.Def_ChanPangGQVI_Existence_Supplement_AbstractEconomy
-- name    : ChanPangGQVI_Existence_Supplement_AbstractEconomy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:54:24.866856+00:00
-- url     : https://prove2.me/theorems/5fbd6c56-804e-4f69-a13a-1e09ffc0acba
-- title:
--   Abstract economy {(X^j, S^j, u^j)} and its equilibrium points (§3)
-- statement:
--   An **abstract economy** is a family of triples $\{(X^j,S^j,u^j)\}_{j\in N}$, where:
--
--   1. $N$ is a finite set of individuals;
--   2. $X^j\subseteq\mathbb R^{n_j}$ is the strategy set of individual $j$ (the dimension $n_j$ may depend on $j$), and $X=\prod_{j\in N}X^j$ is the set of strategy profiles $x=(x_j)_{j\in N}$;
--   3. $u^j : X\times X^j\to\mathbb R$ is the utility function of individual $j$: $u^j(x,\xi_j)$ is the utility of choosing $\xi_j$ when the profile is $x$;
--   4. $S^j : X\to X^j$ is the feasibility correspondence: $S^j(x)\subseteq X^j$ is the set of strategies available to $j$ at the profile $x$.
--
--   An **equilibrium point** of the economy is a profile $x^*\in X$ such that for every $j\in N$
--
--   $$
--   u^j(x^*,x^*_j)=\max\{\,u^j(x^*,\xi_j) : \xi_j\in S^j(x^*)\,\},
--   $$
--
--   with the maximum attained at the feasible strategy $x^*_j\in S^j(x^*)$; that is, $x^*_j\in S^j(x^*)$ and $u^j(x^*,\xi_j)\le u^j(x^*,x^*_j)$ for all $\xi_j\in S^j(x^*)$.
--
--   Abstract economies (generalized games) extend $N$-person games by letting the feasible strategies of each individual depend on the choices of all. The paper derives the existence of an equilibrium (Theorem 3.4) from its Theorem 3.1.
--
--   **Formalization Note** The structure `AbstractEconomy N d` stores the sets `X j ⊆ EuclideanSpace ℝ (Fin (d j))`, the correspondences `S j` and the utilities `u j` as total functions of the whole profile (product type `Profile d`), together with the field `S_subset`: $S^j(x)\subseteq X^j$ for $x\in X$. Values off $X$ never enter a statement. $S^j(x)$ and $u^j(x,\cdot)$ may depend on the individual's own coordinate $x_j$, as in the paper. The equilibrium requires $x^*_j\in S^j(x^*)$, which is Debreu's definition (the paper's reference [7]) and the meaning of "the maximum over $S^j(x^*)$ equals $u^j(x^*,x^*_j)$".
--
--   Differences from the source:
--   - reading: the equilibrium maximum → feasible attainment at x*_j and comparison with every feasible ξ; reason: the proof of Theorem 3.4 produces x* ∈ ∏_j S^j(x*) before the utility inequalities (p. 217), so it establishes feasibility as well as the printed maximum equality.
--   - encoding: S^j and u^j defined on X and X × X^j → total functions, with S_subset and all uses restricted to those domains; reason: every source function extends to these ambient types and off-domain values are irrelevant. The finite index set is encoded by [Fintype N].
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 216, Section 3 (abstract economy and equilibrium point, before Theorem 3.4)

import Mathlib

namespace ChanPangGQVI.Existence.Supplement

/-- The space of strategy profiles `x = (x_j)_{j ∈ N}` with `x_j ∈ ℝ^{n_j}` (Chan and Pang 1982,
p. 216: `X = ∏_{j ∈ N} X^j` lies in it). It carries the product topology and the componentwise
vector-space structure. -/
abbrev Profile {N : Type*} (d : N → ℕ) : Type _ :=
  ∀ j : N, EuclideanSpace ℝ (Fin (d j))

/-- Chan and Pang 1982, p. 216, §3: an *abstract economy* is a family of triples
`{(X^j, S^j, u^j)}_{j ∈ N}`, where `N` is a finite set of individuals, `X^j ⊆ ℝ^{n_j}` is the
strategy set of individual `j`, `u^j : X × X^j → ℝ` with `X = ∏_{j ∈ N} X^j` is the utility
function of `j`, and `S^j : X → X^j` is the feasibility correspondence.

Lean representation: `[Fintype N]` encodes the finite set of individuals.
`S j` and `u j` are total functions on profiles; only their values on `X`
(resp. `X × X^j`) enter any statement. The field `S_subset` is the typing `S^j : X → X^j`:
`S^j(x) ⊆ X^j` for every `x ∈ X`. Note that `S^j(x)` and `u^j(x, ·)` may depend on the whole
profile `x`, including the individual's own coordinate `x_j`. -/
structure AbstractEconomy (N : Type*) [Fintype N] (d : N → ℕ) where
  /-- The strategy sets `X^j ⊆ ℝ^{n_j}`. -/
  X : ∀ j : N, Set (EuclideanSpace ℝ (Fin (d j)))
  /-- The feasibility correspondences `S^j : X → X^j`. -/
  S : ∀ j : N, Profile d → Set (EuclideanSpace ℝ (Fin (d j)))
  /-- The utility functions `u^j : X × X^j → ℝ`. -/
  u : ∀ j : N, Profile d → EuclideanSpace ℝ (Fin (d j)) → ℝ
  /-- `S^j` maps `X` into subsets of `X^j`. -/
  S_subset : ∀ j : N, ∀ x ∈ Set.univ.pi X, S j x ⊆ X j

namespace AbstractEconomy

variable {N : Type*} [Fintype N] {d : N → ℕ}

/-- The set `X = ∏_{j ∈ N} X^j` of strategy profiles of the economy. -/
def profiles (G : AbstractEconomy N d) : Set (Profile d) :=
  Set.univ.pi G.X

/-- Chan and Pang 1982, p. 216: an *equilibrium point* of the economy is a vector `x* ∈ X` with
`u^j(x*, x*_j) = max{u^j(x*, ξ_j) : ξ_j ∈ S^j(x*)}` for every `j ∈ N`, i.e. `x*_j ∈ S^j(x*)` and
`u^j(x*, ξ) ≤ u^j(x*, x*_j)` for every `ξ ∈ S^j(x*)` (Debreu's definition, which the paper
recalls; the maximum is attained at the feasible point `x*_j`). -/
def IsEquilibriumPoint (G : AbstractEconomy N d) (x : Profile d) : Prop :=
  x ∈ G.profiles ∧ ∀ j : N, x j ∈ G.S j x ∧ ∀ ξ ∈ G.S j x, G.u j x ξ ≤ G.u j x (x j)

end AbstractEconomy

end ChanPangGQVI.Existence.Supplement


