-- Prove2me | Definitions.Def_ExtensionComplexity_TSP_CutCor
-- name    : ExtensionComplexity_TSP_CutCor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:08:16.876603+00:00
-- url     : https://prove2.me/theorems/7ab3cd94-2886-415c-853e-a8175952c6a7
-- title:
--   The complete graph $K_n$, the cut polytope $\mathrm{CUT}(n)$ and the correlation polytope $\mathrm{COR}(n)$
-- statement:
--   Let $K_n=(V_n,E_n)$ be the complete graph on $n$ vertices, with edges the unordered pairs $\{u,v\}$, $u\neq v$. For $F\subseteq E_n$ the **characteristic vector** $\chi^F\in\mathbb R^{E_n}$ has $\chi^F_e=1$ if $e\in F$ and $0$ otherwise. For $X\subseteq V_n$ the **cut** $\delta(X)$ is the set of edges with one endpoint in $X$ and the other in its complement.
--
--   1. The **cut polytope** is
--   $$\mathrm{CUT}(n):=\mathrm{conv}\{\chi^{\delta(X)}\in\mathbb R^{E_n} : X\subseteq V_n\}.$$
--   2. The **correlation polytope** (Boolean quadric polytope) is the convex hull of the rank-one binary symmetric $n\times n$ matrices,
--   $$\mathrm{COR}(n):=\mathrm{conv}\{bb^\top\in\mathbb R^{n\times n} : b\in\{0,1\}^n\}.$$
--
--   The two polytopes are linearly isomorphic (Theorem 5) and both have extension complexity $2^{\Omega(n)}$ (Theorem 7); the correlation polytope is the source of every lower bound in the paper's reductions.
--
--   **Formalization Note** The vertex set $V_n$ is `Fin n` and the edge type `Edge n` is the subtype of `Sym2 (Fin n)` of non-diagonal unordered pairs, so $\mathbb R^{E_n}$ has one coordinate per edge (not per ordered pair). $\mathbb R^{n\times n}$ is `Fin n × Fin n → ℝ`.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:11, §3.2 (K_n, δ(X), χ^F, CUT(n)); p. 17:12 (COR(n))

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_CorrelationMatrix

namespace ExtensionComplexity.TSP

/-- The edge set `E_n` of the complete graph `K_n` on the vertex set `V_n = Fin n`: unordered pairs
`{u, v}` with `u ≠ v`. `ℝ^{E_n}` is `Edge n → ℝ`. -/
abbrev Edge (n : ℕ) : Type := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- The characteristic vector `χ^F ∈ ℝ^{E_n}` of a set `F` of edges (p. 17:11):
`χ^F_e = 1` if `e ∈ F` and `0` otherwise. -/
noncomputable def charVec {n : ℕ} (F : Set (Edge n)) : Edge n → ℝ :=
  open Classical in fun e => if e ∈ F then 1 else 0

/-- The cut `δ(X)` of `X ⊆ V_n` (p. 17:11): the edges of `K_n` with one endpoint in `X` and the
other in its complement. -/
def cutSet {n : ℕ} (X : Finset (Fin n)) : Set (Edge n) :=
  {e | ∃ u v : Fin n, u ∈ X ∧ v ∉ X ∧ e.1 = s(u, v)}

/-- The **cut polytope** (p. 17:11): `CUT(n) := conv{χ^{δ(X)} ∈ ℝ^{E_n} | X ⊆ V_n}`. -/
noncomputable def cutPolytope (n : ℕ) : Set (Edge n → ℝ) :=
  convexHull ℝ (Set.range fun X : Finset (Fin n) => charVec (cutSet X))

/-- The **correlation polytope** (Boolean quadric polytope) (p. 17:12):
`COR(n) := conv{bbᵀ ∈ ℝ^{n×n} | b ∈ {0,1}^n}`; `ℝ^{n×n}` is `Fin n × Fin n → ℝ`. -/
noncomputable def corPolytope (n : ℕ) : Set (Fin n × Fin n → ℝ) :=
  convexHull ℝ (Set.range fun b : Fin n → Bool => outerBits b)

end ExtensionComplexity.TSP


