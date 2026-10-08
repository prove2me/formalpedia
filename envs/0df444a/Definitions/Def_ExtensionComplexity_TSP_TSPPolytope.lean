-- Prove2me | Definitions.Def_ExtensionComplexity_TSP_TSPPolytope
-- name    : ExtensionComplexity_TSP_TSPPolytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:24:57.241876+00:00
-- url     : https://prove2.me/theorems/ba9dba08-b6f6-479e-bb1e-f23eb19adab0
-- title:
--   Tours of $K_n$ and the TSP polytope $\mathrm{TSP}(n)$
-- statement:
--   A set $F\subseteq E_n$ of edges of the complete graph $K_n$ is a **tour** if it is the edge set of a Hamiltonian cycle of $K_n$, a cycle passing through every vertex exactly once. The **traveling salesman polytope** is
--
--   $$\mathrm{TSP}(n):=\mathrm{conv}\{\chi^F\in\mathbb R^{E_n} : F\subseteq E_n \text{ is a tour of } K_n\}.$$
--
--   Optimizing a linear function over $\mathrm{TSP}(n)$ is the symmetric traveling salesman problem; the main theorem of the mission says that no linear program of subexponential size projects onto it.
--
--   **Formalization Note** A tour is the edge set of a closed walk `c` in the complete simple graph on `Fin n` with `c.IsHamiltonianCycle` (Mathlib). For $n\le 2$ there is no tour and $\mathrm{TSP}(n)=\emptyset$; the main theorem is asymptotic and is unaffected.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:14, §3.4 (TSP(n))

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_CutCor

namespace ExtensionComplexity.TSP

/-- A set `F ⊆ E_n` of edges is a **tour** of `K_n` (p. 17:14) if it is the edge set of a
Hamiltonian cycle of the complete graph `K_n = (⊤ : SimpleGraph (Fin n))`. For `n ≤ 2` there is no
tour. -/
def IsTour {n : ℕ} (F : Set (Edge n)) : Prop :=
  ∃ (v : Fin n) (c : (⊤ : SimpleGraph (Fin n)).Walk v v),
    c.IsHamiltonianCycle ∧ ∀ e : Edge n, e ∈ F ↔ e.1 ∈ c.edges

/-- The **TSP polytope** (p. 17:14):
`TSP(n) := conv{χ^F ∈ ℝ^{E_n} | F ⊆ E_n is a tour of K_n}`. -/
noncomputable def tspPolytope (n : ℕ) : Set (Edge n → ℝ) :=
  convexHull ℝ {x | ∃ F : Set (Edge n), IsTour F ∧ x = charVec F}

end ExtensionComplexity.TSP


