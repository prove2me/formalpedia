-- Prove2me | Definitions.Def_NewtonLCP_Supplement_MaxCut
-- name    : NewtonLCP_Supplement_MaxCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:16:38.076424+00:00
-- url     : https://prove2.me/theorems/d3bead98-e630-47b9-9d60-a87bd6a89706
-- title:
--   Max-Cut, graph codes and polynomial-time multiplicative value approximation
-- statement:
--   For a finite simple undirected graph $G=(V,E)$,
--
--   $$\mathrm{maxcut}(G)=\max_{S\subseteq V}\big|\{\{i,j\}\in E:\ |\{i,j\}\cap S|=1\}\big|,$$
--
--   the maximum number of edges between $S$ and $V\setminus S$; it is $0$ for an edgeless graph. A graph on $\{0,\dots,n-1\}$ is encoded by the code of $n$ followed by its upper-triangular adjacency bits.
--
--   Let a class of instances, a value $v(I)$ and a fixed real $\alpha\ge1$ be given. A **polynomial-time multiplicative $\alpha$-approximation** of $v$ on the class is a polynomial-time computable map that sends the code of every instance $I$ of the class to the code of a rational number $y$ with
--
--   $$\frac{v(I)}{\alpha}\le y\le v(I)\qquad\text{(from below)},\qquad\text{resp.}\qquad v(I)\le y\le \alpha\,v(I)\qquad\text{(from above)}.$$
--
--   These notions state Theorem 1.4.
--
--   **Formalization Note** Polynomial time is the published `CookPvsNP.PolyTimeComputable` on binary strings. The approximation is of the value: the output is a number, not a cut. Both conventions are defined because the paper does not fix one.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 1.4 and the Max-Cut problem, p.4; §7.2, pp.26–28

import Mathlib
import Definitions.Def_NewtonLCP_Supplement_Complexity

namespace NewtonLCP.Supplement

/-!
# Max-Cut, graph encodings and polynomial-time multiplicative value approximation

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8),
Theorem 1.4 and the Max-Cut problem, p.4; §7.2, pp.26–28.

* `maxcut(G) = max_{S ⊆ V} |{edges with exactly one end in S}|` for an undirected graph
  `G = (V, E)` (p.4).
* A **polynomial-time multiplicative α-approximation** (`α ≥ 1` a fixed real) of a value `v` on a
  class of instances is a polynomial-time computable map `f` from codes of instances to codes of
  rationals such that, for every instance `I` of the class, `f(code I)` is the code of a rational
  `y` with `v(I)/α ≤ y ≤ v(I)` (`IsLowerApprox`) resp. `v(I) ≤ y ≤ α·v(I)` (`IsUpperApprox`).

**Formalization Note.**
* A graph is a `SimpleGraph (Fin n)` (finite, undirected, loopless, no multiple edges); every
  `n ≥ 0`, connected or not. Edges are counted once as pairs `i < j`. `maxcut` is `0` for an
  edgeless graph.
* `encGraph G` is `encNat n` followed by the upper-triangular adjacency bits `[i ~ j]` for
  `i < j` in row-major order (adjacency decided classically). It is injective.
* Polynomial-time computability is the published `CookPvsNP.PolyTimeComputable` over the binary
  alphabet. The approximation is of the **value**: the output is a number, not a solution.
-/

open Classical in
/-- Code of a finite simple graph on `Fin n`: `n`, then the bits `[i ~ j]` for `i < j`. -/
noncomputable def encGraph {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool :=
  encNat n ++ (List.finRange n).flatMap (fun i =>
    (List.finRange n).flatMap (fun j => if i < j then [decide (G.Adj i j)] else []))

open Classical in
/-- `maxcut(G)`: the maximum over `S ⊆ V` of the number of edges with exactly one end in `S`. -/
noncomputable def maxcut {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ : Finset (Finset (Fin n))).sup (fun S =>
    ((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ (p.1 ∈ S ↔ p.2 ∉ S))).card)

/-- `f` is a polynomial-time multiplicative `α`-approximation of `v` on the instances satisfying
`dom`, from below: `v(I)/α ≤ y ≤ v(I)`. -/
def IsLowerApprox {X : Type} (enc : X → List Bool) (dom : X → Prop) (v : X → ℝ) (α : ℝ)
    (f : List Bool → List Bool) : Prop :=
  CookPvsNP.PolyTimeComputable f ∧
    ∀ I, dom I → ∃ y : ℚ, f (enc I) = encQ y ∧ v I / α ≤ (y : ℝ) ∧ (y : ℝ) ≤ v I

/-- `f` is a polynomial-time multiplicative `α`-approximation of `v` on the instances satisfying
`dom`, from above: `v(I) ≤ y ≤ α·v(I)`. -/
def IsUpperApprox {X : Type} (enc : X → List Bool) (dom : X → Prop) (v : X → ℝ) (α : ℝ)
    (f : List Bool → List Bool) : Prop :=
  CookPvsNP.PolyTimeComputable f ∧
    ∀ I, dom I → ∃ y : ℚ, f (enc I) = encQ y ∧ v I ≤ (y : ℝ) ∧ (y : ℝ) ≤ α * v I

end NewtonLCP.Supplement


