-- Prove2me | Definitions.Def_RandomOrderCRS_FractionalMatching
-- name    : RandomOrderCRS_FractionalMatching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:20:26.334133+00:00
-- url     : https://prove2.me/theorems/52aaf7da-759e-4f2a-b71e-a4266e6bac70
-- title:
--   Fractional matchings and 1-regular inputs
-- statement:
--   Let $G=(V,E)$ be a finite simple graph. For a vertex $v$, write $\partial(v)$ for the set of edges incident to $v$. A vector $x\in[0,1]^E$ is a **fractional matching** of $G$, i.e. it lies in the matching polytope $\mathcal P_G$, if
--
--   $$\sum_{e\in\partial(v)}x_e\le1\qquad\text{for all }v\in V.$$
--
--   The pair $(G,x)$ is a **1-regular input** if each of these constraints holds with equality.
--
--   These are the inputs of every contention resolution scheme in this mission: Theorem 3 of the paper concerns 1-regular inputs, and its reduction Lemma EC.1 turns every input into a 1-regular one.
--
--   **Formalization Note** The vector $x$ is a function on all unordered pairs of vertices, `Sym2 V → ℝ`, that vanishes off the edges. So $x_{(w,v)}$ can be written with no case split, and it is $0$ when $(w,v)$ is not an edge. Edges with $x_e=0$ remain edges. The fractional degree of $v$ is `fracDegree G x v`.
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, §1.1, p.3 (matching polytope, fractional matching); Definition 4, p.16 (1-regular)

import Mathlib

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The fractional degree `∑_{e ∈ ∂(v)} x_e` of a vertex `v`, MacRury, Ma & Grammel, *On
(Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite)
Graphs*, arXiv:2209.07520v2, §1.1, p.3.

**Formalization Note.** `∂(v)` is `G.incidenceFinset v`, and `x` is a function on all of `Sym2 V`. -/
noncomputable def fracDegree (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ) (v : V) :
    ℝ :=
  ∑ e ∈ G.incidenceFinset v, x e

/-- `x` is a fractional matching of `G`, i.e. `x` lies in the matching polytope `𝒫_G`:
"A vector x ∈ [0, 1]^E lies in the matching polytope of G ... if ∑_{e∈∂(v)} x_e ≤ 1 for all
v ∈ V", arXiv:2209.07520v2, §1.1, p.3.

**Formalization Note.** Graphs are finite simple graphs `SimpleGraph V`, with edges `G.edgeSet`.
The vector `x` is a function `Sym2 V → ℝ` that vanishes off the edges. Hence `x s(w, v)` is the
paper's `x_{fᶜ}` with no case split, and it is `0` when `fᶜ` is not an edge. Edges with `x_e = 0`
remain edges. -/
def IsFractionalMatching (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ) : Prop :=
  (∀ e, 0 ≤ x e ∧ x e ≤ 1) ∧ (∀ e, e ∉ G.edgeSet → x e = 0) ∧ ∀ v, fracDegree G x v ≤ 1

/-- `(G, x)` is a 1-regular input: "if x = (x_e)_{e∈E} satisfies constraints ∑_{e∈∂(v)} x_e ≤ 1
for all v ∈ V as equality, then we then say that G is 1-regular (with respect to x)",
arXiv:2209.07520v2, Definition 4, p.16.

**Formalization Note.** A vertex with no incident edge has fractional degree `0`, so a 1-regular
input has no isolated vertex; this is what the paper's condition says. -/
def IsOneRegular (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ) : Prop :=
  (∀ e, 0 ≤ x e ∧ x e ≤ 1) ∧ (∀ e, e ∉ G.edgeSet → x e = 0) ∧ ∀ v, fracDegree G x v = 1

theorem IsOneRegular.isFractionalMatching {G : SimpleGraph V} [DecidableRel G.Adj]
    {x : Sym2 V → ℝ} (h : IsOneRegular G x) : IsFractionalMatching G x :=
  ⟨h.1, h.2.1, fun v => (h.2.2 v).le⟩

end RandomOrderCRS


