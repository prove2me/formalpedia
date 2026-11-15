-- Prove2me | Definitions.Def_FlowOptimalSeparators_MinorFree_Supplement_InducedMinorFree
-- name    : FlowOptimalSeparators_MinorFree_Supplement_InducedMinorFree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:00:02.915615+00:00
-- url     : https://prove2.me/theorems/1b11ed51-baa7-4912-a65f-e5ceb39c7a19
-- title:
--   Induced-minor-freeness, touch probability of two random paths, and Theorem 3's input and output
-- statement:
--   Let $H$ be a finite simple graph with $a=|V(H)|$ vertices and $|E(H)|$ edges, and let $G$ be a finite simple graph with $n$ vertices and $m$ edges.
--
--   1. $G$ is **$H$-induced-minor-free** when $H$ is not an induced minor of $G$: there are no pairwise disjoint nonempty vertex sets $B_x$ ($x\in V(H)$), each inducing a connected subgraph of $G$, such that for distinct $x,y$ the sets $B_x,B_y$ are joined by an edge of $G$ exactly when $xy\in E(H)$.
--
--   2. Let $\pi$ be a probability distribution on $V(G)$ and, for each ordered pair $(u,v)$, let $\kappa(u,v,\cdot)$ be a probability distribution on simple $u$–$v$ paths (the one-vertex path $\{u\}$ when $u=v$). Sample $u,v$ independently from $\pi$ and then $P\sim\kappa(u,v,\cdot)$; let $P'$ be an independent copy. The **touch probability** is
--   $$\Pr\bigl[\exists x\in P,\ \exists x'\in P' :\ x=x'\ \text{or}\ xx'\in E(G)\bigr],$$
--   computed as a finite double sum over the path laws of $P$ and $P'$. It is at least the shared-vertex collision probability of the published definitions, and can be strictly larger.
--
--   3. The input of the Section 5 algorithm is the compressed adjacency array of $G$ with the parameter $h:=|V(H)|$, followed by the number $|E(H)|$.
--
--   4. A final machine state is a **valid output for Theorem 3** with constant $C_{\rm size}$ when its natural memory is the indicator vector of a vertex set $S$, every connected component $K$ of $G-S$ satisfies $4|K|\le 3n$, and, whenever $n\ge2$,
--   $$|S|\le C_{\rm size}\,\ln|V(H)|\,\sqrt{m\,(|V(H)|+|E(H)|)}.$$
--
--   These are the objects of Section 5 and Proposition 1 that the published definitions of the live mission do not provide.
--
--   **Formalization Note** At $n=1$ the right-hand side of the size bound is $0$ while the only balanced set is the vertex itself, so the size bound is imposed only for $n\ge2$.
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 3, 5, 19–20, Proposition 1; Section 5; Theorem 3

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_Connectors
import Definitions.Def_FlowOptimalSeparators_MinorFree_SeparatorOutput

set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree.Supplement

/-- `G` is `H`-induced-minor-free (Section 5, p.19): `H` is not an induced minor of `G`, in the
published adjacency-iff branch-set sense. `H` is any finite simple graph, labelled by `Fin a`. -/
def InducedMinorFree {a n : ℕ} (H : Graph a) (G : Graph n) : Prop :=
  ¬ MISInducedMinor.IsInducedMinor H G

/-- Proposition 1's event, p.5 and p.20: two independent endpoint-path samples `P`, `P'`
share a vertex or are joined by an edge of `G`. Same finite double sum over path lists as the
published `collisionProbability`, with the larger event. -/
noncomputable def touchProbability {n : ℕ} (G : Graph n) (π : Fin n → ℝ)
    (κ : Fin n → Fin n → List (Fin n) → ℝ) : ℝ := by
  classical
  exact ∑ P ∈ pathLists n, ∑ Q ∈ pathLists n,
    if ∃ v ∈ P, ∃ v' ∈ Q, v = v' ∨ G.Adj v v' then pathLaw π κ P * pathLaw π κ Q else 0

/-- Theorem 3's input: the published CSR array of `G` with `h := |V(H)|`, followed by `|E(H)|`.
The algorithm uses `H` only through these two numbers. -/
noncomputable def inducedInput {n a : ℕ} {G : Graph n} (A : AdjacencyInput G) (H : Graph a) :
    List ℕ :=
  A.encode a ++ [edgeCount H]

/-- Theorem 3's output, p.3 and p.20: a vertex mask whose set is a 3/4-balanced separator,
of size at most `Csize · ln|V(H)| · √(m(|V(H)|+|E(H)|))` whenever `n ≥ 2`. At `n = 1` the
right side is `0` while the single vertex must be removed, so only balance is required there. -/
noncomputable def InducedSeparatorOutput {n a : ℕ} (G : Graph n) (H : Graph a) (Csize : ℝ)
    (s : VehicleRoutingSurvey.Routing.ArithmeticState) : Prop :=
  IsVertexMask n s ∧ Balanced G (outputSet n s) ∧
    (2 ≤ n → ((outputSet n s).card : ℝ) ≤
      Csize * Real.log a * Real.sqrt ((edgeCount G : ℝ) * ((a : ℝ) + edgeCount H)))

end FlowOptimalSeparators.MinorFree.Supplement


