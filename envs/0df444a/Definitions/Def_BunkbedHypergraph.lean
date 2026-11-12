-- Prove2me | Definitions.Def_BunkbedHypergraph
-- name    : BunkbedHypergraph
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-09-11T16:15:44.797295+00:00
-- url     : https://prove2.me/theorems/0ca9c607-2a8c-49e4-9156-6c819fef7974
-- title:
--   Hypergraph percolation, Hollom's hypergraph, and the Wierman-Ziff model
-- statement:
--   This file supplies the hypergraph side of the argument: hypergraph percolation, Hollom's example, and the Wierman–Ziff model.
--
--   A **hypergraph** is a finite family of hyperedges, each a set of vertices. As with graphs one forms the **bunkbed hypergraph** over a transversal set $T$, with two levels and posts above $T$.
--
--   In the **alternative** bunkbed hypergraph percolation, each hyperedge $e$ is retained on exactly one of the two levels and deleted on the other, the choice being a fair coin, independently across hyperedges. For a hypergraph with $k$ hyperedges there are therefore $2^k$ equally likely configurations. Two vertices are connected when a path joins them, where all vertices of a retained hyperedge are mutually connected and posts may be used freely.
--
--   **Hollom's hypergraph** $H$ is the $3$-uniform hypergraph on $u_1, \dots, u_{10}$ with the six hyperedges
--
--   $$\{u_2,u_1,u_3\},\quad \{u_9,u_3,u_6\},\quad \{u_7,u_6,u_5\},\quad \{u_2,u_5,u_4\},\quad \{u_7,u_4,u_8\},\quad \{u_9,u_8,u_{10}\},$$
--
--   with transversal set $T = \{u_2, u_7, u_9\}$. Each hyperedge contains exactly one transversal vertex, which is listed first.
--
--   The **Wierman–Ziff model** refines hyperedge percolation. Rather than being simply present or absent, a hyperedge $(a,b,c)$ takes one of five states — it connects all three vertices, exactly one of the three pairs, or none — with prescribed probabilities summing to $1$, independently across hyperedges. Ordinary hypergraph percolation is the special case in which only the all-three and none states occur. This extra freedom is what lets a hyperedge be *approximated* by a gadget graph, which is the crux of the whole argument, since a hyperedge cannot be simulated exactly.
--
--   **Formalization Note** Hyperedges are ordered triples, so that the distinguished transversal vertex is the first coordinate, matching the ordering the source fixes along its path $\rho$. The five WZ states are an inductive type with a `Fintype` instance, and a state determines which pairs of its hyperedge's vertices are linked at a given level. Hollom's hypergraph and the alternative-model probabilities were validated by direct computation: they reproduce $\mathbb{P}^{\mathrm{alt}}[u_1 \leftrightarrow u_{10}] = 12/64$ and $\mathbb{P}^{\mathrm{alt}}[u_1 \leftrightarrow u'_{10}] = 13/64$, exactly the values of Lemma 3.1.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, "The bunkbed conjecture is false", Proc. Natl. Acad. Sci. USA 122 (2025), no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122 - Section 3 (hypergraph percolation, Hollom's example Fig. 1, Definition 3.2 of the WZ model); hyperedge ordering from Eq. [5] on p. 5.

import Definitions.Def_BunkbedPercolation

/-!
# Hypergraph percolation, Hollom's example, and the Wierman–Ziff model

Section 3 of Gladkov–Pak–Zimin, *The bunkbed conjecture is false*, PNAS 122 (2025) e2420725122.
-/

namespace Bunkbed.Hyper

open Bunkbed SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The underlying vertex set of an ordered hyperedge `(a,b,c)`. -/
def tripleSet (t : V × V × V) : Finset V := {t.1, t.2.1, t.2.2}

/-- All edges of the clique on `s`, placed at level `l` of the bunkbed. -/
def cliqueAt (s : Finset V) (l : Fin 2) : Finset (Sym2 (V × Fin 2)) :=
  ((s ×ˢ s).filter (fun p => p.1 ≠ p.2)).image (fun p => s((p.1, l), (p.2, l)))

/-- The vertical posts over the transversal set `T`; these are always retained. -/
def posts (T : Finset V) : Finset (Sym2 (V × Fin 2)) := T.image (fun t => s((t, 0), (t, 1)))

/-! ## Alternative bunkbed hypergraph percolation -/

/-- In the **alternative** model each hyperedge `i` is retained on exactly one of the two
levels — `σ i` — and deleted on the other. Posts over `T` are always present. -/
abbrev altBBGraph {ι : Type*} [Fintype ι] (e : ι → Finset V) (T : Finset V) (σ : ι → Fin 2) :
    SimpleGraph (V × Fin 2) :=
  ofEdges ((Finset.univ.biUnion (fun i => cliqueAt (e i) (σ i))) ∪ posts T)

/-- `ℙᵃˡᵗ[x ↔ y]`: all `2^{|ι|}` level-assignments are equally likely. -/
def altProb {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → Finset V) (T : Finset V)
    (x y : V × Fin 2) : ℚ :=
  (∑ σ : ι → Fin 2, if (altBBGraph e T σ).Reachable x y then (1 : ℚ) else 0)
    / 2 ^ Fintype.card ι

/-! ## Hollom's 3-uniform hypergraph (Fig. 1)

Ordered as in the path `ρ` of Eq. [5], so that in each hyperedge `(a,b,c)` the first vertex
`a` is the transversal one. Vertices `uᵢ ↦ i-1`, so `u₁ = 0`, …, `u₁₀ = 9`. -/
def hollomTriple : Fin 6 → (Fin 10 × Fin 10 × Fin 10) :=
  ![(1, 0, 2), (8, 2, 5), (6, 5, 4), (1, 4, 3), (6, 3, 7), (8, 7, 9)]

/-- The six hyperedges of Hollom's hypergraph, as vertex sets. -/
def hollomE (i : Fin 6) : Finset (Fin 10) := tripleSet (hollomTriple i)

/-- Hollom's transversal set `T = {u₂, u₇, u₉}`. -/
def hollomT : Finset (Fin 10) := {1, 6, 8}

/-! ## The Wierman–Ziff five-state model -/

/-- The five states of a hyperedge `(a,b,c)` in the WZ model: which of its vertices the
hyperedge connects. -/
inductive WZ | abc | ab_c | ac_b | a_bc | a_b_c
  deriving DecidableEq, Repr

instance : Fintype WZ := ⟨{.abc, .ab_c, .ac_b, .a_bc, .a_b_c}, by intro x; cases x <;> decide⟩

/-- The pairs of vertices that state `s` links, for the hyperedge `t = (a,b,c)` at level `l`. -/
def WZ.edges (s : WZ) (t : V × V × V) (l : Fin 2) : Finset (Sym2 (V × Fin 2)) :=
  let a : V × Fin 2 := (t.1, l)
  let b : V × Fin 2 := (t.2.1, l)
  let c : V × Fin 2 := (t.2.2, l)
  match s with
  | .abc   => {s(a, b), s(b, c), s(a, c)}
  | .ab_c  => {s(a, b)}
  | .ac_b  => {s(a, c)}
  | .a_bc  => {s(b, c)}
  | .a_b_c => ∅

/-- The graph realised by a WZ configuration `ψ`, which assigns a state to each hyperedge on
each of the two levels. Posts over `T` are always present. -/
abbrev wzGraph {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → (V × V × V)) (T : Finset V)
    (ψ : ι × Fin 2 → WZ) : SimpleGraph (V × Fin 2) :=
  ofEdges ((Finset.univ.biUnion (fun p : ι × Fin 2 => (ψ p).edges (t p.1) p.2)) ∪ posts T)

/-- `ℙʷᶻ[x ↔ y]`, where each hyperedge on each level independently takes state `s` with
probability `P s`.

⚠️ This carries **no internal normalisation**: `P` is an arbitrary `WZ → ℚ`, so the total mass
is `(∑ s, P s) ^ (2 * |ι|)`. Comparing two values of `wzProb` is only meaningful when the caller
supplies a genuine distribution, i.e. `0 ≤ P s` for every `s` and `∑ s, P s = 1`. (Contrast
`altProb`, which normalises internally and always lands in `[0,1]`.) -/
def wzProb {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → (V × V × V)) (T : Finset V)
    (P : WZ → ℚ) (x y : V × Fin 2) : ℚ :=
  ∑ ψ : ι × Fin 2 → WZ,
    (if (wzGraph t T ψ).Reachable x y then (1 : ℚ) else 0) * ∏ p : ι × Fin 2, P (ψ p)

end Bunkbed.Hyper


