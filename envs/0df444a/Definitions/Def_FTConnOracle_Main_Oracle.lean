-- Prove2me | Definitions.Def_FTConnOracle_Main_Oracle
-- name    : FTConnOracle_Main_Oracle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:26:31.492372+00:00
-- url     : https://prove2.me/theorems/9c991b20-dafc-4cdd-a3bb-fdcbd2abb44f
-- title:
--   Crossing edge sets, f-bounded deterministic component oracles with b-bit encodings, and f-cut compatibility
-- statement:
--   Throughout, $G$ is a simple undirected graph on the labeled vertex set $[n]$ (in Lean `Fin n`), and edges are unordered pairs $\{u,v\}$. For an edge set $E$ and $S\subseteq[n]$, the **crossing edges** of $E$ are the edges with exactly one endpoint in $S$; for a graph $G$,
--
--   $$\delta_G(S)=\{\{u,v\}\in E(G):u\in S,\ v\notin S\}.$$
--
--   For $F\subseteq E(G)$, $G-F$ is $G$ with the edges of $F$ deleted, and $\mathrm{cc}(G-F)$ is its partition into connected components, represented by the reachability relation of $G-F$ on all of $[n]$ (isolated vertices included). An edge set $F$ is a **valid query** for $G$ when $F\subseteq E(G)$.
--
--   A **deterministic component oracle on $[n]$ for at most $f$ failures with $b$ bits** is a pair of maps $\mathrm{Enc}:\{\text{graphs on }[n]\}\to\{0,1\}^b$ and $\mathrm{Dec}:\{0,1\}^b\times\{\text{edge sets on }[n]\}\to\{\text{relations on }[n]\}$ such that
--
--   $$\mathrm{Dec}(\mathrm{Enc}(G),F)=\mathrm{cc}(G-F)\quad\text{for every }G\text{ and every }F\subseteq E(G)\text{ with }|F|\le f.$$
--
--   The decoder sees only the encoding and $F$, never $G$; nothing is required of it on queries that are not valid, and no computability is required of either map.
--
--   More generally, an encoding $\mathrm{Enc}$ of the graphs on $[n]$ into any set **admits an exact component decoder for failure of at most $f$ edges** if some decoder $\mathrm{Dec}$ (a function of $\mathrm{Enc}(G)$ and $F$ only) satisfies the display above. It is **$f$-cut compatible** (Definition 2.1) if for every ordered pair of graphs $G,H$ on $[n]$ with $\mathrm{Enc}(G)=\mathrm{Enc}(H)$ and every $S\subseteq[n]$,
--
--   $$\delta_G(S)\subseteq E(H)\ \text{ and }\ |\delta_G(S)|\le f\ \Longrightarrow\ \delta_H(S)=\delta_G(S).\qquad(2.1)$$
--
--   These are the objects of Theorem 1.1, clause (i), and of Observation 2.1.
--
--   **Formalization Note.** `edges G` is $E(G)$ as a `Finset (Sym2 (Fin n))`, `cutEdges E S` the crossing edges of an edge set, `delta G S` $=\delta_G(S)$, `removeEdges G F` $=G-F$ (`SimpleGraph.deleteEdges`). Encodings in `FTOracle n f b` are fixed-length bit strings `Fin b → Bool`.
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), pp. 4–6 (PDF 6–8), §2 'Model and notation', §2.1, Definition 2.1 (2.1)

import Mathlib

namespace FTConnOracle.Main

/-!
# Crossing edge sets, f-bounded component oracles, f-cut compatibility

Parter, Tzalik, *Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space*,
STOC 2027 submission (manuscript sha256 168306b7…), pp. 4–6 (PDF 6–8), §2, §2.1, Definition 2.1.

* Graphs are simple undirected graphs on the labeled vertex set `[n]`, here `Fin n`; edges are
  unordered pairs `Sym2 (Fin n)`.
* `edges G` is the edge set `E(G)`, `cutEdges E S` the edges of `E` with exactly one endpoint in
  `S`, and `delta G S` is `δ_G(S)`. `removeEdges G F` is `G − F`.
* A component oracle with `b` bits for at most `f` failures is an encoder from graphs to
  `{0,1}^b` (`Fin b → Bool`) and a decoder that sees only the encoding and the query `F`; it must
  return the reachability relation of `G − F` (the component partition `cc(G − F)`, isolated
  vertices included) for every valid query `F ⊆ E(G)` with `|F| ≤ f`. Nothing is required on
  other queries, and no computability is required of either map.
-/

open Classical in
/-- The edge set `E(G)` of a graph `G` on `[n]`, as a finite set of unordered pairs. -/
noncomputable def edges {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => e ∈ G.edgeSet

open Classical in
/-- The edges of the edge set `E` crossing the cut `(S, [n] ∖ S)`: those `{u, v} ∈ E` with
`u ∈ S` and `v ∉ S`. -/
noncomputable def cutEdges {n : ℕ} (E : Finset (Sym2 (Fin n))) (S : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  E.filter fun e => ∃ u ∈ S, ∃ v, v ∉ S ∧ e = s(u, v)

/-- `δ_G(S)`: the set of edges of `G` crossing `(S, [n] ∖ S)`. -/
noncomputable def delta {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  cutEdges (edges G) S

/-- `G − F`: the graph `G` with the edges of `F` deleted (same vertex set `[n]`). -/
def removeEdges {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n))) :
    SimpleGraph (Fin n) :=
  G.deleteEdges (F : Set (Sym2 (Fin n)))

/-- A deterministic component oracle on `[n]` with `b`-bit encodings for at most `f` failures:
`enc G ∈ {0,1}^b` depends on `G` only; `dec` sees only the encoding and the query `F`, and returns
the reachability relation of `G − F` for every valid query `F ⊆ E(G)` with `|F| ≤ f`. -/
structure FTOracle (n f b : ℕ) where
  /-- The encoder, a function of the graph only. -/
  enc : SimpleGraph (Fin n) → (Fin b → Bool)
  /-- The decoder, a function of the encoding and the failure set only. -/
  dec : (Fin b → Bool) → Finset (Sym2 (Fin n)) → (Fin n → Fin n → Prop)
  /-- Correctness on every valid query with at most `f` failures. -/
  correct : ∀ (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n))),
    F ⊆ edges G → F.card ≤ f → dec (enc G) F = (removeEdges G F).Reachable

/-- An encoding `Enc` of the graphs on `[n]` (into any set `α`) **admits an exact component
decoder for failure of at most `f` edges** if some decoder, seeing only `Enc G` and `F`, returns
the component partition of `G − F` for every graph `G` and every `F ⊆ E(G)` with `|F| ≤ f`. -/
def AdmitsDecoder {n : ℕ} {α : Type} (Enc : SimpleGraph (Fin n) → α) (f : ℕ) : Prop :=
  ∃ Dec : α → Finset (Sym2 (Fin n)) → (Fin n → Fin n → Prop),
    ∀ (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n))),
      F ⊆ edges G → F.card ≤ f → Dec (Enc G) F = (removeEdges G F).Reachable

/-- Definition 2.1 (p. 6): `Enc` is **`f`-cut compatible** if for every ordered pair of graphs
`G, H` on `[n]` with `Enc G = Enc H` and every `S ⊆ [n]`,
`δ_G(S) ⊆ E(H)` and `|δ_G(S)| ≤ f` imply `δ_H(S) = δ_G(S)` (2.1). -/
def IsCutCompatible {n : ℕ} {α : Type} (Enc : SimpleGraph (Fin n) → α) (f : ℕ) : Prop :=
  ∀ G H : SimpleGraph (Fin n), Enc G = Enc H → ∀ S : Finset (Fin n),
    delta G S ⊆ edges H → (delta G S).card ≤ f → delta H S = delta G S

end FTConnOracle.Main


