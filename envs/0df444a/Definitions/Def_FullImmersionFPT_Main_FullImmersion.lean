-- Prove2me | Definitions.Def_FullImmersionFPT_Main_FullImmersion
-- name    : FullImmersionFPT_Main_FullImmersion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:47:56.331371+00:00
-- url     : https://prove2.me/theorems/784c0ab5-34d2-4315-b4f6-385cc6e55a9e
-- title:
--   Labeled tour graphs, full immersions (Section 1) and the question of Theorem 1 (p. 2)
-- statement:
--   A **tour graph** is a connected 4-regular graph (loops and parallel edges allowed); it is **labeled** if its edges carry vectors of $\mathbb F_2^d$ for a fixed $d$. A labeled tour graph $H$ is a **full immersion** of a labeled tour graph $G$ if $H$ can be obtained from $G$ by a sequence of shiftings (add any $c\in\mathbb F_2^d$ to every edge of a cut $\delta(S)$) and of splittings off of vertices (one of the three pairings of the four half-edges at the vertex, excluding by footnote 2 the pairing of the two halves of a loop or of a 2-edge cut; the new edges carry the sums of the labels). $G$ **has a full immersion isomorphic to** $H$ if some full immersion of $G$ is isomorphic to $H$ by a graph isomorphism preserving the edge labels exactly (no change of basis of $\mathbb F_2^d$, no coordinate projection). The size of the target is
--   $$|H| = |V(H)| + d,$$
--   the number of vertices plus the dimension of the label space.
--
--   For the algorithm, a labeled graph is given as an edge list: $n$, $m$, $d$, then for every edge its two end vertices and its $d$ label bits. When $G$ is labeled in $\mathbb F_2^d$ and $H$ in $\mathbb F_2^{d'}$, the question "does $G$ have a full immersion isomorphic to $H$" requires $d=d'$.
--
--   **Formalization Note.** `IsLabeledTourGraph G lab` is: well-formed, 4-regular, connected (which includes non-empty), and both half-edges of an edge carry the same label. `Obtains G lab G' lab'` is the reflexive closure of shiftings (`shiftAt`) and legal splittings off (`splitOff`, `splitLabel`), each applied to a labeled tour graph. `CodeHasFullImmersionIso G K` is `∃ hd : d' = d, …` with `K`'s labels transported along `hd`.
-- source:
--   Barabash, Geelen, McCarty, McFarland, Wollan, Finding full immersions is fixed-parameter tractable in labeled tour graphs, STOC 2027 submission (manuscript of November 2, 2026, sha256 c071967d…), p. 2 (Section 1 and footnote 2)

import Mathlib
import Definitions.Def_FullImmersionFPT_Main_Machine

set_option autoImplicit false

/-!
# Labeled tour graphs, shifting, splitting off and full immersions (§1, p. 2)

Barabash, Geelen, McCarty, McFarland, Wollan, *Finding full immersions is fixed-parameter
tractable in labeled tour graphs* (STOC 2027 submission, manuscript of November 2, 2026), p. 2.

"A tour graph is a connected 4-regular graph, and it is labeled if its edges are labeled by binary
vectors of a fixed length. We allow tour graphs to have loops and parallel edges. We consider
labeled tour graphs up to the standard equivalence relation of shifting, which adds any binary
vector of the given length to every edge of a cut. Given a vertex v, there are three ways to pair
its four incident edges into two parts of size two. For each of these three ways, we can 'split
off' the two pairs of edges by combining them, thus removing v. We sum the labels of the paired
edges to obtain the label of the new edge … A labeled tour graph H is a full immersion of a
labeled tour graph G if H can be obtained from G by a sequence of shiftings and of splitting off
vertices." Footnote 2: "Technically, we pair the half-edges incident to v in order to handle
loops. Also, we do not allow two half-edges to be paired if they are part of the same loop or
2-edge cut." "|H| … is the number of vertices plus the dimension of the vector space in which it
is labeled. Isomorphisms of labeled tour graphs are just graph isomorphisms that preserve the edge
labels."

Labels live in `F₂^d = Fin d → ZMod 2`; a label is stored on both half-edges of its edge.
-/

namespace FullImmersionFPT.Main

open Classical

noncomputable section

variable {V H : Type}

/-- `(G, lab)` is a labeled tour graph with labels in `F₂^d`: a well-formed connected 4-regular
multigraph (loops and parallel edges allowed; connected includes non-empty) whose two half-edges of
each edge carry the same label. -/
def IsLabeledTourGraph {d : ℕ} (G : Multigraph V H) (lab : H → (Fin d → ZMod 2)) : Prop :=
  G.IsValid ∧ G.IsRegular 4 ∧ G.IsConnected ∧ ∀ h ∈ G.halves, lab (G.mate h) = lab h

/-- `(G', lab')` is obtained from the labeled tour graph `(G, lab)` by a sequence of shiftings
(`shiftAt`, at any vertex set `S` by any vector `c`) and of splittings off of vertices (`splitOff`
with a pairing of the four half-edges at the vertex that is legal by footnote 2). Every operation
is applied to a labeled tour graph. -/
inductive Obtains {d : ℕ} : Multigraph V H → (H → (Fin d → ZMod 2)) → Multigraph V H →
    (H → (Fin d → ZMod 2)) → Prop
  | refl (G : Multigraph V H) (lab : H → (Fin d → ZMod 2)) : Obtains G lab G lab
  | shift (G : Multigraph V H) (lab : H → (Fin d → ZMod 2)) (S : Finset V) (c : Fin d → ZMod 2)
      (G' : Multigraph V H) (lab' : H → (Fin d → ZMod 2)) :
      IsLabeledTourGraph G lab → Obtains G (G.shiftAt lab S c) G' lab' → Obtains G lab G' lab'
  | split (G : Multigraph V H) (lab : H → (Fin d → ZMod 2)) (v : V) (π : H → H)
      (G' : Multigraph V H) (lab' : H → (Fin d → ZMod 2)) :
      IsLabeledTourGraph G lab → v ∈ G.verts → G.IsPairingAt v π → G.IsLegalPairing v π →
      Obtains (G.splitOff v π) (G.splitLabel v π lab) G' lab' → Obtains G lab G' lab'

/-- `(G, lab)` has a full immersion isomorphic to `(K, lab')` (Section 1): some labeled tour graph
obtained from `(G, lab)` by shiftings and splittings off is isomorphic to `(K, lab')` by a
label-preserving graph isomorphism. -/
def HasFullImmersionIso {V' H' : Type} {d : ℕ} (G : Multigraph V H) (lab : H → (Fin d → ZMod 2))
    (K : Multigraph V' H') (lab' : H' → (Fin d → ZMod 2)) : Prop :=
  ∃ (G' : Multigraph V H) (l' : H → (Fin d → ZMod 2)),
    Obtains G lab G' l' ∧ Multigraph.IsIsoLabeled G' l' K lab'

/-- A labeled multigraph given as an edge list: `n` vertices, `m` edges, labels in `F₂^d`. -/
structure EdgeCode (n m d : ℕ) where
  ends : Fin m → Fin 2 → Fin n
  lab : Fin m → Fin d → ZMod 2

namespace EdgeCode

variable {n m d : ℕ}

/-- The multigraph of the code. -/
def graph (G : EdgeCode n m d) : Multigraph (Fin n) (Fin m × Fin 2) := ofEnds G.ends

/-- The labels of the code, on half-edges. -/
def label (G : EdgeCode n m d) : Fin m × Fin 2 → (Fin d → ZMod 2) := fun p => G.lab p.1

/-- The words of the code: `n, m, d`, then for every edge its two end vertices (in half-edge
order) and its `d` label bits. -/
def words (G : EdgeCode n m d) : List ℤ :=
  [(n : ℤ), (m : ℤ), (d : ℤ)] ++
    (List.finRange m).flatMap fun e =>
      [((G.ends e 0 : ℕ) : ℤ), ((G.ends e 1 : ℕ) : ℤ)] ++ vecWords (G.lab e)

end EdgeCode

/-- The question of Theorem 1 for codes `G` (labels in `F₂^d`) and `K` (labels in `F₂^{d'}`):
the label spaces agree and `G` has a full immersion isomorphic to `K`. -/
def CodeHasFullImmersionIso {n m d n' m' d' : ℕ} (G : EdgeCode n m d) (K : EdgeCode n' m' d') :
    Prop :=
  ∃ hd : d' = d, HasFullImmersionIso G.graph G.label K.graph
    (fun p (i : Fin d) => K.lab p.1 (Fin.cast hd.symm i))

/-- `|H|`: the number of vertices plus the dimension of the label space. -/
def size {n m d : ℕ} (_K : EdgeCode n m d) : ℕ := n + d

end

end FullImmersionFPT.Main


