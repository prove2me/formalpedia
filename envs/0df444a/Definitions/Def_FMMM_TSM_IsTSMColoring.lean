-- Prove2me | Definitions.Def_FMMM_TSM_IsTSMColoring
-- name    : FMMM_TSM_IsTSMColoring
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:16:01.21445+00:00
-- url     : https://prove2.me/theorems/6ae18883-1ce2-45fe-a0a0-58db21194a15
-- title:
--   The blue/red colouring of $E_f$ used by the TSM algorithm
-- statement:
--   Let $F$ be a set of edges between ads $A$ and impression types $J$ (in the algorithm, $F = E_f$, whose components are paths and cycles because every degree is at most $2$). A set $B \subseteq F$ of **blue** edges, with **red** edges $F \setminus B$, is a **TSM colouring** of $F$ if $F$ can be written as a family of vertex-disjoint **pieces**, each a vertex sequence $v_0, v_1, \dots, v_k$ whose consecutive vertices are joined by edges of $F$, such that:
--
--   1. every edge of $F$ is an edge of some piece;
--   2. each piece is either a **path** (all vertices distinct, $k \ge 1$, and both end vertices have exactly one incident edge of $F$) or a **cycle** ($k \ge 4$, $v_k = v_0$, and $v_0, \dots, v_{k-1}$ distinct);
--   3. the colours follow the rules of the paper, with edges numbered $1, \dots, k$ along the piece:
--      - cycle edges alternate blue and red;
--      - on a path of odd length, edges alternate blue and red, with more blue than red (edges $1, 3, 5, \dots$ blue);
--      - on a path of even length that starts and ends with ads, edges alternate blue and red;
--      - on a path of even length that starts and ends with impressions, the first two edges are blue, and then the colours alternate red, blue, red, blue, …, ending in blue.
--
--   The choice of starting point and direction of each piece is free: this is exactly the freedom the paper leaves when it says "alternating". Every 2-matching has a TSM colouring, and the colouring is what defines the two suggested matchings: the blue edges and the red edges.
--
--   **Formalization Note** The pieces are encoded as a list of lists of vertices of $A \oplus J$; vertex-disjointness and the end-degree condition make each piece a whole connected component of $(A \oplus J, F)$. Edge positions are $0$-based in Lean, so "edge $j$ is blue iff $j$ is odd" reads "position $i$ is blue iff $i$ is even", and the rule for even paths between impressions reads "$i \le 1$ or $i$ odd".
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.1, pp. 6–7 (four colouring rules)

import Mathlib
import Definitions.Def_FMMM_TSM_pieceEdge

namespace FMMM.TSM

/-- **A blue/red colouring of `E_f` by the rules of the TSM algorithm.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.1, pp. 6–7: "we know that the graph induced by E_f is a collection of paths
and cycles. Using this structure, we assign colors blue and red to the edges of E_f as follows:
• Color the cycle edges alternating blue and red. • Color the edges of the odd-length paths
alternating blue and red, with more blue than red. • For the even-length paths that start and end
with nodes a ∈ A, alternate blue and red. • For the even-length paths that start and end with
impressions i ∈ I, color the first two edges blue, and then alternate red, blue, red, blue, etc.,
ending in blue."

`IsTSMColoring F blue` says `blue ⊆ F` (the red edges are `F \ blue`) and there is a list of
*pieces*, each a vertex sequence `p = [v₀, …, v_k]` of `A ⊕ J`, such that
1. distinct pieces share no vertex;
2. every edge of `F` is an edge `pieceEdge p i` of some piece;
3. in each piece, consecutive vertices lie on opposite sides and are joined by an edge of `F`;
4. each piece is either a **path** (all vertices distinct, `k ≥ 1`, and both end vertices have
   `F`-degree 1) or a **cycle** (`k ≥ 4`, `v_k = v₀`, and `v₀, …, v_{k−1}` distinct);
5. the `i`-th edge (0-based) of a piece is blue iff: for a path of even length `k` starting at an
   impression, `i ≤ 1` or `i` is odd ("first two edges blue, then alternate red, blue, …, ending in
   blue"); in every other case (cycles, odd paths, even paths between ads), `i` is even
   ("alternating blue and red", starting with blue).

**Formalization Note.** The pieces are the connected components of `(A ⊕ J, F)`; the existential
over the list of each piece (starting point and orientation) is exactly the freedom the paper
leaves in "alternating". For an even path between ads the two orientations give the two
alternating colourings; for an even path between impressions they give the two placements of the
pair of blue edges. The rules are not replaced by local degree conditions, which would admit other
colourings. -/
def IsTSMColoring {A J : Type} [DecidableEq A] [DecidableEq J] (F blue : Finset (A × J)) :
    Prop :=
  let deg : A ⊕ J → ℕ := Sum.elim (fun a => (F.filter (fun e => e.1 = a)).card)
    (fun j => (F.filter (fun e => e.2 = j)).card)
  blue ⊆ F ∧
  ∃ pieces : List (List (A ⊕ J)),
    pieces.Pairwise (fun p q => ∀ v ∈ p, v ∉ q) ∧
    (∀ e ∈ F, ∃ p ∈ pieces, ∃ i : ℕ, pieceEdge p i = some e) ∧
    ∀ p ∈ pieces,
      (∀ i : ℕ, i + 1 < p.length → ∃ e ∈ F, pieceEdge p i = some e) ∧
      ((p.Nodup ∧ 2 ≤ p.length ∧ (∀ v ∈ p.head?, deg v = 1) ∧ (∀ v ∈ p.getLast?, deg v = 1)) ∨
        (5 ≤ p.length ∧ p.head? = p.getLast? ∧ p.dropLast.Nodup)) ∧
      ∀ (i : ℕ) (e : A × J), pieceEdge p i = some e →
        (e ∈ blue ↔
          ((p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j)) ∧
              (i ≤ 1 ∨ Odd i)) ∨
          (¬ (p.Nodup ∧ Even (p.length - 1) ∧ ∃ j : J, p.head? = some (Sum.inr j)) ∧ Even i))

end FMMM.TSM


