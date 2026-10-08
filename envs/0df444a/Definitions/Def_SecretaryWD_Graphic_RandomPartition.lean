-- Prove2me | Definitions.Def_SecretaryWD_Graphic_RandomPartition
-- name    : SecretaryWD_Graphic_RandomPartition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:06:44.803946+00:00
-- url     : https://prove2.me/theorems/4f76df09-8215-42ff-b84d-80ddab4c0b22
-- title:
--   The random partition of Lemma 5.3 (graphic matroid to partition matroid)
-- statement:
--   This file defines the random partition of the edges of a graph used in the proof of Lemma 5.3. Colours are red and blue. Given the current edge set $E$ (initially all edges of the graph):
--
--   1. If $E$ has no edge, stop and return the empty family of parts.
--   2. Otherwise pick an edge $\{u,w\}\in E$ uniformly at random. With probability $\tfrac12$ colour $u$ red and $w$ blue, and with probability $\tfrac12$ colour $u$ blue and $w$ red. Colour every other vertex red or blue independently, each with probability $\tfrac12$.
--   3. For each red vertex $x$, create a part consisting of all red-blue edges of $E$ incident on $x$ (that is, all edges of $E$ at $x$ whose other endpoint is blue). Parts that would be empty are not created.
--   4. Recurse on the edges of $E$ with both endpoints blue, with fresh, independent randomness, and add the parts it creates.
--
--   The chosen edge is red-blue, so the edge set strictly shrinks and the procedure terminates. The result is a probability distribution over finite families of edge sets; it depends only on the graph.
--
--   By Lemma 5.3, this random partition shows that every graphic matroid satisfies a $3$-partition property.
--
--   **Formalization Note.** The edge $\{u,w\}$ is written as an ordered pair through a fixed representative; the fair coin decides which of its two vertices is red, which gives the paper's law. The independent colours are drawn for every vertex of the vertex type and then overwritten at $u$ and $w$. Edges with both endpoints red, and red-blue edges already placed in a part, are discarded for good. Loops are never chosen in step 2 (a simple graph has none).
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), p. 9, proof of Lemma 5.3 (construction)

import Mathlib

namespace SecretaryWD.Graphic

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The colouring of one round (p. 9), with `true` = red and `false` = blue. Write the chosen
edge as `e = {u, w}` with `(u, w) = e.out`. The node `u` gets colour `b` and `w` gets colour
`!b` (so `b` is the fair coin deciding which endpoint is red), and every other node `x` gets the
independent fair colour `c x`. -/
noncomputable def roundColoring (e : Sym2 V) (b : Bool) (c : V → Bool) : V → Bool :=
  fun x => if x = e.out.1 then b else if x = e.out.2 then !b else c x

open Classical in
/-- The part created for the red node `x` (p. 9): the edges of the current edge set `E` that
are incident on `x` and have a blue endpoint, i.e. all red-blue edges incident on `x`. -/
noncomputable def redPart (E : Finset (Sym2 V)) (col : V → Bool) (x : V) : Finset (Sym2 V) :=
  E.filter fun e => x ∈ e ∧ ∃ y ∈ e, col y = false

open Classical in
/-- The parts created in one round: one part for each red node, empty parts dropped. -/
noncomputable def roundParts (E : Finset (Sym2 V)) (col : V → Bool) : Finset (Finset (Sym2 V)) :=
  ((Finset.univ.filter fun x => col x = true).image (redPart E col)).filter Finset.Nonempty

open Classical in
/-- The edges of the current edge set `E` with both endpoints blue: the edge set on which the
procedure recurses (p. 9). All other edges of `E` (red-red, and red-blue ones already placed in a
part) are discarded for good. -/
noncomputable def blueEdges (E : Finset (Sym2 V)) (col : V → Bool) : Finset (Sym2 V) :=
  E.filter fun e => ∀ y ∈ e, col y = false

/-- The non-loop edges of `E` (all of `E` when `E` is the edge set of a simple graph). -/
def properEdges (E : Finset (Sym2 V)) : Finset (Sym2 V) :=
  E.filter fun e => ¬ e.IsDiag

theorem blueEdges_card_lt (E : Finset (Sym2 V)) (e : {e // e ∈ properEdges E}) (b : Bool)
    (c : V → Bool) : (blueEdges E (roundColoring e.1 b c)).card < E.card := by
  classical
  obtain ⟨e, he⟩ := e
  simp only [properEdges, Finset.mem_filter] at he
  obtain ⟨heE, hnd⟩ := he
  apply Finset.card_lt_card
  refine Finset.filter_ssubset.2 ⟨e, heE, ?_⟩
  have hne : e.out.1 ≠ e.out.2 := by
    intro h
    apply hnd
    rw [← Quot.out_eq e]
    exact (Sym2.mk_isDiag_iff).2 h
  intro hall
  have h1 := hall _ (Sym2.out_fst_mem e)
  have h2 := hall _ (Sym2.out_snd_mem e)
  simp only [roundColoring, if_neg (Ne.symm hne)] at h1 h2
  cases b <;> simp_all

/-- The random partition of Lemma 5.3 (p. 9), as a probability mass function on finite
families of parts. On the current edge set `E`: if `E` has no (non-loop) edge, return the empty
family. Otherwise pick an edge `e` of `E` uniformly at random, a fair coin `b` deciding which
endpoint of `e` is red, and independent fair colours `c` for all nodes; colour by
`roundColoring e b c`; output the parts of the red nodes, together with the parts produced by
running the procedure recursively on the blue-blue edges of `E`. -/
noncomputable def partitionPMF (E : Finset (Sym2 V)) : PMF (Finset (Finset (Sym2 V))) :=
  if h : (properEdges E).Nonempty then
    (PMF.uniformOfFinset (properEdges E).attach (by simpa using h)).bind fun e =>
      (PMF.uniformOfFintype Bool).bind fun b =>
        (PMF.uniformOfFintype (V → Bool)).bind fun c =>
          (partitionPMF (blueEdges E (roundColoring e.1 b c))).map fun Q =>
            roundParts E (roundColoring e.1 b c) ∪ Q
  else PMF.pure ∅
termination_by E.card
decreasing_by exact blueEdges_card_lt E e b c

end SecretaryWD.Graphic


