-- Prove2me | Definitions.Def_QuantumScalingMWPM_QLiquidationist_Blossom
-- name    : QuantumScalingMWPM_QLiquidationist_Blossom
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:13:00.178467+00:00
-- url     : https://prove2.me/theorems/f28f0d74-c6a2-45da-a4d1-63181a55b145
-- title:
--   Blossoms, the contracted graph $G/\Omega$, Definition 1, duals, Criteria 1–3, lifting, and the SEARCHONE tasks of Figure 3
-- statement:
--   This module formalizes the blossom machinery of §2 together with the specification of the five SEARCHONE tasks.
--
--   **Blossoms (§2.1, p. 5; App. E, p. 39).** A trivial blossom is a single vertex. A non-trivial blossom $B$ is stored with its ordered odd cycle of child blossoms $C_0,C_1,\dots,C_{2k}$, where $C_0$ is the base child, and with its defining cycle edges $e_1,\dots,e_{2k},e_{2k+1}$. Here $e_i$ joins $C_{i-1}$ to $C_i$ and $e_{2k+1}$ joins $C_{2k}$ to $C_0$. The cycle edges alternate unmatched, matched, …, matched, unmatched. The base $b(B)$ is the base of $C_0$, recursively. A blossom family $\Omega$ is *valid* for a matching $M$ when:
--   1. it is laminar and forms a forest;
--   2. every record is such an alternating odd cycle of blossoms of $\Omega$;
--   3. a matched edge leaving a blossom is incident to its base.
--
--   These are the facts the source says are always maintained (p. 6).
--
--   **Contracted graph.** The root blossom of $v$ is the largest blossom containing $v$. A root blossom is *free* if no matched edge crosses its boundary. A path in $G/\Omega$ is given by its original edges $e_1,\dots,e_{r-1}$, with $e_i$ joining $B_i$ to $B_{i+1}$ and the root blossoms $B_1,\dots,B_r$ distinct. **Definition 1** (augmenting path of blossoms) requires that the edges alternate, starting and ending with an unmatched edge, and that $B_1$ and $B_r$ are free.
--
--   **Duals and eligibility (p. 6, p. 24, p. 37).** The quantity
--   $$yz(u,v)=y(u)+y(v)+\sum_{B\in\Omega:\,u,v\in B}z(B)$$
--   is defined here. Criterion 1 is $yz=w$ and Criterion 3 is $yz\in\{w,\,w-2\}$. Criterion 2 applies to an edge between different root blossoms: it holds for a matched edge with $y(u)+y(v)=w(u,v)$ and for an unmatched edge with $y(u)+y(v)=w(u,v)-2$.
--
--   **Expansion (Lemma 26, Fact 1, Algorithm 1 line 32).** The route from a vertex to the base of its blossom follows the stored cycle in the direction with an even number of cycle edges and expands the children recursively. Lifting a contracted path concatenates these routes. Stopped at single vertices, the lift is an augmenting path in $G$. Stopped at the blossoms of $\Omega$, it expands the temporary blossoms of $\Omega'\setminus\Omega$. Augmenting along a path flips its edges. Afterwards each record is re-based, that is, rotated so that the child whose two cycle edges are unmatched comes first (proof of Fact 1, p. 40: only the base child changes).
--
--   **The SEARCHONE specification (Figure 3, p. 7; §3.5, p. 22).** From $(M,\Omega,y,z)$ the tasks produce $(M',\Omega',y',z')$ as follows.
--   1. $\Psi$ is a maximal set of blossom-disjoint eligible augmenting paths in $G/\Omega$.
--   2. $M'$ is $M$ augmented along their lifts.
--   3. New blossoms are contracted one at a time. Each is an eligible odd alternating cycle of current root blossoms whose base child is OUT. Contraction continues until no eligible edge joins two OUT vertices in different root blossoms, and every new blossom gets $z=0$.
--   4. $y$ decreases by $1$ on $V_{OUT}$ and increases by $1$ on $V_{IN}$. $z$ increases by $2$ on OUT root blossoms and decreases by $2$ on IN root blossoms. Here $V_{OUT}$ and $V_{IN}$ are the vertices whose root blossom is reached by an eligible alternating path of even, respectively odd, length from a free root blossom.
--   5. Every root blossom with $z=0$ is dissolved.
--
--   **Formalization Note** A blossom is identified with its vertex set, and the duals are $y:V\to\mathbb Z$ and $z$ on vertex sets.
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), §2.1, pp. 4–5 (blossoms, Definition 1); §2.2, p. 6 (yz, Criterion 2); Figure 3, p. 7; §3.5, p. 22; §4.1, p. 24 (Criteria 1, 3); Appendix C, p. 37; Appendix E, pp. 39–40 (base, Lemma 26, proof of Fact 1); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_Graph

/-!
# Blossoms, the contracted graph, duals, eligibility and the tasks of SEARCHONE

Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026):
§2.1 (pp. 4–5, blossoms, Definition 1), §2.2 (p. 6, `yz`, tight/almost tight, Criterion 2),
§4.1 (p. 24, Criteria 1 and 3), Figure 3 (p. 7, the five tasks), §3.5 (p. 22, dual adjustment),
Appendix C (p. 37), Appendix E (p. 39, base, defining cycles, Lemma 26 expansion).

**Blossoms.** A trivial blossom is a single vertex. A non-trivial blossom `B` is stored as a record:
its ordered cycle of children `C₀, C₁, …, C₂ₖ` (blossoms, given by their vertex sets; `C₀` is the
base child) and its defining cycle edges `e₁, …, e₂ₖ, e₂ₖ₊₁`, where `eᵢ = (pᵢ, qᵢ)` joins
`pᵢ ∈ Cᵢ₋₁` to `qᵢ ∈ Cᵢ` and `e₂ₖ₊₁` joins `C₂ₖ` to `C₀` (Algorithm 2, line 6, p. 15). Along the
cycle the edges alternate unmatched, matched, …, matched, unmatched, so `⌊d/2⌋` of the `d = 2k+1`
cycle edges are matched and the base child is the unmatched child (p. 5). The base `b(B)` is the
base of the base child, recursively (p. 39). A blossom family `Ω` is a list of non-trivial records;
a blossom is identified with its vertex set (distinct blossoms of a laminar family of odd sets with
at least three children have distinct vertex sets). The **standing blossom invariant** (p. 6, "It
is standard for matching algorithms in general graphs to explicitly maintain the blossom structure
so that these facts always hold"; p. 39) is `IsBlossomFamily`: laminar, every record an odd
alternating cycle of child blossoms, and a matched edge leaving a blossom is incident to its base.

**Contracted graph.** `rootSet Ω v` is the root blossom containing `v` (the largest blossom of `Ω`
containing `v`, or `{v}`). The vertices of `G/Ω` are the root blossoms (p. 5); a root blossom is
free if no matched edge crosses its boundary (p. 5). A path in `G/Ω` is given by its original
edges `e₁, …, e_{r−1}`, `eᵢ` from `Bᵢ` to `Bᵢ₊₁` (Figure 2, Definition 1); the blossoms
`B₁, …, B_r` are read off as root blossoms of the endpoints and must be distinct (a path).

**Formalization Note.** Edges of `G` are unordered (`Sym2`) for weights; paths carry ordered pairs
to record direction. Dual variables are `y : Fin n → ℤ` and `z : Finset (Fin n) → ℤ` (read on the
vertex sets of records). `Elig2` is Criterion 2 for an edge whose endpoints lie in different root
blossoms (the root-crossing condition is stated separately wherever the source states it), where
`yz = y(u) + y(v)` (p. 6). The expansion `route` of a blossom along its stored defining cycles is
Lemma 26's construction; it is used both to lift contracted paths to `G` (Fact 1) and, stopped at
the blossoms of `Ω`, to expand the temporary blossoms of `Ω′ \ Ω` (Algorithm 1, line 32).
-/

namespace QuantumScalingMWPM.QLiquidationist

open scoped Classical

variable {n : ℕ}

/-- A non-trivial blossom record: ordered children `C₀ … C₂ₖ` (vertex sets, `C₀` the base child)
and defining cycle edges `e₁ … e₂ₖ₊₁` (`eᵢ` from `Cᵢ₋₁` to `Cᵢ`, the last from `C₂ₖ` to `C₀`). -/
structure BRec (n : ℕ) where
  kids : List (Finset (Fin n))
  cyc : List (Fin n × Fin n)

/-- The vertex set `V(B)` of a record: the union of its children. -/
def BRec.verts (B : BRec n) : Finset (Fin n) := B.kids.foldr (· ∪ ·) ∅

/-- A blossom family `Ω`: a list of non-trivial blossom records. -/
abbrev Family (n : ℕ) := List (BRec n)

/-- The record of `Ω` with vertex set `S`, if any. -/
def findRec (Ω : Family n) (S : Finset (Fin n)) : Option (BRec n) :=
  Ω.find? fun B => decide (B.verts = S)

/-- The root blossom of `Ω` containing `v` (`ROOTB`): the union of `{v}` and every record
containing `v`; in a laminar family this is the largest blossom containing `v`. -/
def rootSet (Ω : Family n) (v : Fin n) : Finset (Fin n) :=
  {v} ∪ (Ω.filter fun B => decide (v ∈ B.verts)).foldr (fun B acc => B.verts ∪ acc) ∅

/-- `S` is a blossom of `Ω`: a singleton (trivial blossom) or the vertex set of a record. -/
def IsUnit (Ω : Family n) (S : Finset (Fin n)) : Prop :=
  (∃ v, S = {v}) ∨ ∃ B ∈ Ω, B.verts = S

/-- The record `B` is a root of `Ω`: no record of `Ω` strictly contains it. -/
def IsRootRec (Ω : Family n) (B : BRec n) : Prop :=
  B ∈ Ω ∧ ∀ B' ∈ Ω, B.verts ⊆ B'.verts → B'.verts = B.verts

/-- Base of a blossom, by recursion on the base child (`fuel` bounds the nesting depth). -/
noncomputable def baseAux (Ω : Family n) : ℕ → Finset (Fin n) → Option (Fin n)
  | 0, _ => none
  | f + 1, S =>
      if h : S.card = 1 then some (S.min' (Finset.card_pos.1 (by omega)))
      else match findRec Ω S with
        | some B => match B.kids.head? with
          | some C => baseAux Ω f C
          | none => none
        | none => none

/-- The base `b(B)` of the blossom with vertex set `S` (p. 39). -/
noncomputable def base (Ω : Family n) (S : Finset (Fin n)) : Option (Fin n) :=
  baseAux Ω (Ω.length + 1) S

/-- The standing blossom invariant (§2.1 p. 5, Fact 1 p. 6, Appendix E p. 39) for the matching `M`:
1. every record has an odd number `≥ 3` of children, pairwise disjoint blossoms of `Ω`, and as
   many cycle edges as children;
2. cycle edge `i` (0-based) is an edge of `G` from child `i` to child `i+1 mod d`, matched iff `i`
   is odd (unmatched, matched, …, matched, unmatched);
3. the records form a laminar family of distinct sets, and a record strictly inside another lies
   inside one of its children (the forest structure);
4. a matched edge leaving a blossom is incident to its base. -/
def IsBlossomFamily (G : SimpleGraph (Fin n)) (M : Mate n) (Ω : Family n) : Prop :=
  (∀ B ∈ Ω, Odd B.kids.length ∧ 3 ≤ B.kids.length ∧ B.cyc.length = B.kids.length ∧
      (∀ C ∈ B.kids, C.Nonempty ∧ IsUnit Ω C) ∧ B.kids.Pairwise Disjoint) ∧
  (∀ B ∈ Ω, ∀ i (h : i < B.cyc.length),
      (B.cyc[i]).1 ∈ B.kids.getD i ∅ ∧ (B.cyc[i]).2 ∈ B.kids.getD ((i + 1) % B.kids.length) ∅ ∧
      G.Adj (B.cyc[i]).1 (B.cyc[i]).2 ∧ (M (B.cyc[i]).1 = some (B.cyc[i]).2 ↔ i % 2 = 1)) ∧
  (Ω.map BRec.verts).Nodup ∧
  (∀ B ∈ Ω, ∀ B' ∈ Ω, B.verts ⊆ B'.verts ∨ B'.verts ⊆ B.verts ∨ Disjoint B.verts B'.verts) ∧
  (∀ B ∈ Ω, ∀ B' ∈ Ω, B'.verts ⊂ B.verts → ∃ C ∈ B.kids, B'.verts ⊆ C) ∧
  (∀ B ∈ Ω, ∀ a ∈ B.verts, ∀ b, M a = some b → b ∉ B.verts → base Ω B.verts = some a)

/-- A root blossom is free if no matched edge crosses its boundary (p. 5). -/
def IsFreeRoot (Ω : Family n) (M : Mate n) (R : Finset (Fin n)) : Prop :=
  (∃ v, R = rootSet Ω v) ∧ ∀ a ∈ R, ∀ b, M a = some b → b ∈ R

/-! ### Duals and eligibility -/

/-- `yz(u, v) = y(u) + y(v) + Σ_{B ∈ Ω, u, v ∈ B} z(B)` (p. 6, p. 37). -/
def yz (Ω : Family n) (y : Fin n → ℤ) (z : Finset (Fin n) → ℤ) (u v : Fin n) : ℤ :=
  y u + y v + ((Ω.filter fun B => decide (u ∈ B.verts ∧ v ∈ B.verts)).map fun B => z B.verts).sum

/-- Criterion 1 (p. 24): the edge is tight, `yz(e) = w(e)`. -/
def Elig1 (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (Ω : Family n) (y : Fin n → ℤ)
    (z : Finset (Fin n) → ℤ) (u v : Fin n) : Prop :=
  G.Adj u v ∧ yz Ω y z u v = w s(u, v)

/-- Criterion 3 (p. 24): `yz(e) = w(e)` or `yz(e) = w(e) − 2`. -/
def Elig3 (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (Ω : Family n) (y : Fin n → ℤ)
    (z : Finset (Fin n) → ℤ) (u v : Fin n) : Prop :=
  G.Adj u v ∧ (yz Ω y z u v = w s(u, v) ∨ yz Ω y z u v = w s(u, v) - 2)

/-- Criterion 2 (p. 6) for an edge `(u, v)` with endpoints in different root blossoms: matched and
tight (`y(u) + y(v) = w(u, v)`), or unmatched and almost tight (`y(u) + y(v) = w(u, v) − 2`). -/
def Elig2 (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
    (u v : Fin n) : Prop :=
  G.Adj u v ∧ ((M u = some v ∧ y u + y v = w s(u, v)) ∨ (M u ≠ some v ∧ y u + y v = w s(u, v) - 2))

/-! ### Paths in the contracted graph (Definition 1, p. 5) -/

/-- The blossoms `B₁, …, B_r` of a contracted path given by its edges. -/
def blossomsOf (Ω : Family n) : List (Fin n × Fin n) → List (Finset (Fin n))
  | [] => []
  | e :: es => rootSet Ω e.1 :: (e :: es).map fun f => rootSet Ω f.2

/-- An alternating path of root blossoms of `G/Ω` starting at a free root blossom with an unmatched
edge: edges of `G` joining distinct consecutive root blossoms, alternating unmatched/matched,
distinct blossoms (a path). -/
def IsAltPathH (G : SimpleGraph (Fin n)) (M : Mate n) (Ω : Family n)
    (es : List (Fin n × Fin n)) : Prop :=
  es ≠ [] ∧
  (∀ i (h : i < es.length), G.Adj (es[i]).1 (es[i]).2 ∧
      rootSet Ω (es[i]).1 ≠ rootSet Ω (es[i]).2 ∧ (M (es[i]).1 = some (es[i]).2 ↔ i % 2 = 1)) ∧
  (∀ i (h : i + 1 < es.length), rootSet Ω (es[i]).2 = rootSet Ω (es[i + 1]).1) ∧
  (blossomsOf Ω es).Nodup ∧
  ∀ e ∈ es.head?, IsFreeRoot Ω M (rootSet Ω e.1)

/-- Definition 1 (p. 5): an augmenting path of blossoms in `G/Ω`: an alternating path that starts
and ends with an unmatched edge (odd number of edges) and whose first and last blossoms are free. -/
def IsAugPathH (G : SimpleGraph (Fin n)) (M : Mate n) (Ω : Family n)
    (es : List (Fin n × Fin n)) : Prop :=
  IsAltPathH G M Ω es ∧ Odd es.length ∧ ∀ e ∈ es.getLast?, IsFreeRoot Ω M (rootSet Ω e.2)

/-- An eligible augmenting path of blossoms: every edge satisfies Criterion 2. -/
def IsEligAugPathH (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n)
    (y : Fin n → ℤ) (Ω : Family n) (es : List (Fin n × Fin n)) : Prop :=
  IsAugPathH G M Ω es ∧ ∀ e ∈ es, Elig2 G w M y e.1 e.2

/-- Two contracted paths are blossom-disjoint: no root blossom lies on both. -/
def BlossomDisjoint (Ω : Family n) (P Q : List (Fin n × Fin n)) : Prop :=
  Disjoint (blossomsOf Ω P).toFinset (blossomsOf Ω Q).toFinset

/-- An augmenting path in `G` itself: consecutive edges of `G` sharing endpoints, distinct
vertices, alternating unmatched/matched starting and ending unmatched, free endpoints. -/
def IsAugPathG (G : SimpleGraph (Fin n)) (M : Mate n) (es : List (Fin n × Fin n)) : Prop :=
  es ≠ [] ∧ Odd es.length ∧
  (∀ i (h : i < es.length), G.Adj (es[i]).1 (es[i]).2 ∧ (M (es[i]).1 = some (es[i]).2 ↔ i % 2 = 1)) ∧
  (∀ i (h : i + 1 < es.length), (es[i]).2 = (es[i + 1]).1) ∧
  (match es with | [] => True | e :: _ => (e.1 :: es.map Prod.snd).Nodup) ∧
  (∀ e ∈ es.head?, M e.1 = none) ∧ (∀ e ∈ es.getLast?, M e.2 = none)

/-! ### Expansion along stored defining cycles (Lemma 26, Fact 1, Algorithm 1 line 32) -/

/-- Reverse a path given by its edges. -/
def revPath (es : List (Fin n × Fin n)) : List (Fin n × Fin n) := (es.map Prod.swap).reverse

/-- `routeAux Φ stop f S a`: the alternating path inside the blossom `S` of `Φ` from (the unit
containing) `a` to the base of `S`, obtained recursively from the stored defining cycles; blossoms
with `stop` are units and are not expanded. If `a` lies in child `Cᵢ`, the route goes around the
cycle in the direction with an even number of cycle edges (down `Cᵢ, Cᵢ₋₁, …, C₀` for even `i`, up
`Cᵢ, Cᵢ₊₁, …, C₂ₖ, C₀` for odd `i`), entering and leaving each child at the endpoints of the cycle
edges and expanding it recursively (Lemma 26, p. 39). -/
def routeAux (Φ : Family n) (stop : Finset (Fin n) → Bool) :
    ℕ → Finset (Fin n) → Fin n → List (Fin n × Fin n)
  | 0, _, _ => []
  | f + 1, S, a =>
    if stop S then [] else
    match findRec Φ S with
    | none => []
    | some B =>
      let L := B.kids.length
      let C : ℕ → Finset (Fin n) := fun j => B.kids.getD j ∅
      let p : ℕ → Fin n := fun j => (B.cyc.getD (j - 1) (a, a)).1
      let q : ℕ → Fin n := fun j => (B.cyc.getD (j - 1) (a, a)).2
      let r : Finset (Fin n) → Fin n → List (Fin n × Fin n) := fun T x => routeAux Φ stop f T x
      let i := B.kids.findIdx fun T => decide (a ∈ T)
      if i = 0 then r (C 0) a
      else if i % 2 = 0 then
        r (C i) a ++ [(q i, p i)] ++
          (((List.range (i - 1)).reverse.map (· + 1)).flatMap fun j =>
            (if j % 2 = 1 then revPath (r (C j) (q j)) else r (C j) (p (j + 1))) ++ [(q j, p j)]) ++
          r (C 0) (p 1)
      else
        r (C i) a ++ [(p (i + 1), q (i + 1))] ++
          (((List.range (L - 1 - i)).map (· + (i + 1))).flatMap fun j =>
            (if j % 2 = 0 then revPath (r (C j) (p (j + 1))) else r (C j) (q j)) ++
              [(p (j + 1), q (j + 1))]) ++
          r (C 0) (q L)

/-- The route from `a` to the base of the root blossom of `Φ` containing `a`. -/
def route (Φ : Family n) (stop : Finset (Fin n) → Bool) (a : Fin n) : List (Fin n × Fin n) :=
  routeAux Φ stop (Φ.length + 1) (rootSet Φ a) a

/-- Lift (expand) a contracted path `e₁, …, e_{r−1}` of root blossoms of `Φ`: start at the base of
`B₁`, route to the endpoint of `e₁`, and inside every later blossom connect the endpoint of the
unmatched boundary edge with the base, which carries the matched boundary edge; in `B_r` route to
its base (proof of Fact 1, p. 40). -/
def liftPath (Φ : Family n) (stop : Finset (Fin n) → Bool) (es : List (Fin n × Fin n)) :
    List (Fin n × Fin n) :=
  match es with
  | [] => []
  | e₁ :: _ =>
    revPath (route Φ stop e₁.1) ++
      (List.range es.length).flatMap fun i =>
        let e := es.getD i e₁
        [e] ++ (if i + 1 = es.length then route Φ stop e.2
                else if i % 2 = 0 then route Φ stop e.2
                else revPath (route Φ stop (es.getD (i + 1) e₁).1))

/-- Units of the original graph: single vertices (lifting all the way to `G`). -/
def vertexStop : Finset (Fin n) → Bool := fun S => decide (S.card ≤ 1)

/-- The lift to `G` of a path of root blossoms of `Ω` (Fact 1). -/
def liftG (Ω : Family n) (es : List (Fin n × Fin n)) : List (Fin n × Fin n) :=
  liftPath Ω vertexStop es

/-- Augment `M` along a path of `G` given by its edges: the edges in odd positions (1-based, the
unmatched ones) become matched; every other vertex keeps its mate. -/
def augment (M : Mate n) (es : List (Fin n × Fin n)) : Mate n := fun v =>
  match ((es.zipIdx).filter fun p => decide (p.2 % 2 = 0)).find?
      (fun p => decide (p.1.1 = v ∨ p.1.2 = v)) with
  | some p => some (if p.1.1 = v then p.1.2 else p.1.1)
  | none => M v

/-- Augment along each path of a list in turn (Task 2). -/
def augmentAll (M : Mate n) (Ps : List (List (Fin n × Fin n))) : Mate n := Ps.foldl augment M

/-- After an augmentation the defining cycle of a blossom is unchanged but its base child may
change ("this flip only changes which child acts as the base child", proof of Fact 1, p. 40). The
record is re-based: its children and cycle edges are rotated so that the first child is the one
whose two cycle edges are both unmatched under `M` (if there is none the record is unchanged). -/
def rebaseRec (M : Mate n) (B : BRec n) : BRec n :=
  let L := B.kids.length
  let unm : ℕ → Bool := fun i =>
    match B.cyc[i]? with
      | some (a, b) => decide (M a ≠ some b)
      | none => false
  let ok : ℕ → Bool := fun i => unm i && unm ((i + L - 1) % L)
  match (List.range L).find? ok with
  | some j => ⟨B.kids.rotate j, B.cyc.rotate j⟩
  | none => B

/-- Re-base every record of a family for the matching `M`. -/
def rebase (M : Mate n) (Ω : Family n) : Family n := Ω.map (rebaseRec M)

/-! ### The tasks of SEARCHONE (Figure 3, p. 7; §3.5, p. 22) -/

/-- Even/odd eligible alternating reachability in `G/Φ` (§3.5): `v ∈ V_OUT` if its root blossom is
free or is the last blossom of an eligible alternating path of even length from a free root
blossom; `v ∈ V_IN` if it is the last blossom of one of odd length. -/
def InVOut (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
    (Φ : Family n) (v : Fin n) : Prop :=
  IsFreeRoot Φ M (rootSet Φ v) ∨
    ∃ es, IsAltPathH G M Φ es ∧ (∀ e ∈ es, Elig2 G w M y e.1 e.2) ∧ Even es.length ∧
      ∀ e ∈ es.getLast?, rootSet Φ e.2 = rootSet Φ v

/-- See `InVOut`. -/
def InVIn (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
    (Φ : Family n) (v : Fin n) : Prop :=
  ∃ es, IsAltPathH G M Φ es ∧ (∀ e ∈ es, Elig2 G w M y e.1 e.2) ∧ Odd es.length ∧
    ∀ e ∈ es.getLast?, rootSet Φ e.2 = rootSet Φ v

/-- Task 1 (Figure 3): `Ψ` is a maximal set of pairwise blossom-disjoint eligible augmenting paths
in `G/Ω`. -/
def MaximalAugSet (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n) (y : Fin n → ℤ)
    (Ω : Family n) (Ψ : List (List (Fin n × Fin n))) : Prop :=
  (∀ P ∈ Ψ, IsEligAugPathH G w M y Ω P) ∧ Ψ.Pairwise (BlossomDisjoint Ω) ∧
    ∀ P, IsEligAugPathH G w M y Ω P → ∃ Q ∈ Ψ, ¬ BlossomDisjoint Ω P Q

/-- Task 3 (Figure 3) as a sequence of contractions: `news` are new records added one after
another to `Ω`; each is an odd alternating cycle of root blossoms of the family built so far, with
eligible cycle edges and an OUT base child, and the final family is a valid blossom family. -/
def IsContractionSeq (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Mate n)
    (y : Fin n → ℤ) (Ω : Family n) (news : Family n) : Prop :=
  IsBlossomFamily G M (Ω ++ news) ∧
  ∀ j (h : j < news.length),
    (∀ C ∈ (news[j]).kids, ∃ v, C = rootSet (Ω ++ news.take j) v) ∧
    (∀ e ∈ (news[j]).cyc, Elig2 G w M y e.1 e.2) ∧
    ∀ C ∈ (news[j]).kids.head?, ∃ v ∈ C, InVOut G w M y (Ω ++ news.take j) v

/-- The dual adjustment of Task 4 (§3.5) given OUT/IN predicates on vertices, followed by the
shape of `z`: on root records of `Φ` contained in `OUT` add `2`, contained in `IN` subtract `2`. -/
noncomputable def adjustY (y : Fin n → ℤ) (isOut isIn : Fin n → Prop) : Fin n → ℤ := fun v =>
  if isOut v then y v - 1 else if isIn v then y v + 1 else y v

/-- See `adjustY`. -/
noncomputable def adjustZ (Φ : Family n) (z : Finset (Fin n) → ℤ) (isOut isIn : Fin n → Prop) :
    Finset (Fin n) → ℤ := fun S =>
  if ∃ B, IsRootRec Φ B ∧ B.verts = S then
    (if ∀ v ∈ S, isOut v then z S + 2 else if ∀ v ∈ S, isIn v then z S - 2 else z S)
  else z S

/-- Task 5: dissolve every root blossom with `z(B) = 0`. -/
noncomputable def dissolveZero (Φ : Family n) (z : Finset (Fin n) → ℤ) : Family n :=
  Φ.filter fun B => decide (¬ (IsRootRec Φ B ∧ z B.verts = 0))

/-- The `z` values after Task 3: new blossoms get `z(B) = 0` (p. 12, p. 22). -/
def zAfterPromotion (news : Family n) (z : Finset (Fin n) → ℤ) : Finset (Fin n) → ℤ :=
  fun S => if S ∈ news.map BRec.verts then 0 else z S

/-- **The specification of SEARCHONE (Figure 3, with §3.5).** From `(M, Ω, y, z)` the five tasks
produce `(M', Ω', y', z')` when: (1) `Ψ` is a maximal set of blossom-disjoint eligible augmenting
paths in `G/Ω`; (2) `M₂` is `M` augmented along their lifts to `G`, the blossoms of `Ω` unchanged (only re-based,
`rebase`); (3) new blossoms
`news` are contracted (eligible odd alternating cycles with OUT base) until no eligible edge joins
two OUT vertices in distinct root blossoms of `Ω₃ = rebase M₂ Ω ++ news`, and the new blossoms get `z = 0`;
(4) `y(v)` decreases by `1` on `V_OUT` and increases by `1` on `V_IN`, `z(B)` increases by `2` on
OUT root blossoms and decreases by `2` on IN root blossoms (reachability in `G/Ω₃`); (5) root
blossoms with `z(B) = 0` are dissolved. -/
def SearchOneSpec (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ)
    (M : Mate n) (Ω : Family n) (y : Fin n → ℤ) (z : Finset (Fin n) → ℤ)
    (M' : Mate n) (Ω' : Family n) (y' : Fin n → ℤ) (z' : Finset (Fin n) → ℤ) : Prop :=
  ∃ (Ψ : List (List (Fin n × Fin n))) (news : Family n),
    MaximalAugSet G w M y Ω Ψ ∧
    M' = augmentAll M (Ψ.map (liftG Ω)) ∧
    IsContractionSeq G w M' y (rebase M' Ω) news ∧
    (∀ u v, InVOut G w M' y (rebase M' Ω ++ news) u → InVOut G w M' y (rebase M' Ω ++ news) v →
      rootSet (rebase M' Ω ++ news) u ≠ rootSet (rebase M' Ω ++ news) v →
      ¬ Elig2 G w M' y u v) ∧
    y' = adjustY y (InVOut G w M' y (rebase M' Ω ++ news)) (InVIn G w M' y (rebase M' Ω ++ news)) ∧
    z' = adjustZ (rebase M' Ω ++ news) (zAfterPromotion news z)
      (InVOut G w M' y (rebase M' Ω ++ news)) (InVIn G w M' y (rebase M' Ω ++ news)) ∧
    Ω' = dissolveZero (rebase M' Ω ++ news) z'

/-! ### Sanity checks -/

/-- With no blossoms every vertex is its own root blossom. -/
example (v : Fin 3) : rootSet ([] : Family 3) v = {v} := by simp [rootSet]

/-- A triangle `0, 1, 2` with `1 – 2` matched is a blossom with base child `{0}`. -/
def triangle : BRec 3 := ⟨[{0}, {1}, {2}], [(0, 1), (1, 2), (2, 0)]⟩

example : triangle.verts = Finset.univ := by decide

/-- Lifting the one-edge contracted path from the free vertex `3` into the triangle blossom
`{0, 1, 2}` of `Fin 4` (base `0`, `1 – 2` matched), entering at vertex `1`, continues up the cycle
`1 → 2 → 0` to the base. -/
example : liftPath ([⟨[{0}, {1}, {2}], [(0, 1), (1, 2), (2, 0)]⟩] : Family 4) vertexStop [(3, 1)] =
    [(3, 1), (1, 2), (2, 0)] := by decide

/-- After augmenting so that `0 – 1` (instead of `1 – 2`) is the matched cycle edge, the triangle
is re-based at the child `{2}`: children `{2}, {0}, {1}`, cycle edges unmatched, matched,
unmatched. -/
example :
    let M : Mate 3 := fun v => if v = 0 then some 1 else if v = 1 then some 0 else none
    (rebaseRec M triangle).kids = [{2}, {0}, {1}] ∧
      (rebaseRec M triangle).cyc = [(2, 0), (0, 1), (1, 2)] := by
  decide

/-- With the original matching `1 – 2` the triangle is already based at `{0}`. -/
example :
    let M : Mate 3 := fun v => if v = 1 then some 2 else if v = 2 then some 1 else none
    (rebaseRec M triangle).kids = triangle.kids := by
  decide

/-- Triangle plus a pendant edge (`Fin 4`, triangle `0, 1, 2`, pendant `0 – 3`), the triangle
contracted: vertex `3` and the triangle are the two root blossoms. -/
example : rootSet ([⟨[{0}, {1}, {2}], [(0, 1), (1, 2), (2, 0)]⟩] : Family 4) 1 = {0, 1, 2} ∧
    rootSet ([⟨[{0}, {1}, {2}], [(0, 1), (1, 2), (2, 0)]⟩] : Family 4) 3 = {3} := by
  decide

/-- Augmenting along the single edge `0 – 1` of two free vertices matches them. -/
example : augment (fun _ : Fin 2 => none) [(0, 1)] 0 = some 1 ∧
    augment (fun _ : Fin 2 => none) [(0, 1)] 1 = some 0 := by decide

end QuantumScalingMWPM.QLiquidationist


