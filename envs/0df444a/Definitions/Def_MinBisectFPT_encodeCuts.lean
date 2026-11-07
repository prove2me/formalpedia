-- Prove2me | Definitions.Def_MinBisectFPT_encodeCuts
-- name    : MinBisectFPT_encodeCuts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:55:15.482196+00:00
-- url     : https://prove2.me/theorems/2a596df4-e170-4768-851b-d54e11f40ceb
-- title:
--   Word-RAM inputs and bit encodings of cut lists and families
-- statement:
--   The linear-time clauses of Lemmas 3.1 and 4.5 are stated on the published unit-cost word RAM. Its memory is **preloaded**: the nonnegative cells hold, in order, for Lemma 3.1 the numbers $n$, $m$, $|A_0|$, $|B_0|$, $p$, the elements of $A_0$, of $B_0$, and the edges $u_1,v_1,\dots$ with $u_i<v_i$ in lexicographic order; for Lemma 4.5 the numbers $n$, $m$, $|\beta|$, $v$, $k$, $q$, the elements of $\beta$, and the edges. All other cells hold $0$.
--
--   The output tape holds a list of cuts or sets, each one after the bit $1$, and the list ends with the bit $0$. A cut is its size, then its pairs $u<v$ in lexicographic order; a set is as in the rest of the mission.
--
--   **Formalization Note** A time linear in $|V|+|E|$ needs random access to an input already in memory, since reading a graph bit by bit costs $\log n$ per endpoint. There is no length prefix, because an algorithm that lists its output one item at a time does not know the number of items when it starts writing.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 3.1, p.9; Lemma 4.5, p.14

import Mathlib
import Definitions.Def_MinBisectFPT_cutSize
import Definitions.Def_MinBisectFPT_encodeCounts

open scoped Classical

namespace MinBisectFPT

open ExponomialAssortment.FPTAS (encodeNat)

/-- A preloaded memory of the published word RAM `FixedMachinePrec.ramExec`: the list of naturals in
the nonnegative cells `0, 1, …`, and `0` everywhere else. -/
def memOfList (W : ℕ) (cells : List ℕ) : Int → BitVec W :=
  fun i => if 0 ≤ i then BitVec.ofNat W (cells.getD i.toNat 0) else 0

/-- The elements of a vertex set in increasing order. -/
noncomputable def setCells {n : ℕ} (S : Finset (Fin n)) : List ℕ :=
  ((List.finRange n).filter (· ∈ S)).map fun v => v.val

/-- The edges `u < v` of `H` in lexicographic order, each as the two cells `u, v`. -/
noncomputable def edgeCells {n : ℕ} (H : SimpleGraph (Fin n)) : List ℕ :=
  (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => u < v ∧ H.Adj u v).flatMap fun v => [u.val, v.val]

/-- **Preloaded input of Lemma 3.1(ii)**: `n, m, |A0|, |B0|, p, A0…, B0…, u₁, v₁, …`. Anand,
Kipouridis, Węgrzycki, *Counting over Unbreakable Decompositions*, STOC 2027 submission (manuscript
sha256 8db80a52…), p.9.

**Formalization Note** A linear time bound in `|V| + |E|` needs random access to an input already in
memory: reading a graph bit by bit costs `log n` per endpoint. -/
noncomputable def cutsMem (W : ℕ) {n : ℕ} (H : SimpleGraph (Fin n)) (A0 B0 : Finset (Fin n)) (p : ℕ) :
    Int → BitVec W :=
  memOfList W ([n, edgeCount H, A0.card, B0.card, p] ++ setCells A0 ++ setCells B0 ++
    edgeCells H)

/-- **Preloaded input of Lemma 4.5** (p.14): `n, m, |β|, v, k, q, β…, u₁, v₁, …`. -/
noncomputable def familyMem (W : ℕ) {n : ℕ} (H : SimpleGraph (Fin n)) (β : Finset (Fin n))
    (v : Fin n) (k q : ℕ) : Int → BitVec W :=
  memOfList W ([n, edgeCount H, β.card, v.val, k, q] ++ setCells β ++ edgeCells H)

/-- A set of edges: its size, then its pairs `u < v` in lexicographic order. -/
noncomputable def encodeCut {n : ℕ} (F : Finset (Sym2 (Fin n))) : List Bool :=
  encodeNat F.card ++ (List.finRange n).flatMap fun u =>
    ((List.finRange n).filter fun v => u < v ∧ s(u, v) ∈ F).flatMap fun v =>
      encodeNat u.val ++ encodeNat v.val

/-- A list of cuts, each after the bit `true`, ended by `false`.

**Formalization Note** No length prefix: an algorithm listing the cuts one at a time does not know
their number when it starts writing. -/
noncomputable def encodeCuts {n : ℕ} (L : List (Finset (Sym2 (Fin n)))) : List Bool :=
  L.flatMap (fun F => true :: encodeCut F) ++ [false]

/-- A family of vertex sets, each after the bit `true`, ended by `false` (see `encodeCuts`). -/
noncomputable def encodeFamily {n : ℕ} (L : List (Finset (Fin n))) : List Bool :=
  L.flatMap (fun S => true :: encodeSet S) ++ [false]

end MinBisectFPT


