-- Prove2me | Definitions.Def_StreamColour_Reduction
-- name    : StreamColour_Reduction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:03.250616+00:00
-- url     : https://prove2.me/theorems/1f8d1b1b-dd16-40d4-a315-f91a476e344e
-- title:
--   §4.1 — the two reduction rules, removal records and the deficit $M_v$
-- statement:
--   The kernelization of Algorithm A. Let $U$ be the set of vertices not yet removed, $H=G[U]$, and for $v\in U$ let
--
--   $$B_v=\{u\in N_H[v]:|N_H[u]\triangle N_H[v]|\le 3h\}.$$
--
--   1. If some vertex has $d_H(v)\le 20h$, take the one with the smallest label, store $N_H(v)$, and remove $v$.
--   2. Otherwise, if some vertex has $|B_v|\ge d_H(v)/2$, take the one with the smallest label, store $Q=N_H[v]$ and, for each $u\in B_v$, the correction $e_u=\mathbf 1_{N_H[u]}-\mathbf 1_Q$, and only then remove $B_v$ in increasing label order.
--   3. Repeat until neither rule applies.
--
--   $K$ is the set of removed vertices and $V(H)$ what remains. From the stored records alone, an adjacency test is computed: the first record storing a row of $x$ or of $y$ decides. For $v\in V(H)$, $M_v=\binom{d_v}{2}-|E(H[N_H(v)])|$.
--
--   **Formalization Note** The procedure is a function of $G$ and $h$. $|B_v|\ge d_H(v)/2$ is written $d_H(v)\le 2|B_v|$, with no floor. A correction is stored as its $+1$ coordinates and its $-1$ coordinates. The size of a record counts each stored label and identifier, each of $\lceil\log_2(n+1)\rceil$ bits.
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), §4.1, pp.23–25 (PDF 25–27)

import Mathlib

namespace StreamColour

/-! # The reduction rules of §4.1

Chakraborty, Chatterjee, Kundu, Mishra (STOC 2027 submission, sha256 31a813b3…), §4.1, pp.23–24
(PDF 25–26): `B_v = {u ∈ N_H[v] : |N_H[u] △ N_H[v]| ≤ 3h}`. Rule 1: a vertex of smallest label with
`d_H(v) ≤ 20h`: store `N_H(v)` and remove `v`. Rule 2, tried only when rule 1 is unavailable: a vertex of
smallest label with `|B_v| ≥ d_H(v)/2`: store `Q = N_H[v]` and `e_u = 1_{N_H[u]} − 1_Q` for `u ∈ B_v`, then
remove `B_v` in increasing label order.

**Formalization Note.** `H = G[U]` is represented by the live set `U`. The procedure is a function of
`G` and `h`, which is what makes clause 3 of Lemma 4.2 hold: `removalRecords` lists the records in removal
order, and a rule 2 record lists its group by increasing label, with each correction `e_u` as the pair of
its `+1` coordinates `N_H[u] \ Q` and its `−1` coordinates `Q \ N_H[u]`. `|B_v| ≥ d/2` is written
`d ≤ 2|B_v|`, with no floor. The recursion runs on fuel `n`, and every step removes a vertex. -/

variable {n : ℕ}

/-- `N_H(v)` in the live graph `H = G[U]`. -/
def liveNbrs (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  U.filter (G.Adj v)

/-- `N_H[v]`. -/
def liveClosed (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  insert v (liveNbrs G U v)

/-- `d_H(v)`. -/
def liveDeg (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)) (v : Fin n) : ℕ :=
  (liveNbrs G U v).card

/-- `B_v = {u ∈ N_H[v] : |N_H[u] △ N_H[v]| ≤ 3h}`. -/
def groupB (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : ℕ) (U : Finset (Fin n)) (v : Fin n) :
    Finset (Fin n) :=
  (liveClosed G U v).filter fun u =>
    (symmDiff (liveClosed G U u) (liveClosed G U v)).card ≤ 3 * h

/-- What a rule stores. A rule 2 record holds `v`, `Q`, and `(u, N_H[u] \ Q, Q \ N_H[u])` for each `u` in
the group, by increasing label. -/
inductive RemovalRecord (n : ℕ) where
  | rule1 (v : Fin n) (nbr : Finset (Fin n))
  | rule2 (v : Fin n) (Q : Finset (Fin n)) (members : List (Fin n × Finset (Fin n) × Finset (Fin n)))

/-- One application of the rules: rule 1 at the smallest label if some vertex qualifies, otherwise rule 2
at the smallest label if some vertex qualifies, otherwise `none`. Returns the record and the new live set. -/
def reduceStep (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : ℕ) (U : Finset (Fin n)) :
    Option (RemovalRecord n × Finset (Fin n)) :=
  match (List.finRange n).find? (fun v => v ∈ U ∧ liveDeg G U v ≤ 20 * h) with
  | some v => some (.rule1 v (liveNbrs G U v), U.erase v)
  | none =>
    match (List.finRange n).find? (fun v => v ∈ U ∧ liveDeg G U v ≤ 2 * (groupB G h U v).card) with
    | some v =>
      some (.rule2 v (liveClosed G U v)
          (((List.finRange n).filter (· ∈ groupB G h U v)).map fun u =>
            (u, liveClosed G U u \ liveClosed G U v, liveClosed G U v \ liveClosed G U u)),
        U \ groupB G h U v)
    | none => none

/-- Apply the rules at most `fuel` times from `U`; the records in order, and the final live set. -/
def reduceAux (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : ℕ) :
    ℕ → Finset (Fin n) → List (RemovalRecord n) × Finset (Fin n)
  | 0, U => ([], U)
  | f + 1, U =>
    match reduceStep G h U with
    | none => ([], U)
    | some (r, U') =>
      let rest := reduceAux G h f U'
      (r :: rest.1, rest.2)

/-- The records of the whole procedure, in removal order. -/
def removalRecords (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : ℕ) : List (RemovalRecord n) :=
  (reduceAux G h n Finset.univ).1

/-- `V(H)`, the vertices left when the procedure stops; `K` is its complement. -/
def remainder (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : ℕ) : Finset (Fin n) :=
  (reduceAux G h n Finset.univ).2

/-- The stored row of a vertex in a record: `N_H(v)` for rule 1, `(Q ∪ plus) \ minus = N_H[u]` for rule 2. -/
def RemovalRecord.row : RemovalRecord n → Fin n → Option (Finset (Fin n))
  | .rule1 v nbr, x => if x = v then some nbr else none
  | .rule2 _ Q members, x => (members.find? (fun m => m.1 = x)).map fun m => (Q ∪ m.2.1) \ m.2.2

/-- The adjacency test computed from the records alone: the first record storing a row of `x` or `y`
decides. It has no access to `G`. -/
def adjOf : List (RemovalRecord n) → Fin n → Fin n → Bool
  | [], _, _ => false
  | r :: rs, x, y =>
    match r.row x with
    | some row => decide (y ∈ row)
    | none =>
      match r.row y with
      | some row => decide (x ∈ row)
      | none => adjOf rs x y

/-- The labels and identifiers a record stores. Rule 1: the vertex, its position, the rule, its neighbours.
Rule 2: the labels of `Q`, and per member its label, position, rule and group, and for each correction
coordinate a label and a sign. -/
def RemovalRecord.words : RemovalRecord n → ℕ
  | .rule1 _ nbr => 3 + nbr.card
  | .rule2 _ Q members => Q.card + (members.map fun m => 4 + 2 * (m.2.1.card + m.2.2.card)).sum

/-- The bits of a record list: each label or identifier takes `⌈log₂(n+1)⌉` bits. -/
def recordBits (n : ℕ) (rs : List (RemovalRecord n)) : ℕ :=
  (rs.map RemovalRecord.words).sum * Nat.clog 2 (n + 1)

/-- `|E(H[S])|`: the number of pairs of `S` adjacent in `G`. -/
def edgesAmong (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (S : Finset (Fin n)) : ℕ :=
  ((S ×ˢ S).filter fun p => p.1 < p.2 ∧ G.Adj p.1 p.2).card

/-- `M_v = (d_v choose 2) − |E(H[N_H(v)])|`, p.25, as a real number. -/
def deficitM (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)) (v : Fin n) : ℝ :=
  ((liveDeg G U v).choose 2 : ℝ) - (edgesAmong G (liveNbrs G U v) : ℝ)

end StreamColour


