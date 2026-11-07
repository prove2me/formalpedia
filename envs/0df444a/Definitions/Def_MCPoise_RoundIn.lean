-- Prove2me | Definitions.Def_MCPoise_RoundIn
-- name    : MCPoise_RoundIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:53.863209+00:00
-- url     : https://prove2.me/theorems/5f032097-736d-4055-bd3b-5be6ae699d53
-- title:
--   Input and output of simultaneous rounding
-- statement:
--   The input of Lemma 2.11: for each terminal label, the list of paths $Q^t_j$ with their rational weights, and $L'_d$. The output has one index for each label, which picks a path. The module also defines the graph $H$ of the union of a family of paths, in which an edge used by several paths counts once, and the number $|\delta(v) \cap E(p)|$ of edges of a path at a vertex.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.11, p.19; p.36

import Mathlib
import Definitions.Def_MCPoise_IsPathIn
import Definitions.Def_MCPoise_encIn
import Definitions.Def_MCPoise_JLPOut
import Definitions.Def_OnlineCRS_Combine_encRat

namespace MCPoise

open OnlineCRS.Combine

/-- The graph of the edges of a family of paths: `H := ∪ P_{j,t}` of Lemma 2.11, p.19. An edge shared by several paths is one edge. -/
def pathsGraph {V : Type*} (ps : List (List V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ p ∈ ps, s(u, v) ∈ pEdges p
  symm := ⟨fun u v h => ⟨h.1.symm, by simpa [Sym2.eq_swap (a := u) (b := v)] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **The input of Lemma 2.11.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.11, p.19: "the path sets Q^t_j and fractional weights y^{j,t}_p constructed in Stage 1".

`labels` has one entry for each terminal label `(j, t)`, `j ∈ [µ]`, `t ∈ S′_j`: the list of pairs `(p, y^{j,t}_p)`, `p ∈ Q^t_j`. `Lp` is `L′_d`.

**Formalization Note.** The label `(j, t)` is its position in the list; Lemma 2.11's rounding does not read `j` or `t`. -/
structure RoundIn where
  n : ℕ
  labels : List (List (List (Fin n) × ℚ))
  Lp : ℕ

/-- The path chosen for the label `l` by the output `out` of Lemma 2.11: the entry of `labels[l]` at position `out[l]`. -/
def RoundIn.chosen (R : RoundIn) (out : List ℕ) (l : ℕ) : List (Fin R.n) :=
  (((R.labels.getD l []).map Prod.fst).getD (out.getD l 0) [])

/-- The number of edges of the path `p` incident to `v`: `|δ_G(v) ∩ E(p)|` (p.36). -/
def pInc {V : Type*} [DecidableEq V] (v : V) (p : List V) : ℕ :=
  (pEdges p).countP fun e => v ∈ e

/-- **Encoding of the input of Lemma 2.11:** "the encoding length of the path sets and their fractional weights". `n` in unary,
then the labels, paths and rational weights, then `L′_d`. Injective (`Solutions/verification/MCPoise_sanity.lean`). -/
def encRoundIn (R : RoundIn) : List Sym :=
  EulerSparsify.joinW
    ([List.replicate R.n 0] ++
      ReserveLB.tokList (ReserveLB.tokList fun a : List (Fin R.n) × ℚ =>
        tokNats (a.1.map Fin.val) ++ [encRat a.2]) R.labels ++
      [encNat R.Lp])

/-- **Encoding of a list of indices,** the output of Lemma 2.11. Length first, then binary. Injective. -/
def encIdx (l : List ℕ) : List Sym :=
  EulerSparsify.joinW (tokNats l)

end MCPoise


