-- Prove2me | Definitions.Def_MCPoise_MRIn
-- name    : MCPoise_MRIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:37.932334+00:00
-- url     : https://prove2.me/theorems/f6e5c0ab-09d9-42b3-bf21-070d714af479
-- title:
--   The explicit input of Lemma 2.7
-- statement:
--   The input of multi-root rounding: the graph, the list of roots with terminal sets, the rational parameter $L_\Delta$, the natural number $L'_d$, and the lists of nonzero entries of $\hat x$ and $\hat f$. It is **feasible** when the listed vector is feasible for Multiroot-LP, $r_j \notin S_j$ for each $j$, and $L_\Delta \ge 0$.
--
--   **Formalization Note** The list of entries makes the support part of the input length. $L_\Delta \ge 0$ follows from the degree constraint unless $V$ is empty.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.7, p.15

import Mathlib
import Definitions.Def_MCPoise_Inst
import Definitions.Def_MCPoise_MultirootLP
import Definitions.Def_MCPoise_encIn
import Definitions.Def_MCPoise_JLPOut
import Definitions.Def_OnlineCRS_Combine_encRat

namespace MCPoise

open OnlineCRS.Combine

/-- **The input of Lemma 2.7.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.7, p.15: "a graph G = (V, E), roots r₁, . . . , r_µ ∈ V, terminal sets S_j ⊆ V \ {r_j} ..., parameters L_∆,
L′_d, and an explicitly represented feasible solution to (Multiroot-LP) with polynomial support".

`groups` lists `(r_j, S_j)`; `xh` has entries `(u, v, j, x̂_{uv,j})`; `fh` has entries `(j, t, p, f̂_p)`.

**Formalization Note.** A variable with no entry is `0` and repeated entries add, so the support is the length of the lists,
which is part of the input length. `L_∆` is rational. `L′_d` is a natural number: it bounds a number of edges, and a rational
`L′_d` has the same `P^j_t` as its floor, for which the conclusion of Lemma 2.7 is stronger. -/
structure MRIn where
  n : ℕ
  edges : List (Fin n × Fin n)
  groups : List (Fin n × List (Fin n))
  LΔ : ℚ
  Lp : ℕ
  xh : List (ℕ × ℕ × ℕ × ℚ)
  fh : List (ℕ × ℕ × List ℕ × ℚ)

/-- The graph of the input. -/
abbrev MRIn.graph (R : MRIn) : SimpleGraph (Fin R.n) := listGraph R.edges

/-- The root `r_j`. -/
def MRIn.r (R : MRIn) (j : Fin R.groups.length) : Fin R.n := (R.groups.get j).1

/-- The terminal set `S_j`. -/
def MRIn.S (R : MRIn) (j : Fin R.groups.length) : Finset (Fin R.n) := (R.groups.get j).2.toFinset

/-- The value of `x̂_{e,j}` read from the input. -/
noncomputable def MRIn.xVal (R : MRIn) (e : Sym2 (Fin R.n)) (j : Fin R.groups.length) : ℝ :=
  ((R.xh.filter fun a => s(a.1, a.2.1) = e.map Fin.val ∧ a.2.2.1 = j.val).map
    fun a => (a.2.2.2 : ℝ)).sum

/-- The value of `f̂_p` for the terminal `t` of the group `j` read from the input. -/
noncomputable def MRIn.fVal (R : MRIn) (j : Fin R.groups.length) (t : Fin R.n)
    (p : List (Fin R.n)) : ℝ :=
  ((R.fh.filter fun a => a.1 = j.val ∧ a.2.1 = t.val ∧ a.2.2.1 = p.map Fin.val).map
    fun a => (a.2.2.2 : ℝ)).sum

/-- The input carries a feasible solution of Multiroot-LP, with `r_j ∉ S_j` for every `j`. `0 ≤ L_∆` follows from the degree
constraint unless `V` is empty, and it excludes only that degenerate corner. -/
def MRIn.Feasible (R : MRIn) : Prop :=
  (∀ j, R.r j ∉ R.S j) ∧ 0 ≤ R.LΔ ∧
    MultirootLP R.graph R.r R.S (R.LΔ : ℝ) R.Lp R.xVal R.fVal

/-- **Encoding of the input of Lemma 2.7.** `n` in unary, then the lists, each length-prefixed, numbers and rationals in
binary. Injective (`Solutions/verification/MCPoise_sanity.lean`). -/
def encMRIn (R : MRIn) : List Sym :=
  EulerSparsify.joinW
    ([List.replicate R.n 0] ++ tokPairs (valPairs R.edges) ++
      ReserveLB.tokList (fun g : Fin R.n × List (Fin R.n) =>
        [encNat g.1.val] ++ tokNats (g.2.map Fin.val)) R.groups ++
      [encRat R.LΔ, encNat R.Lp] ++
      ReserveLB.tokList (fun a : ℕ × ℕ × ℕ × ℚ =>
        [encNat a.1, encNat a.2.1, encNat a.2.2.1, encRat a.2.2.2]) R.xh ++
      ReserveLB.tokList (fun a : ℕ × ℕ × List ℕ × ℚ =>
        [encNat a.1, encNat a.2.1] ++ tokNats a.2.2.1 ++ [encRat a.2.2.2]) R.fh)

end MCPoise


