-- Prove2me | Definitions.Def_ConstrainedDirSep_STSep_OrderedRep
-- name    : ConstrainedDirSep_STSep_OrderedRep
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:07:43.014193+00:00
-- url     : https://prove2.me/theorems/ce0dcfa1-78e9-4843-aee3-39a864066e97
-- title:
--   Ordered representations (Definition 5.1), feasible assignments, marked sets and encodings
-- statement:
--   An **ordered representation** $\rho$ of a digraph $D$ on $\{0,\dots,n-1\}$ with distinct terminals $s,t$ consists of a rank $\lambda\ge0$, domains $[d_1],\dots,[d_\lambda]$, an injective **candidate map** $(i,p)\mapsto v_i(p)\in V(D)\setminus\{s,t\}$ ($p\in[d_i]$), allowed sets $U_i\subseteq[d_i]$, and for every $i<j$ a finite set $Q_{ij}$ of well-ranged quadrant constraints with window $W_{ij}$ (`OrderedRep.WF`).
--
--   An assignment $x$ is **feasible** if $x_i\in U_i$ for every $i$ and every constraint of every $Q_{ij}$ holds; it selects $S(x)=\{v_i(x_i): i\in[\lambda]\}$. $\rho$ **represents** $S$ if some feasible $x$ has $S(x)=S$. The **marked sets** are $F_{ij}=\{(p,q): v_i(p)v_j(q)\in A(D)\}$ and $B_{ij}=\{(p,q): v_j(q)v_i(p)\in A(D)\}$, with $(p,q)\in[d_i]\times[d_j]$.
--
--   A representation is encoded by $\lambda$, the $d_i$, every candidate $v_i(p)$, the membership bits of every $U_i$ and of every $Q_{ij}$ ($i<j$); its **size** is the length of this word. A family is a $1$ before each member and a final $0$. The input word of the representation theorem is the digraph, $s$, $t$, the $n$ membership bits of the allowed set $\Lambda$, and $k$.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 18 (PDF 21), Definition 5.1; p. 23 (PDF 26), (11)–(12)

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Encoding
import Definitions.Def_ConstrainedDirSep_STSep_ChainCSP

set_option autoImplicit false

namespace ConstrainedDirSep.STSep

/-- **Ordered representation** (data). Olkowski, Ramanujan, *Constrained Directed Separation*,
STOC 2027 submission (manuscript sha256 4dd06c29…), Definition 5.1, p. 18 (PDF 21): a rank
`λ ≥ 0`, ordered domains `[d_1], …, [d_λ]`, a candidate map `(i, p) ↦ v_i(p) ∈ V(D)`, allowed sets
`U_i ⊆ [d_i]`, and for every `i < j` a finite set `Q_ij` of quadrant constraints on `(X_i, X_j)`.

**Formalization Note.** `D` has vertex set `Fin n`; positions `i` are `Fin lam` (0-based), domain
values are `1, …, d_i` as in the paper. `cand i p` is only meaningful for `p ∈ [d_i]`. -/
structure OrderedRep (n : ℕ) where
  /-- the rank `λ` -/
  lam : ℕ
  /-- the domain sizes `d_i` -/
  d : Fin lam → ℕ
  /-- the candidate map `(i, p) ↦ v_i(p)` -/
  cand : Fin lam → ℕ → Fin n
  /-- the allowed sets `U_i` -/
  U : Fin lam → Finset ℕ
  /-- the quadrant constraints `Q_ij` -/
  Q : Fin lam → Fin lam → Finset Quadrant

/-- **Well-formed ordered representation of `D` with terminals `s`, `t`** (Definition 5.1): every
candidate `v_i(p)` (`p ∈ [d_i]`) lies in `V(D) \ {s, t}`, the candidate map is injective on
`{(i, p) : p ∈ [d_i]}`, `U_i ⊆ [d_i]`, `Q_ij` is empty unless `i < j`, and every threshold lies in
the range of (1)–(2). -/
def OrderedRep.WF {n : ℕ} (ρ : OrderedRep n) (s t : Fin n) : Prop :=
  (∀ i p, 1 ≤ p → p ≤ ρ.d i → ρ.cand i p ≠ s ∧ ρ.cand i p ≠ t) ∧
  (∀ i p j q, 1 ≤ p → p ≤ ρ.d i → 1 ≤ q → q ≤ ρ.d j → ρ.cand i p = ρ.cand j q → i = j ∧ p = q) ∧
  (∀ i, ∀ p ∈ ρ.U i, 1 ≤ p ∧ p ≤ ρ.d i) ∧
  (∀ i j, ¬ i < j → ρ.Q i j = ∅) ∧
  (∀ i j, i < j → ∀ c ∈ ρ.Q i j, c.WellRanged (ρ.d i) (ρ.d j))

/-- **Feasible assignment** (Definition 5.1): `x_i ∈ U_i` for every `i`, and `x` satisfies every
constraint of every `Q_ij`. -/
def OrderedRep.Feasible {n : ℕ} (ρ : OrderedRep n) (x : Fin ρ.lam → ℕ) : Prop :=
  (∀ i, x i ∈ ρ.U i) ∧ ∀ i j, i < j → ∀ c ∈ ρ.Q i j, c.Holds (x i) (x j)

/-- **The selected set `S(x) = {v_i(x_i) : i ∈ [λ]}`** (Definition 5.1). -/
def OrderedRep.selected {n : ℕ} (ρ : OrderedRep n) (x : Fin ρ.lam → ℕ) : Finset (Fin n) :=
  Finset.univ.image fun i => ρ.cand i (x i)

/-- **`ρ` represents `S`** (Definition 5.1): some feasible assignment `x` has `S(x) = S`. -/
def OrderedRep.Represents {n : ℕ} (ρ : OrderedRep n) (S : Finset (Fin n)) : Prop :=
  ∃ x : Fin ρ.lam → ℕ, ρ.Feasible x ∧ ρ.selected x = S

/-- **The window `W_ij`** of the representation (Definition 5.1, "with window `W_ij` as in
Section 4"). -/
def OrderedRep.W {n : ℕ} (ρ : OrderedRep n) (i j : Fin ρ.lam) : Set (ℕ × ℕ) :=
  window (ρ.Q i j) (ρ.d i) (ρ.d j)

/-- **Forward marked set** `F_ij = {(p, q) : v_i(p)v_j(q) ∈ A(D)}` (Definition 5.1; (11), p. 23). -/
def OrderedRep.Fwd {n : ℕ} (ρ : OrderedRep n) (D : Digraph (Fin n)) (i j : Fin ρ.lam) :
    Set (ℕ × ℕ) :=
  {pq | 1 ≤ pq.1 ∧ pq.1 ≤ ρ.d i ∧ 1 ≤ pq.2 ∧ pq.2 ≤ ρ.d j ∧ D.Adj (ρ.cand i pq.1) (ρ.cand j pq.2)}

/-- **Backward marked set** `B_ij = {(p, q) : v_j(q)v_i(p) ∈ A(D)}` (Definition 5.1; (12)). -/
def OrderedRep.Bwd {n : ℕ} (ρ : OrderedRep n) (D : Digraph (Fin n)) (i j : Fin ρ.lam) :
    Set (ℕ × ℕ) :=
  {pq | 1 ≤ pq.1 ∧ pq.1 ≤ ρ.d i ∧ 1 ≤ pq.2 ∧ pq.2 ≤ ρ.d j ∧ D.Adj (ρ.cand j pq.2) (ρ.cand i pq.1)}

/-- **Encoding of an ordered representation**: `λ`, the domain sizes, every candidate `v_i(p)`
(`p ∈ [d_i]`), the allowed sets as membership bits over `[d_i]`, and for every `i < j` the
constraint set `Q_ij` as membership bits over `allQuadrants (d_i) (d_j)`. Its length is the size of
the representation. -/
noncomputable def encRep {n : ℕ} (ρ : OrderedRep n) : List Bool :=
  encNat ρ.lam ++ (List.finRange ρ.lam).flatMap (fun i => encNat (ρ.d i)) ++
    (List.finRange ρ.lam).flatMap (fun i => (rangeOne (ρ.d i)).flatMap fun p =>
      encNat (ρ.cand i p).val) ++
    (List.finRange ρ.lam).flatMap (fun i => charBits (· ∈ ρ.U i) (rangeOne (ρ.d i))) ++
    (List.finRange ρ.lam).flatMap fun i => (List.finRange ρ.lam).flatMap fun j =>
      if i < j then charBits (· ∈ ρ.Q i j) (allQuadrants (ρ.d i) (ρ.d j)) else []

/-- **Output word of a family of representations** `ρ_1, …, ρ_m`: for each, the bit `true` and
`encRep ρ`; then `false`. -/
noncomputable def encRepFamily {n : ℕ} (R : List (OrderedRep n)) : List Bool :=
  R.flatMap (fun ρ => true :: encRep ρ) ++ [false]

/-- **Input word of the representation theorem** (Theorem 5.2, p. 18, PDF 21): the digraph `D` on
`Fin n` (adjacency matrix), the terminals `s`, `t`, the allowed set `Λ` as `n` membership bits, and
`k`. -/
noncomputable def encRepInput {n : ℕ} (D : Digraph (Fin n)) (s t : Fin n) (Λ : Finset (Fin n))
    (k : ℕ) : List Bool :=
  encDigraph n D ++ encNat s.val ++ encNat t.val ++ charBits (· ∈ Λ) (List.finRange n) ++ encNat k

end ConstrainedDirSep.STSep


