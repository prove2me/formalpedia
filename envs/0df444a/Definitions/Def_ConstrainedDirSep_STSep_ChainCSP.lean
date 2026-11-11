-- Prove2me | Definitions.Def_ConstrainedDirSep_STSep_ChainCSP
-- name    : ConstrainedDirSep_STSep_ChainCSP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:06:37.95967+00:00
-- url     : https://prove2.me/theorems/fa600fd7-059a-4a29-b7d5-f0ae4392adbf
-- title:
--   Chain CSP instances, the chain promise, satisfying assignments, costs and encodings
-- statement:
--   A **Chain CSP instance** $I$ has variables $X_1,\dots,X_r$ (indexed $0,\dots,r-1$) with domains $[d_i]$, $d_i\ge1$, allowed sets $U_i\subseteq[d_i]$, and for every $i<j$ a finite set $Q_{ij}$ of well-ranged quadrant constraints on $(X_i,X_j)$ with window $W_{ij}$, two sets $F_{ij},B_{ij}\subseteq[d_i]\times[d_j]$ of marked points, and a loopless **target digraph** $\Pi$ on the variables. The **chain promise** (4) requires $F_{ij}\cap W_{ij}$ and $B_{ij}\cap W_{ij}$ to be increasing chains for every $i<j$ (`ChainCSP.WF`).
--
--   An assignment $x$ **satisfies** $I$ if $x_i\in U_i$ for every $i$, every constraint of every $Q_{ij}$ holds, and for every $i<j$
--   $$(x_i,x_j)\in F_{ij}\cap W_{ij}\iff ij\in A(\Pi),\qquad (x_i,x_j)\in B_{ij}\cap W_{ij}\iff ji\in A(\Pi).$$
--   The **total domain size** is $N=\sum_i d_i$. For unary costs $\omega_i(p)\in\mathbb Z_{\ge0}$ the cost of $x$ is $\sum_i\omega_i(x_i)$, and $\|\omega\|$ is the total length of the binary words of all $\omega_i(p)$, $p\in[d_i]$.
--
--   The instance is encoded explicitly: $r$, the $d_i$, the membership bits of every $U_i$ over $[d_i]$, of every $Q_{ij}$ over the list of all well-ranged constraints, of $F_{ij}$, $B_{ij}$ over $[d_i]\times[d_j]$, and the adjacency matrix of $\Pi$ (length polynomial in $N$). An assignment is output as the bit $1$ followed by $\mathrm{enc}(x_1),\dots,\mathrm{enc}(x_r)$.
--
--   **Formalization Note.** Entries $Q_{ij}$, $F_{ij}$, $B_{ij}$ with $i\not<j$ are required to be empty.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 15 (PDF 18), §4, problem Chain CSP, (4)–(6); p. 17 (PDF 20), Theorem 4.8 (N, costs, ‖ω‖)

import Mathlib
import Definitions.Def_ConstrainedDirSep_STSep_Separator
import Definitions.Def_ConstrainedDirSep_STSep_Encoding
import Definitions.Def_ConstrainedDirSep_STSep_Quadrant

set_option autoImplicit false

namespace ConstrainedDirSep.STSep

/-- **All well-ranged quadrant constraints on a pair with domains `[dX]`, `[dY]`**, in a fixed
order: every `Q↘_{a,b}` with `a ∈ [dX + 1]`, `b ∈ {0} ∪ [dY]`, then every `Q↖_{a,b}` with
`a ∈ {0} ∪ [dX]`, `b ∈ [dY + 1]` (§4, p. 14, PDF 17, (1)–(2)). A set of constraints is encoded by its
characteristic bits along this list ("at most `2(di + 1)(dj + 1)` quadrant constraints for a pair",
p. 15, PDF 18). -/
def allQuadrants (dX dY : ℕ) : List Quadrant :=
  ((rangeOne (dX + 1)).flatMap fun a => (List.range (dY + 1)).map fun b => Quadrant.se a b) ++
    ((List.range (dX + 1)).flatMap fun a => (rangeOne (dY + 1)).map fun b => Quadrant.nw a b)

/-- **All pairs of `[dX] × [dY]`**, row by row. -/
def gridPairs (dX dY : ℕ) : List (ℕ × ℕ) :=
  (rangeOne dX).flatMap fun p => (rangeOne dY).map fun q => (p, q)

/-- **A Chain CSP instance** (data). Olkowski, Ramanujan, *Constrained Directed Separation*, STOC
2027 submission (manuscript sha256 4dd06c29…), §4, p. 15 (PDF 18), problem *Chain CSP*: variables
`X_1, …, X_r` (indexed by `Fin r`) with domains `[d_i]`, allowed sets `U_i ⊆ [d_i]`, for `i < j` a
finite set `Q_ij` of quadrant constraints on `(X_i, X_j)` and two sets `F_ij`, `B_ij ⊆ [d_i] × [d_j]`
of marked points, and a target digraph `Π` on the variables.

**Formalization Note.** Variables are indexed by `Fin r` (0-based); domain values are the
integers `1, …, d_i` as in the paper. The entries `Q i j`, `F i j`, `B i j` with `¬ i < j` carry no
information and are required to be empty by `ChainCSP.WF`. -/
structure ChainCSP where
  /-- the number of variables -/
  r : ℕ
  /-- the domain sizes `d_i` -/
  d : Fin r → ℕ
  /-- the allowed sets `U_i` -/
  U : Fin r → Finset ℕ
  /-- the quadrant constraints `Q_ij` -/
  Q : Fin r → Fin r → Finset Quadrant
  /-- the forward marked points `F_ij` -/
  F : Fin r → Fin r → Finset (ℕ × ℕ)
  /-- the backward marked points `B_ij` -/
  B : Fin r → Fin r → Finset (ℕ × ℕ)
  /-- the target digraph `Π` on `[r]` -/
  Pi : Digraph (Fin r)

/-- **The window `W_ij` of a Chain CSP instance** (§4, p. 15, PDF 18). -/
def ChainCSP.W (I : ChainCSP) (i j : Fin I.r) : Set (ℕ × ℕ) :=
  window (I.Q i j) (I.d i) (I.d j)

/-- **Well-formed Chain CSP instance.** §4, p. 15 (PDF 18): nonempty domains (`d_i ≥ 1`),
`U_i ⊆ [d_i]`, thresholds in the ranges of (1)–(2), marked points in `[d_i] × [d_j]`, a loopless
target digraph, and the **chain promise** (4): `F_ij ∩ W_ij` and `B_ij ∩ W_ij` are increasing chains
for every `i < j`. -/
def ChainCSP.WF (I : ChainCSP) : Prop :=
  (∀ i, 1 ≤ I.d i) ∧
  (∀ i, ∀ p ∈ I.U i, 1 ≤ p ∧ p ≤ I.d i) ∧
  (∀ i j, ¬ i < j → I.Q i j = ∅ ∧ I.F i j = ∅ ∧ I.B i j = ∅) ∧
  (∀ i j, i < j → ∀ c ∈ I.Q i j, c.WellRanged (I.d i) (I.d j)) ∧
  (∀ i j, i < j → ∀ pq ∈ I.F i j ∪ I.B i j,
    1 ≤ pq.1 ∧ pq.1 ≤ I.d i ∧ 1 ≤ pq.2 ∧ pq.2 ≤ I.d j) ∧
  Loopless I.Pi ∧
  (∀ i j, i < j →
    IsIncreasingChain ((I.F i j : Set (ℕ × ℕ)) ∩ I.W i j) ∧
      IsIncreasingChain ((I.B i j : Set (ℕ × ℕ)) ∩ I.W i j))

/-- **Satisfying assignment of a Chain CSP instance.** §4, p. 15 (PDF 18): `x_i ∈ U_i` for every
`i`, every constraint in every `Q_ij` is satisfied, and for every `i < j`
(5) `(x_i, x_j) ∈ F_ij ∩ W_ij ⇔ ij ∈ A(Π)` and (6) `(x_i, x_j) ∈ B_ij ∩ W_ij ⇔ ji ∈ A(Π)`. -/
def ChainCSP.Satisfies (I : ChainCSP) (x : Fin I.r → ℕ) : Prop :=
  (∀ i, x i ∈ I.U i) ∧
  ∀ i j, i < j →
    (∀ c ∈ I.Q i j, c.Holds (x i) (x j)) ∧
    ((x i, x j) ∈ (I.F i j : Set (ℕ × ℕ)) ∩ I.W i j ↔ I.Pi.Adj i j) ∧
    ((x i, x j) ∈ (I.B i j : Set (ℕ × ℕ)) ∩ I.W i j ↔ I.Pi.Adj j i)

/-- **Total domain size** `N = ∑_{i=1}^r d_i` (§4, p. 15, PDF 18; Theorem 4.8, p. 17, PDF 20). -/
def ChainCSP.N (I : ChainCSP) : ℕ :=
  ∑ i, I.d i

/-- **Cost of an assignment** under unary costs `ω_i(p)` (Theorem 4.8, p. 17, PDF 20):
`∑_i ω_i(x_i)`. -/
def assignCost {r : ℕ} (ω : Fin r → ℕ → ℕ) (x : Fin r → ℕ) : ℕ :=
  ∑ i, ω i (x i)

/-- **Total binary encoding length of all unary costs** `‖ω‖` (Theorem 4.8, p. 17, PDF 20): the
sum of the lengths of the binary words `encNat (ω_i(p))` over `i` and `p ∈ [d_i]`. -/
def ChainCSP.costLength (I : ChainCSP) (ω : Fin I.r → ℕ → ℕ) : ℕ :=
  ∑ i, ((rangeOne (I.d i)).map fun p => (encNat (ω i p)).length).sum

/-- **Input word of a Chain CSP instance.** §4, p. 15 (PDF 18): "All sets are explicitly encoded
without repetitions." `r`, the domain sizes, the allowed sets as membership bits over `[d_i]`, then
for every `i < j` (lexicographic order) the constraint set `Q_ij` as membership bits over
`allQuadrants (d_i) (d_j)` and `F_ij`, `B_ij` as membership bits over `[d_i] × [d_j]`, and finally
the adjacency matrix of `Π`. The word has length polynomial in `N`. -/
noncomputable def encChainCSP (I : ChainCSP) : List Bool :=
  encNat I.r ++ (List.finRange I.r).flatMap (fun i => encNat (I.d i)) ++
    (List.finRange I.r).flatMap (fun i => charBits (· ∈ I.U i) (rangeOne (I.d i))) ++
    (List.finRange I.r).flatMap (fun i => (List.finRange I.r).flatMap fun j =>
      if i < j then
        charBits (· ∈ I.Q i j) (allQuadrants (I.d i) (I.d j)) ++
          charBits (· ∈ I.F i j) (gridPairs (I.d i) (I.d j)) ++
          charBits (· ∈ I.B i j) (gridPairs (I.d i) (I.d j))
      else []) ++
    adjBits I.Pi

/-- **Input word of a Chain CSP instance with unary costs** (Theorem 4.8, p. 17, PDF 20): the
instance, then the binary cost `ω_i(p)` for every `i` and `p ∈ [d_i]`. -/
noncomputable def encWChainCSP (I : ChainCSP) (ω : Fin I.r → ℕ → ℕ) : List Bool :=
  encChainCSP I ++ (List.finRange I.r).flatMap fun i => (rangeOne (I.d i)).flatMap fun p =>
    encNat (ω i p)

/-- **Output word of an assignment** `x = (x_1, …, x_r)`: the bit `true`, then `encNat (x_i)` for
every `i`. The output "no satisfying assignment" is `encNone = [false]`. -/
def encAssign {r : ℕ} (x : Fin r → ℕ) : List Bool :=
  true :: (List.finRange r).flatMap fun i => encNat (x i)

end ConstrainedDirSep.STSep


