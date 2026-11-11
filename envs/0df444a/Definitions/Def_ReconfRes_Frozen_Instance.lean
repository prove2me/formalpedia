-- Prove2me | Definitions.Def_ReconfRes_Frozen_Instance
-- name    : ReconfRes_Frozen_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:22:34.265722+00:00
-- url     : https://prove2.me/theorems/eee0825f-4a35-4e8c-95fe-65216ca4f672
-- title:
--   Frozen lean reachability: instances (F, w, s, R1, R2) with w and s in unary, their encoding, and the promises of Theorem 3.63 and Corollary 3.64
-- statement:
--   An instance of **frozen lean reachability** for a fixed locality $k$ is a CNF formula $F$, a width bound $w$ and a size budget $s$ written in unary, and two refutations $R_1$, $R_2$ given explicitly; the answer is yes iff $R_1$ and $R_2$ are vertices of $G^{fr}_k(F,w,s)$ lying in one connected component:
--   $$\mathrm{FrozenReach}_k(F,w,s,R_1,R_2)\iff R_1,R_2\in V(G^{fr}_k(F,w,s))\ \wedge\ R_1\leftrightsquigarrow R_2 .$$
--   The **one-copy promise** (Corollary 3.64): $F$ is Horn; $R_1$, $R_2$ are vertices whose axiom multiset is $F$ with every multiplicity one; $s=2|F|-1$; $w=\max_{C\in F}|C|$; every refutation reachable from either endpoint is a read-once tree without weakening. The **prescribed-inventory promise** (Theorem 3.63): $F$ is Horn; $R_1$, $R_2$ are vertices with the same axiom multiset of $\alpha$ occurrences; $s=2\alpha-1$; $w$ is two above the maximum axiom width; every reachable refutation is read-once without weakening.
--
--   **Formalization Note.** Variables are natural numbers. The encoding is injective and self-delimiting: binary numerals `encNat` for variables, node counts and the sink; $w$ and $s$ in unary ($w$ ones and a zero); a clause as its sorted positive and negative variable lists; a formula as its clause count and its clause codes in increasing lexicographic order; a refutation as node count, sink, adjacency matrix and labels. The adjacency matrix makes a refutation's code at most quadratically longer than an edge list, which changes no polynomial bound. $s=2|F|-1$ is written $s+1=2|F|$ (no natural-number truncation).
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), p. 19 (unary bounds); p. 22 (reachability problem); p. 82, Theorem 3.63; p. 83, Corollary 3.64

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_ReconfRes_Frozen_Refutation
import Definitions.Def_ReconfRes_Frozen_FrozenGraph

open MultiplierAssoc206.Resolution OptimalQueuingComplexity.Restless

namespace ReconfRes.Frozen

/-!
# Frozen lean reachability: instances, their encoding, and the promises of Theorem 3.63 and
Corollary 3.64

Myrisiotis, *Reconfiguring Resolution Refutations*, STOC 2027 submission, p. 19 (bounds in
unary), p. 22 (the reachability problem), p. 82 (Theorem 3.63), p. 83 (Corollary 3.64).

An instance is a CNF formula `F` over the variables `ℕ`, a width bound `w`, a size budget `s`
and two refutations `R₁`, `R₂` given explicitly. The locality `k` is not part of the input: each
`k` gives its own decision problem `FrozenReach k`.

The encoding is injective and self-delimiting piece by piece: natural numbers (variables, node
counts, the sink) in the binary numeral `encNat`; `w` and `s` in unary (`w` ones and a zero); a
set of variables as its size followed by its elements in increasing order; a clause as its set of
positive variables followed by its set of negative variables; a formula as its number of clauses
followed by the codes of its clauses in increasing lexicographic order; a refutation as its node
count, its sink, its adjacency matrix (`n²` bits, row by row) and the codes of its node labels.
-/

/-- Unary numeral: `w` ones followed by a zero. -/
def encUnary (w : ℕ) : List Bool := List.replicate w true ++ [false]

/-- A finite set of variables: its size, then its elements in increasing order. -/
def encVarSet (S : Finset ℕ) : List Bool :=
  encNat S.card ++ (S.sort (· ≤ ·)).flatMap encNat

/-- A clause: the set of its positive variables, then the set of its negative variables. -/
def encClause (C : Clause ℕ) : List Bool :=
  encVarSet ((C.filter fun l => l.2 = true).image Prod.fst) ++
    encVarSet ((C.filter fun l => l.2 = false).image Prod.fst)

/-- A CNF formula: its number of clauses, then its clause codes in increasing lexicographic
order. -/
def encCNF (F : CNF ℕ) : List Bool :=
  encNat F.card ++ ((F.image encClause).sort (· ≤ ·)).flatten

/-- A refutation: node count, sink, adjacency matrix, node labels. -/
def encProofDag (R : ProofDag ℕ) : List Bool :=
  encNat R.n ++ encNat R.sink.val ++
    (List.finRange R.n).flatMap (fun i => (List.finRange R.n).map fun j => decide ((i, j) ∈ R.edges)) ++
    (List.finRange R.n).flatMap fun i => encClause (R.label i)

/-- An instance `(F, w, s, R₁, R₂)` of frozen lean reachability. -/
structure Instance where
  /-- the formula -/
  F : CNF ℕ
  /-- the width bound (written in unary) -/
  w : ℕ
  /-- the size budget (written in unary) -/
  s : ℕ
  /-- the first endpoint -/
  R₁ : ProofDag ℕ
  /-- the second endpoint -/
  R₂ : ProofDag ℕ

/-- The encoding of an instance, with `w` and `s` in unary. -/
def encInstance (x : Instance) : List Bool :=
  encCNF x.F ++ encUnary x.w ++ encUnary x.s ++ encProofDag x.R₁ ++ encProofDag x.R₂

/-- Frozen lean reachability for the locality `k`: `R₁` and `R₂` are vertices of
`G^fr_k(F,w,s)` lying in one connected component (refutations up to renaming of nodes). -/
def FrozenReach (k : ℕ) (x : Instance) : Prop :=
  IsVertex x.F x.w x.s x.R₁ ∧ IsVertex x.F x.w x.s x.R₂ ∧
    FrozenConnected k x.F x.w x.s x.R₁ x.R₂

/-- The promise of Corollary 3.64 (one-copy instances) for the locality `k`: `F` is Horn; both
endpoints are vertices of `G^fr_k(F,w,s)` whose axiom multiset is `F` with every multiplicity one
(exactly one axiom node per clause of `F` and no other axiom node); `s = 2|F| − 1`;
`w = max_{C∈F} |C|`; and every refutation reachable from either endpoint is a read-once tree
without weakening. -/
def OneCopy (k : ℕ) (x : Instance) : Prop :=
  IsHorn x.F ∧
  IsVertex x.F x.w x.s x.R₁ ∧ IsVertex x.F x.w x.s x.R₂ ∧
  x.R₁.axiomMultiset = x.F.val ∧ x.R₂.axiomMultiset = x.F.val ∧
  x.s + 1 = 2 * x.F.card ∧
  x.w = cnfWidth x.F ∧
  (∀ R, FrozenConnected k x.F x.w x.s x.R₁ R → R.IsReadOnce) ∧
  (∀ R, FrozenConnected k x.F x.w x.s x.R₂ R → R.IsReadOnce)

/-- The maximum width of a clause of a multiset of clauses (`0` when empty). -/
def maxWidth {V : Type} (M : Multiset (Clause V)) : ℕ := (M.map Finset.card).sup

/-- The promise of Theorem 3.63 for the locality `k`: `F` is Horn; both endpoints are vertices of
`G^fr_k(F,w,s)` with the same axiom multiset (prescribed inventory) of `α` source occurrences;
`s = 2α − 1`; `w` is two above the maximum axiom width; and every refutation reachable from either
endpoint is a read-once tree without weakening. -/
def PrescribedInventory (k : ℕ) (x : Instance) : Prop :=
  IsHorn x.F ∧
  IsVertex x.F x.w x.s x.R₁ ∧ IsVertex x.F x.w x.s x.R₂ ∧
  x.R₁.axiomMultiset = x.R₂.axiomMultiset ∧
  x.s + 1 = 2 * Multiset.card x.R₁.axiomMultiset ∧
  x.w = maxWidth x.R₁.axiomMultiset + 2 ∧
  (∀ R, FrozenConnected k x.F x.w x.s x.R₁ R → R.IsReadOnce) ∧
  (∀ R, FrozenConnected k x.F x.w x.s x.R₂ R → R.IsReadOnce)

end ReconfRes.Frozen


