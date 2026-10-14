-- Prove2me | Definitions.Def_SeymourSecondNeighborhood_Image
-- name    : SeymourSecondNeighborhood_Image
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-13T20:19:29.480423+00:00
-- url     : https://prove2.me/theorems/3b47b0d2-b661-4801-9501-5bd740960c27
-- title:
--   Image operators, subset deficit, strict expansion, transitive-tournament blow-up and the conflict structure of two families of pairs
-- statement:
--   Auxiliary notions for the lemma chain of the manuscript *A proof of Seymour's second-neighborhood conjecture* (OpenAI, September 2026), over the mission block `SeymourSecondNeighborhood`.
--
--   For a relation $r$ on a finite type $V$ and $U\subseteq V$: `fwd r U` is the one-step image $F(U)=\{y : \exists x\in U,\ x\to y\}$ (the union of the out-neighborhoods; $U$ is not subtracted). `PosIndeg r` says every vertex has an in-neighbor. `SubsetDeficit r` is the subset deficit (3) of the manuscript: $|F^2(S)\setminus F(S)|<|F(S)\setminus S|$ for every nonempty proper $S$. `StrictExpander r` is the strict inequality (2)/(17): $|U|+|F^2(U)|<2|F(U)|$ for every nonempty proper $U$. `blowup r m` is the lexicographic product $D[T_m]$ on $V\times\mathrm{Fin}\,m$: each vertex is replaced by a transitive tournament on $m$ labels (arcs from smaller to larger labels) and each arc $v\to w$ of $D$ becomes all arcs from the block at $v$ to the block at $w$.
--
--   In the namespace `Pruning`, for an arbitrary relation `arrow` on a finite type $X$ and families $R,C\subseteq X\times X$: a left member $(p,j)$ and a right member $(i,s)$ `Conflict` when $p\to i$ and $s\to j$; $(p,j)$ `CoversL` the point $(i,j)$ when $p\to i$, and $(i,s)$ `CoversR` the point $(i,j)$ when $s\to j$; `conflicts arrow R C` is the set of conflicting pairs; `pointsZ` $=\{(i,j)\}$ and `pointsH` $=\{(p,s)\}$ collect the points determined by the conflicts; and `uncovered arrow R C R' C'` is the set of points of $Z$ covered by no member of $R'\cup C'$. These are exactly the objects of the pruning lemma (Lemma 3.1 of the manuscript).
-- source:
--   Definitions following OpenAI, *A proof of Seymour's second-neighborhood conjecture*, preprint, September 23, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/paper.pdf (Sections 2–4). Subset image operators as in T. Seacrest, arXiv:1808.06293; blow-up as in Brantner–Brockman–Kay–Snively, Involve 2 (2009) 387–395.

import Mathlib
import Definitions.Def_SeymourSecondNeighborhood

/-!
# Second-neighborhood mission: image operators, subset deficit, strict expansion, blow-up,
and the conflict structure for the pruning lemma

Auxiliary notions used to state the lemmas of the manuscript
*A proof of Seymour's second-neighborhood conjecture* (OpenAI, 2026).
-/

noncomputable section

open Finset

namespace OAI.SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One-step image `F(U) = {y | ∃ x ∈ U, x → y}` (the union of the out-neighborhoods; `U` is not
subtracted). -/
def fwd (r : V → V → Prop) (U : Finset V) : Finset V := by
  classical
  exact univ.filter (fun y => ∃ x ∈ U, r x y)

/-- Every vertex has an in-neighbor. -/
def PosIndeg (r : V → V → Prop) : Prop := ∀ v, ∃ u, r u v

/-- The subset deficit (3): `|F²(S) \ F(S)| < |F(S) \ S|` for every nonempty proper `S`. -/
def SubsetDeficit (r : V → V → Prop) : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ univ → (fwd r (fwd r S) \ fwd r S).card < (fwd r S \ S).card

/-- Strict expansion (2)/(17): `|U| + |F²(U)| < 2 |F(U)|` for every nonempty proper `U`. -/
def StrictExpander (r : V → V → Prop) : Prop :=
  ∀ U : Finset V, U.Nonempty → U ≠ univ → U.card + (fwd r (fwd r U)).card < 2 * (fwd r U).card

/-- The lexicographic blow-up `D[T_m]`: each vertex is replaced by a transitive tournament on
`Fin m` (arcs from smaller to larger labels), and every arc `v → w` of `D` becomes all arcs from the
block at `v` to the block at `w`. -/
def blowup (r : V → V → Prop) (m : ℕ) : V × Fin m → V × Fin m → Prop :=
  fun x y => r x.1 y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

end OAI.SeymourSecondNeighborhood

namespace OAI.SeymourSecondNeighborhood.Pruning

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A left member `(p, j)` and a right member `(i, s)` conflict when `p → i` and `s → j`. -/
def Conflict (arrow : X → X → Prop) (l c : X × X) : Prop := arrow l.1 c.1 ∧ arrow c.2 l.2

/-- A left member `(p, j)` covers the point `(i, j)` when `p → i`. -/
def CoversL (arrow : X → X → Prop) (l z : X × X) : Prop := z.2 = l.2 ∧ arrow l.1 z.1

/-- A right member `(i, s)` covers the point `(i, j)` when `s → j`. -/
def CoversR (arrow : X → X → Prop) (c z : X × X) : Prop := z.1 = c.1 ∧ arrow c.2 z.2

/-- The conflicting pairs of two families. -/
def conflicts (arrow : X → X → Prop) (R C : Finset (X × X)) : Finset ((X × X) × (X × X)) := by
  classical
  exact (R ×ˢ C).filter (fun lc => Conflict arrow lc.1 lc.2)

/-- `Z = {(i, j) : some (p, j) ∈ R conflicts with some (i, s) ∈ C}`. -/
def pointsZ (arrow : X → X → Prop) (R C : Finset (X × X)) : Finset (X × X) :=
  (conflicts arrow R C).image (fun lc => (lc.2.1, lc.1.2))

/-- `H = {(p, s) : some (p, j) ∈ R conflicts with some (i, s) ∈ C}`. -/
def pointsH (arrow : X → X → Prop) (R C : Finset (X × X)) : Finset (X × X) :=
  (conflicts arrow R C).image (fun lc => (lc.1.1, lc.2.2))

/-- The points of `Z` covered by no member of `R' ∪ C'`. -/
def uncovered (arrow : X → X → Prop) (R C R' C' : Finset (X × X)) : Finset (X × X) := by
  classical
  exact (pointsZ arrow R C).filter
    (fun z => (∀ l ∈ R', ¬ CoversL arrow l z) ∧ (∀ c ∈ C', ¬ CoversR arrow c z))

end OAI.SeymourSecondNeighborhood.Pruning


