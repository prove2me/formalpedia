-- Prove2me | Definitions.Def_RepellingPairs_Config
-- name    : RepellingPairs_Config
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:22.553421+00:00
-- url     : https://prove2.me/theorems/98b51ee8-d360-4df8-b26c-849b0a47b872
-- title:
--   Chord configurations, the metric $\mathrm{dist}_C$, dominance and uncrossing
-- statement:
--   A **configuration** $C$ on $n$ points of a circle is a multiset of unordered pairs, called chords. For each point $i$ the bar $\bar i$ lies between $i$ and $i+1$. The cut $(\bar i,\bar j)$ separates $\{i+1,\dots,j\}$ from $\{j+1,\dots,i\}$, and $\mathrm{dist}_C(\bar i,\bar j)$ is the number of chords with one end on each side. **$C$ dominates $C'$**, written $C\succeq C'$, if $\mathrm{dist}_C\ge\mathrm{dist}_{C'}$ at every pair of bars, and $C\succ C'$ if in addition the inequality is strict at some pair.
--
--   Chords $(x,y),(z,w)$ **cross** if their four distinct ends alternate on the circle. An **uncrossing** replaces them by $(x,z),(y,w)$ or by $(x,w),(y,z)$. The **degenerate move** replaces $(x,y),(x,w)$, with $x\notin\{y,w\}$, by $(x,x),(y,w)$. $C\to C'$ means that a finite sequence of these moves leads from $C$ to $C'$. The **degree** of a point is the number of chord ends at it, a loop counting twice.
--
--   This is the language of §3.1 and §3.4, in which the flow statement of Theorem 1 becomes a statement about chords.
--
--   **Formalization Note** The page says "a set of chords"; a flow can send two units along one pair, so a configuration is a multiset. The points $1,\dots,n$ of the page are $0,\dots,n-1$. The degenerate move does not appear on the page under that name; it is the image of a printed uncrossing under the vertex splitting of p.13, and the correction on Lemma 10 explains why it is needed. A loop crosses no cut.
-- source:
--   Chen, Pylyavskyy, Tan, Paths and Intersections: Repelling Pairs, arXiv:2607.02883 (version of October 23, 2026), §3.1, p.8; §3.4, p.13

import Mathlib
import Definitions.Def_RepellingPairs_CyclicallyOrdered

set_option autoImplicit false

namespace RepellingPairs

/-- A configuration of chords on the points `Fin n`, §3.1, p.8. Chen, Pylyavskyy, Tan, arXiv:2607.02883
(version of October 23, 2026), §3.1, p.8.

**Formalization Note.** The page says "a set of chords", but a flow can send two units along one pair, so
a configuration is a multiset of unordered pairs; the chord `s(t, t)` is the image of a trivial path. The
points `1, …, n` of the page are `0, …, n - 1`, and increasing index is the direction the page calls
clockwise. -/
abbrev Config (n : ℕ) : Type := Multiset (Sym2 (Fin n))

namespace Config

variable {n : ℕ}

/-- The number of ends of a chord at the point `t`; a loop at `t` has two. -/
def chordDeg (t : Fin n) : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun a b => (if a = t then 1 else 0) + (if b = t then 1 else 0),
    fun _ _ => Nat.add_comm _ _⟩

/-- The total number of chord ends of `C` at `t`. -/
def deg (C : Config n) (t : Fin n) : ℕ := (C.map (chordDeg t)).sum

/-- Membership in the set of points `{i + 1, …, j}` (cyclically), one side of the cut `(ī, j̄)`. The bar
`ī` lies between the points `i` and `i + 1`, so `i = j` gives the empty side. -/
def onSide (i j a : Fin n) : Bool :=
  if i ≤ j then decide (i < a ∧ a ≤ j) else decide (i < a ∨ a ≤ j)

/-- `1` if the chord crosses the cut `(ī, j̄)`, that is, has its two ends on different sides of it, and
`0` otherwise. A loop crosses no cut. -/
def chordCross (i j : Fin n) : Sym2 (Fin n) → ℕ :=
  Sym2.lift ⟨fun a b => if onSide i j a = onSide i j b then 0 else 1, fun _ _ => by simp [eq_comm]⟩

/-- `dist_C(ī, j̄)`: the number of chords of `C`, with multiplicity, crossing the cut `(ī, j̄)`. -/
def dist (C : Config n) (i j : Fin n) : ℕ := (C.map (chordCross i j)).sum

/-- `C ⪰ C′`: "for every pair ī, j̄, dist_C(ī, j̄) ≥ dist_C′(ī, j̄)" (p.8). -/
def Dominates (C C' : Config n) : Prop := ∀ i j, C'.dist i j ≤ C.dist i j

/-- `C ≻ C′`: `C ⪰ C′` and some cut has `dist_C(ī, j̄) > dist_C′(ī, j̄)` (p.8). -/
def StrictlyDominates (C C' : Config n) : Prop :=
  Dominates C C' ∧ ∃ i j, C'.dist i j < C.dist i j

/-- The chords `(x, y)` and `(z, w)` cross: their four distinct endpoints alternate on the circle (p.8). -/
def ChordsCross (x y z w : Fin n) : Prop :=
  CyclicallyOrdered x z y w ∨ CyclicallyOrdered x w y z

/-- `C₁` is obtained from `C` by uncrossing a crossing pair `(x, y), (z, w)` into `(x, z), (y, w)` or into
`(x, w), (y, z)` (p.8). -/
def UncrossStep (C C₁ : Config n) : Prop :=
  ∃ (x y z w : Fin n) (rest : Config n), ChordsCross x y z w ∧
    C = s(x, y) ::ₘ s(z, w) ::ₘ rest ∧
    (C₁ = s(x, z) ::ₘ s(y, w) ::ₘ rest ∨ C₁ = s(x, w) ::ₘ s(y, z) ::ₘ rest)

/-- The degenerate move `(x, y), (x, w) → (x, x), (y, w)`, with `x ∉ {y, w}`. It is the image of a printed
uncrossing under the vertex splitting of p.13, where the two chords at `x` have distinct points of the
split vertex as ends and cross. It is needed once `C′` has loops. Not on the page as a named move; see
the correction recorded on Lemma 10. -/
def DegenerateStep (C C₁ : Config n) : Prop :=
  ∃ (x y w : Fin n) (rest : Config n), x ≠ y ∧ x ≠ w ∧
    C = s(x, y) ::ₘ s(x, w) ::ₘ rest ∧ C₁ = s(x, x) ::ₘ s(y, w) ::ₘ rest

/-- `C → C′`: a finite sequence of moves leads from `C` to `C′` (p.8, with the degenerate move). -/
def Reaches (C C' : Config n) : Prop :=
  Relation.ReflTransGen (fun A B => UncrossStep A B ∨ DegenerateStep A B) C C'

end Config

end RepellingPairs


