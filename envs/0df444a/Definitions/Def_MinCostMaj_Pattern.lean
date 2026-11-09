-- Prove2me | Definitions.Def_MinCostMaj_Pattern
-- name    : MinCostMaj_Pattern
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:09:21.666683+00:00
-- url     : https://prove2.me/theorems/c7e82343-39ca-4da9-b81a-89675e136d31
-- title:
--   Patterns, connection, cycle consistency and ac-leq-cycle pairs
-- statement:
--   A **pattern** $p$ from $u$ to $v$ in an instance is a sequence of relations $R_1,\dots,R_n$ and variables $u=w_0,w_1,\dots,w_n=v$ with $R_i\in\mathcal R_{w_{i-1}w_i}$. It **connects** $a$ to $b$ if there are values $a=a_0,a_1,\dots,a_n=b$ with $(a_{i-1},a_i)\in R_i$ for all $i$. For patterns $p$ from $u$ to $v$ and $q$ from $v$ to $w$, $p+q$ is their concatenation, and $rp$ is the concatenation of $r$ copies of $p$. For $B\subseteq A^I_x$ and a pattern $p$ from $x$ to $y$, $B+p$ is the set of $b\in A^I_y$ connected by $p$ to some element of $B$.
--
--   - An arc-consistent instance is **cycle consistent** if every pattern from a variable $u$ to itself connects every $a\in A^I_u$ to itself.
--   - $(I,J)$ is an **ac-leq-cycle pair** if $I$ is arc-consistent, $J$ is cycle consistent and $I\le J$ (Definition 3.1).
--   - $I$ has **connected input** if every two variables are joined by a pattern.
--
--   **Formalization Note** A pattern is its start variable together with the list of its steps $(R_i,w_i)$; the empty list is the empty pattern. Concatenation is list append. A pattern of $J$ is read in a subinstance $I\le J$ by restricting the values after the start to the potatoes of $I$ (`ConnectsIn`), since the constraints of $I$ are those of $J$ restricted to the potatoes of $I$; a variant restricts the value at each position to a prescribed set (`ConnectsPos`).
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), §3, p.6, Definition 3.1; Appendix A, p.12 (PDF pp.7, 13)

import Mathlib
import Definitions.Def_MinCostMaj_BinInst

namespace MinCostMaj

/-- **Pattern** from `u` to `v` (§3, p.6): "A pattern p from u to v (in instance I) is a sequence of
relations R1, . . . , Rn and variables u = w0, w1, . . . , wn = v such that Ri ∈ R^I_{wi−1wi} for
each i."

`IsPat rels u l v`: the list `l = [(R₁, w₁), …, (Rₙ, wₙ)]` together with the start `u = w₀` is a
pattern from `u` to `v = wₙ` in the constraint family `rels`.

**Formalization Note.** A pattern is its start variable and the list of its steps `(Rᵢ, wᵢ)`; the
empty list (`n = 0`) is the empty pattern from `u` to `u`. Concatenation `p + q` ("removing one
copy of v at the junction") is list append, and `rp` is the concatenation of `r` copies. -/
def IsPat {V D : Type*} (rels : V → V → Set (Set (D × D))) :
    V → List (Set (D × D) × V) → V → Prop
  | u, [], v => u = v
  | u, (R, w) :: l, v => R ∈ rels u w ∧ IsPat rels w l v

/-- **The pattern connects `a` to `b`** (§3, p.6): "there exist values a = a0, a1, . . . , an = b
such that (ai−1, ai) ∈ Ri for all i." -/
def Connects {V D : Type*} : D → List (Set (D × D) × V) → D → Prop
  | a, [], b => a = b
  | a, (R, _) :: l, b => ∃ c, (a, c) ∈ R ∧ Connects c l b

/-- Connection with every value after the start restricted to the sets `S wᵢ` (used to read a
pattern of `J` inside a subinstance `I ≤ J`, with `S = A^I`: the constraints of `I` are those of `J`
restricted to the potatoes of `I`). -/
def ConnectsIn {V D : Type*} (S : V → Set D) : D → List (Set (D × D) × V) → D → Prop
  | a, [], b => a = b
  | a, (R, w) :: l, b => ∃ c ∈ S w, (a, c) ∈ R ∧ ConnectsIn S c l b

/-- Connection with the value at position `i` of the pattern (`i = 0` the start) restricted to
`S i` (Theorem 4.1 Item 3: "after restricting intermediate potatoes to suitable two-element
subsets"). `ConnectsPos S i a l b` reads `l` starting at position `i`. -/
def ConnectsPos {V D : Type*} (S : ℕ → Set D) : ℕ → D → List (Set (D × D) × V) → D → Prop
  | _, a, [], b => a = b
  | i, a, (R, _) :: l, b => ∃ c ∈ S (i + 1), (a, c) ∈ R ∧ ConnectsPos S (i + 1) c l b

/-- The concatenation `r p` of `r` copies of a closed pattern `p` (§3, p.6). -/
def repPat {V D : Type*} (r : ℕ) (l : List (Set (D × D) × V)) : List (Set (D × D) × V) :=
  (List.replicate r l).flatten

/-- `B + p = {b ∈ A^I_y : some a ∈ B is connected to b by p}` (Appendix A, p.12). -/
def plusPat {V D : Type*} (I : BinInst V D) (y : V) (B : Set D) (l : List (Set (D × D) × V)) :
    Set D :=
  {b | b ∈ I.pot y ∧ ∃ a ∈ B, Connects a l b}

/-- The relation defined by a pattern from `x` to `y` on `A^I_x × A^I_y`,
`Conn(p) = {(a, b) : a is connected to b by p}` (Appendix A, p.12), restricted to the potatoes. -/
def patRel {V D : Type*} (I : BinInst V D) (x y : V) (l : List (Set (D × D) × V)) : Set (D × D) :=
  {ab | ab.1 ∈ I.pot x ∧ ab.2 ∈ I.pot y ∧ Connects ab.1 l ab.2}

namespace BinInst

variable {V D : Type*}

/-- **Cycle consistency** (§3, p.6): "An arc-consistent instance is cycle consistent if, for every
variable u, every pattern p from u to itself, and every a ∈ A^I_u, the pattern p connects a to
itself." -/
def IsCycleConsistent (I : BinInst V D) : Prop :=
  I.IsArcConsistent ∧
    ∀ u (l : List (Set (D × D) × V)), IsPat I.rels u l u → ∀ a ∈ I.pot u, Connects a l a

/-- **ac-leq-cycle pair** (Definition 3.1, p.6): "A pair (I, J) is an ac-leq-cycle pair if I is
arc-consistent, J is cycle consistent, and I ≤ J." -/
def AcLeqCycle (I J : BinInst V D) : Prop :=
  I.IsArcConsistent ∧ J.IsCycleConsistent ∧ Le I J

/-- **Connected input** (Appendix A, p.12): "instances where every two variables are connected by a
pattern". -/
def ConnectedInput (I : BinInst V D) : Prop :=
  ∀ u v, ∃ l : List (Set (D × D) × V), IsPat I.rels u l v

end BinInst

end MinCostMaj


