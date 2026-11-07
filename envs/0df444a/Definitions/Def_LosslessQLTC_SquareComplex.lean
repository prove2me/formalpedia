-- Prove2me | Definitions.Def_LosslessQLTC_SquareComplex
-- name    : LosslessQLTC_SquareComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:08:22.409564+00:00
-- url     : https://prove2.me/theorems/f6b16e1c-2a14-4788-b880-973412e49644
-- title:
--   $k$-dimensional square complex: a decorated $(k,2)$-cubical complex with biregular direction graphs
-- statement:
--   A **$k$-dimensional square complex** $X$ has a finite vertex set partitioned into $2^k$ nonempty blocks $V_I$, $I\subseteq[k]$. Its edges join $V_I$ to $V_{I\cup\{i\}}$ for $i\notin I$, and are oriented upward, written $x\lessdot y$. For every $I$ and $i\notin I$ the graph between $V_I$ and $V_{I\cup\{i\}}$ is $(D_i,D'_i)$-biregular with $D_i,D'_i>0$, so the degrees depend only on the direction $i$.
--
--   $X$ also has a set $X(2)$ of declared squares $\{a;b,b';c\}$ with $c\lessdot b,b'\lessdot a$ and $\mathrm{type}(b)\ne\mathrm{type}(b')$, subject to **2-joint completion**: every vertex together with two incident edges in distinct directions lies in exactly one declared square. A joint has three shapes: two up-edges, two down-edges, or one edge of each.
--
--   This is the model object of the whole mission. A square complex need not declare every four-cycle, and two opposite vertices may lie on several squares.
--
--   **Formalization Note.** There is one vertex type with a type map, not a family of blocks, and directions $1,\dots,k$ are `Fin k` in the same order. Only the graph and $X(2)$ are stored: a $(k,2)$-cubical complex constrains $X(i)$ only for $i\le2$, and the source never uses $X(i)$ for $i\ge3$.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Definitions 2.3, 2.4, 2.5, 2.7, pp.14–15; standing assumptions pp.14, 17

import Mathlib

namespace LosslessQLTC

/-- A `k`-dimensional square complex, i.e. a decorated `(k, 2)`-cubical complex (Definitions 2.3,
2.4, 2.5, 2.7, pp.14–15), with the standing assumptions of pp.14 and 17, of Cohen, Leigh, Reiner,
Ta-Shma, Tzalik, arXiv:2610.00525 (held version, sha256 d61f0ed9…).

* `Vtx` is the finite vertex set `X(0)` and `type v = I` says `v ∈ V_I`; every block is nonempty.
* `up x y` is `x ⋖ y`: an edge between `V_I` and `V_{I ∪ {i}}`, oriented upward (p.16).
* Every `X_{I,i}` is `(D_i, D′_i)`-biregular with `D_i, D′_i > 0` (p.17).
* `Square a b b' c` is the declared square `{a; b, b′; c} ∈ X(2)`, with `c ⋖ b, b′ ⋖ a`.
* `complete_bottom`, `complete_top`, `complete_middle` are 2-joint completion: a vertex together
  with two incident edges in distinct directions lies in exactly one declared square. The three
  fields are the three possible shapes of such a joint.

**Formalization Note.** Directions `1, …, k` are `Fin k`, in the same order. There is one vertex
type with a `type` map rather than a family of blocks. Only the graph and `X(2)` are stored: a
`(k, 2)`-cubical complex constrains `X(i)` only for `i ≤ 2`, `X(0)` and `X(1)` are forced by
1-joint completion, and no result of the source uses `X(i)` for `i ≥ 3` (which Definition 2.4
allows to be empty). `X(2)` need not contain every four-cycle (Remark 2.8), and a pair of opposite
vertices may lie on several squares (Remark 2.9). -/
structure SquareComplex (k : ℕ) where
  /-- The vertex set `X(0)`. -/
  Vtx : Type
  [fintypeVtx : Fintype Vtx]
  [decEqVtx : DecidableEq Vtx]
  /-- `type v = I` means `v ∈ V_I`. -/
  type : Vtx → Finset (Fin k)
  block_nonempty : ∀ I : Finset (Fin k), ∃ v, type v = I
  /-- `up x y` is `x ⋖ y`. -/
  up : Vtx → Vtx → Prop
  [decUp : DecidableRel up]
  up_type : ∀ {x y}, up x y → ∃ i, i ∉ type x ∧ type y = insert i (type x)
  /-- `D i` is the upward degree `D_i`. -/
  D : Fin k → ℕ
  /-- `D' i` is the downward degree `D′_i`. -/
  D' : Fin k → ℕ
  D_pos : ∀ i, 0 < D i
  D'_pos : ∀ i, 0 < D' i
  deg_up : ∀ x i, i ∉ type x →
    (Finset.univ.filter fun y => up x y ∧ type y = insert i (type x)).card = D i
  deg_down : ∀ y i, i ∈ type y →
    (Finset.univ.filter fun x => up x y ∧ type x = (type y).erase i).card = D' i
  /-- `Square a b b' c` is the declared square `{a; b, b′; c}`. -/
  Square : Vtx → Vtx → Vtx → Vtx → Prop
  square_symm : ∀ {a b b' c}, Square a b b' c → Square a b' b c
  square_up : ∀ {a b b' c}, Square a b b' c → up c b ∧ up c b' ∧ up b a ∧ up b' a
  square_type : ∀ {a b b' c}, Square a b b' c → type b ≠ type b'
  complete_bottom : ∀ {c b b'}, up c b → up c b' → type b ≠ type b' → ∃! a, Square a b b' c
  complete_top : ∀ {a b b'}, up b a → up b' a → type b ≠ type b' → ∃! c, Square a b b' c
  complete_middle : ∀ {a b c}, up c b → up b a → ∃! b', Square a b b' c

attribute [instance] SquareComplex.fintypeVtx SquareComplex.decEqVtx SquareComplex.decUp

end LosslessQLTC


