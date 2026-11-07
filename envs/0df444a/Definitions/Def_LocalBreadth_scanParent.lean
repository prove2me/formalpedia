-- Prove2me | Definitions.Def_LocalBreadth_scanParent
-- name    : LocalBreadth_scanParent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:53:24.545811+00:00
-- url     : https://prove2.me/theorems/6ef8b627-c124-4d98-b275-e3bbf2b4311f
-- title:
--   Forest operations: the parent scan, compressed chains and lowest common ancestors
-- statement:
--   For a forest whose vertices are natural numbers with labels $L_v$, an earlier vertex $u<v$ is a **possible parent** of $v$ if $L_v\subseteq L_u$ and $P_u\subseteq L_v$. The **parent scan** runs through the earlier vertices in increasing order, retains the first possible parent, and replaces the retained $p$ by a possible parent $u$ whenever $L_u\subseteq L_p$. The final retained vertex is the parent; with no possible parent, $v$ is a root.
--
--   $a\preceq v$ means that $a$ is an ancestor of $v$, allowing equality. $\overline H[a,v]$ reads the labels along the forest path from $a$ to $v$ and deletes consecutive repetitions. The lowest common ancestor of two vertices is the common ancestor farthest from the root.
--
--   **Formalization Note** Parent indices strictly decrease, so `rootPath` follows parents for at most $v$ steps, and the lowest common ancestor is the common ancestor of largest index.
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc…), §5.4, p.33; §§5.8.2–5.8.3, p.38

import Mathlib

namespace LocalBreadth

open scoped Classical

/-- Helper for `rootPath`: follow parents for at most the given number of steps. -/
def rootPathAux (parent : ℕ → Option ℕ) : ℕ → ℕ → List ℕ
  | 0, v => [v]
  | k + 1, v =>
    match parent v with
    | some p => rootPathAux parent k p ++ [v]
    | none => [v]

/-- The path from the component root to `v`, root first.

**Formalization Note.** Parent indices strictly decrease in the forest (`scanParent`), so `v` steps
always suffice. -/
def rootPath (parent : ℕ → Option ℕ) (v : ℕ) : List ℕ := rootPathAux parent v v

/-- `a ⪯ v`: `a` is an ancestor of `v`, allowing equality (p.31). -/
def IsAnc (parent : ℕ → Option ℕ) (a v : ℕ) : Prop := a ∈ rootPath parent v

/-- The vertices on the forest path from `a` to `v`, `a` first. -/
def pathFrom (parent : ℕ → Option ℕ) (a v : ℕ) : List ℕ :=
  (rootPath parent v).dropWhile (· ≠ a)

/-- Delete consecutive repetitions (§5.8.2, p.38). -/
noncomputable def compress : List (Set ℤ) → List (Set ℤ)
  | [] => []
  | [L] => [L]
  | L :: M :: t => if L = M then compress (M :: t) else L :: compress (M :: t)

/-- `H[a, v]` (§5.8.2, p.38): read the language labels along the forest path from `a` to `v`, and
delete consecutive repetitions of the same label. Kleinberg, Wei, STOC 2027 submission (manuscript
sha256 f924cbfc…). -/
noncomputable def chainFrom (L : ℕ → Set ℤ) (parent : ℕ → Option ℕ) (a v : ℕ) : List (Set ℤ) :=
  compress ((pathFrom parent a v).map L)

/-- The **parent scan** (§5.4, p.33, with §5.8.3, p.38). An earlier vertex `u` is a possible parent of
`v` if `L v ⊆ L u` and `P u ⊆ L v`. Scan in increasing index order: retain the first possible parent,
and replace the retained `p` by `u` whenever `L u ⊆ L p`. `none` means `v` is a root. -/
noncomputable def scanParent (L : ℕ → Set ℤ) (P : ℕ → Finset ℤ) (v : ℕ) : Option ℕ :=
  (List.range v).foldl
    (fun r u =>
      if L v ⊆ L u ∧ (P u : Set ℤ) ⊆ L v then
        match r with
        | none => some u
        | some p => if L u ⊆ L p then some u else some p
      else r)
    none

/-- The lowest common ancestor.

**Formalization Note.** Common ancestors of two vertices lie on one path and indices increase along
it, so the lowest is the one of largest index. The algorithm applies this only to vertices with a
common ancestor. -/
noncomputable def lca (parent : ℕ → Option ℕ) (u w : ℕ) : ℕ :=
  sSup {a | IsAnc parent a u ∧ IsAnc parent a w}

end LocalBreadth


