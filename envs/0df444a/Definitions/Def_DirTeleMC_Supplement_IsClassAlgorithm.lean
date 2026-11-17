-- Prove2me | Definitions.Def_DirTeleMC_Supplement_IsClassAlgorithm
-- name    : DirTeleMC_Supplement_IsClassAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:39:54.752187+00:00
-- url     : https://prove2.me/theorems/a8eab2fa-be19-4136-add9-5bdf0e4986c4
-- title:
--   Separator algorithms of a root-path separable class; the planar class
-- statement:
--   A **separator algorithm** for a class $\mathcal G$ and an integer $p$ is a deterministic polynomial-time algorithm that, for every connected graph $H\in\mathcal G$, vertex $r$ of $H$, spanning tree $A$ of $H$ rooted at $r$ and nonnegative rational vertex weights $\mu$, returns a nonempty set $Z$ of at most $p$ vertices such that every component of $H-A[r,Z]$ has weight at most $\mu(V(H))/2$. Together with minor-closure and the $p$-root-path separability of every connected graph of $\mathcal G$, the existence of such an algorithm makes $\mathcal G$ a **$p$-root-path separable class**.
--
--   The **planar class** consists of the graphs that have a crossing-free drawing in the plane; a digraph is planar if its underlying graph is.
--
--   The separator algorithm is the parameter with which LPSEP is run in Theorems 5.2 and 1.3.
--
--   **Formalization Note** Polynomial time is Mathlib's `Turing.TM2ComputableInTime` with time at most $(m+2)^c$ on inputs of length $m$, over the published alphabet `Fin 4`: inputs are $N$, the adjacency matrices of $H$ and $A$, $r$, and the weights (published `encRat`); the output is a list of vertex numbers. Planarity is the published `WilliamsonShmoys.HasPlanarDrawingOn`.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Definition 5.1, p.14 (PDF p.15), restated p.37 (PDF p.38); App. C, "Graph classes", p.36 (PDF p.37)

import Mathlib
import Definitions.Def_DirTeleMC_Supplement_IsRootPathSeparable
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_bit
import Definitions.Def_OnlineCRS_Combine_encNat
import Definitions.Def_OnlineCRS_Combine_encRat
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

namespace DirTeleMC.Supplement

open OnlineCRS.Combine

/-- The input of a separator (class) algorithm of Definition 5.1: a graph `H` on `Fin N`, a vertex `r`, a graph `A`
(meant to be a spanning tree of `H`, rooted at `r`), and rational vertex weights `μ`. -/
structure SepInput where
  N : ℕ
  H : SimpleGraph (Fin N)
  r : Fin N
  A : SimpleGraph (Fin N)
  μ : Fin N → ℚ

/-- Encoding of a separator input: `N` in binary, the `N²` adjacency bits of `H` row by row, `r` in binary, the `N²`
adjacency bits of `A`, and the `N` weights (published `encRat`), each field followed by the separator `3`. -/
noncomputable def encSepInput (X : SepInput) : List Sym := by
  classical
  exact encNat X.N ++ [3] ++
    ((List.finRange X.N).flatMap fun i => (List.finRange X.N).map fun j => bit (decide (X.H.Adj i j))) ++ [3] ++
    encNat X.r.val ++ [3] ++
    ((List.finRange X.N).flatMap fun i => (List.finRange X.N).map fun j => bit (decide (X.A.Adj i j))) ++ [3] ++
    ((List.finRange X.N).flatMap fun i => encRat (X.μ i) ++ [3])

/-- Encoding of a list of natural numbers: its length, then its entries, in binary, each followed by `3`. -/
def encNatList (l : List ℕ) : List Sym :=
  encNat l.length ++ [3] ++ l.flatMap fun a => encNat a ++ [3]

/-- **A separator algorithm for a class** (Definition 5.1, p.14, restated p.37).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…): "there is a deterministic polynomial-time algorithm that computes such a set Z for
every connected graph H ∈ G, vertex r of H, spanning tree A of H rooted at r and rational vertex weights µ".

`IsClassAlgorithm p C Z`: the function `Z` (returning the numbers of the chosen vertices) is computed by a Turing
machine in time at most `(m + 2)^c` on inputs of length `m`, for some `c`, and on every input in which `H` is a
connected graph of the class `C`, `A` a spanning tree of `H` and the weights are nonnegative, the set `Z` of the
returned vertices is nonempty, has at most `p` vertices, and every component of `H − A[r, Z]` has weight at most
`μ(V(H))/2`.

**Formalization Note.** Machine model: Mathlib's `Turing.TM2ComputableInTime` over the published alphabet `Fin 4`,
inputs encoded by `encSepInput`, outputs by `encNatList` (the source names none). Returned numbers that are not
vertices are ignored. -/
def IsClassAlgorithm (p : ℕ) (C : GraphClass) (Z : SepInput → List ℕ) : Prop :=
  (∃ c : ℕ, ∃ M : Turing.TM2ComputableInTime encSepInput encNatList Z, ∀ m, M.time m ≤ (m + 2) ^ c) ∧
  ∀ X : SepInput, C X.N X.H → X.H.Connected → X.A ≤ X.H → X.A.IsTree → (∀ v, 0 ≤ X.μ v) →
    let Zs : Finset (Fin X.N) := Finset.univ.filter fun v => v.val ∈ Z X
    Zs.Nonempty ∧ Zs.card ≤ p ∧ IsBalanced X.H (rootPaths X.A X.r Zs) fun v => (X.μ v : ℝ)

/-- **The planar graphs** (§1.1, p.3; App. C, p.36: "A digraph is planar if its underlying graph is planar"): the
graphs on `Fin N` with a crossing-free drawing in the plane (the published `WilliamsonShmoys.HasPlanarDrawingOn`). -/
def PlanarClass : GraphClass := fun _ H => WilliamsonShmoys.HasPlanarDrawingOn H

end DirTeleMC.Supplement


