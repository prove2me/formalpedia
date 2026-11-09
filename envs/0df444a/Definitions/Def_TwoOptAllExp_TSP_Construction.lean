-- Prove2me | Definitions.Def_TwoOptAllExp_TSP_Construction
-- name    : TwoOptAllExp_TSP_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:05:48.100212+00:00
-- url     : https://prove2.me/theorems/ace076a4-f000-48fa-a40d-4fdf6849d401
-- title:
--   The graph $G_n$, its completion $G_n'$ and the initial tour $\tau_0$
-- statement:
--   Fix $n\ge1$ and put $a=2^{n+2}+3$. The graph $G_n$ has layers $F_0,\dots,F_n$. A **$T$-interface** is the zero-weight path $(T,T'',T')$.
--
--   The layer $F_0$ has an $A_0$- and a $B_0$-interface and vertices $C_0,C_0'',C_0'$; the vertices $C_0$ and $C_0'$ are joined to $C_0'',A_0,A_0',B_0,B_0'$, and $A_0C_0'$, $A_0'C_0$, $C_0B_0$, $C_0'B_0'$ have weights $a,4,3,a-1$, the others weight zero.
--
--   For $i\in[n-1]$ the layer $F_i$ has an upper gadget, made of the $X_i$- and $A_i$-interfaces and the vertices $C_i',D_i$, and a lower gadget, made of the $Y_i$- and $B_i$-interfaces and the vertices $C_i,D_i',E_i$, joined by the zero-weight paths $(C_i',C_i'',C_i)$ and $(D_i',D_i'',D_i)$. With $b=a2^i$ and $c=2^{n+1-i}$ the nonzero weights are
--   $$AD=XA'=XD=2b-3,\quad XA=XC'=1,\quad X'A=X'C'=b-1,\quad X'A'=X'D=b,$$
--   $$BY=3,\quad B'E=c-1,\quad B'Y'=1,\quad CE=1,\quad CY'=2,\quad D'Y=4,\quad EY=c,$$
--   and $AC',A'D,C'D,D'E,CY,EY',BE,D'Y',B'D',B'C,B'Y$ have weight zero.
--
--   The layer $F_n$ has an $X_n$- and a $Y_n$-interface and a vertex $C_n$; $C_nX_n$ has weight $a2^n$, and $C_nX_n',C_nY_n,C_nY_n'$ have weight zero.
--
--   Consecutive layers are glued by $A_i\equiv X_{i+1}'$, $A_i''\equiv X_{i+1}''$, $A_i'\equiv X_{i+1}$ and $B_i\equiv Y_{i+1}'$, $B_i''\equiv Y_{i+1}''$, $B_i'\equiv Y_{i+1}$. The graph has $13n-3$ vertices. The complete graph $G_n'$ gives every missing edge the weight $2M+1$, where $M$ is the largest edge weight of $G_n$.
--
--   The **initial tour** $\tau_0$ is the union of the edges of the paths $(A_0'\to A_0,C_0\to C_0',B_0\to B_0')$ in $F_0$, of $(A_i'\to A_i,X_i\to X_i')$ and $(Y_i'\to Y_i,C_i\to C_i',D_i\to D_i',E_i,B_i\to B_i')$ in $F_i$ for $i\in[n-1]$, and of $(Y_n'\to Y_n,C_n,X_n\to X_n')$ in $F_n$, where $T\to T'$ stands for the path $(T,T'',T')$.
--
--   This is the instance on which the paper's lower bound is proved. All objects are concrete and computable.
--
--   **Formalization Note** The vertices are named points (symbol, layer index), and `Vtx n` is the finite set of those that exist; $X_i$, $Y_i$ and their primes are abbreviations of the identified $A_{i-1}$, $B_{i-1}$ vertices, used only with $i\ge1$. All natural-number subtractions in the weights have a subtrahend at most the minuend, since $a\ge19$ and $n+1-i\ge2$ for $i\le n-1$. A single function `weight` gives the weights of $G_n'$, and these agree with those of $G_n$ on the edges of $G_n$.
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, §4.1, Figure 3 and Table 4, pp. 13–14

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_KOpt

namespace TwoOptAllExp.TSP

/-- The symbols of the vertices of the construction (§4.1, p. 14). `A`, `A2`, `A1` stand for
`A`, `A''`, `A'`, and likewise for the other letters. -/
inductive Kind
  | A | A2 | A1 | B | B2 | B1 | C | C2 | C1 | D | D2 | D1 | E
  deriving DecidableEq, Repr

/-- All symbols. -/
def allKinds : Finset Kind :=
  {Kind.A, Kind.A2, Kind.A1, Kind.B, Kind.B2, Kind.B1, Kind.C, Kind.C2, Kind.C1, Kind.D, Kind.D2,
   Kind.D1, Kind.E}

/-- A named point: a symbol with its layer index. -/
abbrev Pt : Type := Kind × ℕ

namespace Pt

/-- `A_i`. -/ abbrev A (i : ℕ) : Pt := (Kind.A, i)
/-- `A''_i`. -/ abbrev A'' (i : ℕ) : Pt := (Kind.A2, i)
/-- `A'_i`. -/ abbrev A' (i : ℕ) : Pt := (Kind.A1, i)
/-- `B_i`. -/ abbrev B (i : ℕ) : Pt := (Kind.B, i)
/-- `B''_i`. -/ abbrev B'' (i : ℕ) : Pt := (Kind.B2, i)
/-- `B'_i`. -/ abbrev B' (i : ℕ) : Pt := (Kind.B1, i)
/-- `C_i`. -/ abbrev C (i : ℕ) : Pt := (Kind.C, i)
/-- `C''_i`. -/ abbrev C'' (i : ℕ) : Pt := (Kind.C2, i)
/-- `C'_i`. -/ abbrev C' (i : ℕ) : Pt := (Kind.C1, i)
/-- `D_i`. -/ abbrev D (i : ℕ) : Pt := (Kind.D, i)
/-- `D''_i`. -/ abbrev D'' (i : ℕ) : Pt := (Kind.D2, i)
/-- `D'_i`. -/ abbrev D' (i : ℕ) : Pt := (Kind.D1, i)
/-- `E_i`. -/ abbrev E (i : ℕ) : Pt := (Kind.E, i)
/-- Interface identification (p. 14): `X_i ≡ A'_{i-1}`, for `i ≥ 1`. -/
abbrev X (i : ℕ) : Pt := A' (i - 1)
/-- `X''_i ≡ A''_{i-1}`, for `i ≥ 1`. -/
abbrev X'' (i : ℕ) : Pt := A'' (i - 1)
/-- `X'_i ≡ A_{i-1}`, for `i ≥ 1`. -/
abbrev X' (i : ℕ) : Pt := A (i - 1)
/-- `Y_i ≡ B'_{i-1}`, for `i ≥ 1`. -/
abbrev Y (i : ℕ) : Pt := B' (i - 1)
/-- `Y''_i ≡ B''_{i-1}`, for `i ≥ 1`. -/
abbrev Y'' (i : ℕ) : Pt := B'' (i - 1)
/-- `Y'_i ≡ B_{i-1}`, for `i ≥ 1`. -/
abbrev Y' (i : ℕ) : Pt := B (i - 1)

end Pt

open Pt

/-- Which named points are vertices of `G_n`, after the interface identification: the interfaces
`A_i`, `B_i` and the vertices `C_i`, `C''_i`, `C'_i` for `0 ≤ i < n`; the vertices `D_i`, `D''_i`,
`D'_i`, `E_i` for `1 ≤ i < n`; and the vertex `C_n`. -/
def IsVertex (n : ℕ) : Pt → Bool
  | (Kind.A, i) | (Kind.A2, i) | (Kind.A1, i) | (Kind.B, i) | (Kind.B2, i) | (Kind.B1, i)
  | (Kind.C2, i) | (Kind.C1, i) => decide (i < n)
  | (Kind.C, i) => decide (i ≤ n)
  | (Kind.D, i) | (Kind.D2, i) | (Kind.D1, i) | (Kind.E, i) => decide (1 ≤ i ∧ i < n)

/-- The vertex set of `G_n` as a set of named points. For `n ≥ 1` it has `13n - 3` elements. -/
def vertices (n : ℕ) : Finset Pt :=
  (allKinds ×ˢ Finset.range (n + 1)).filter (fun p => IsVertex n p = true)

/-- The vertex type of `G_n`. -/
abbrev Vtx (n : ℕ) : Type := {p : Pt // p ∈ vertices n}

/-- A weighted edge `(u, v, w)`. -/
abbrev WEdge : Type := Pt × Pt × ℕ

/-- The constant `a = 2^(n+2) + 3` (p. 14). -/
def aConst (n : ℕ) : ℕ := 2 ^ (n + 2) + 3

/-- The two zero-weight edges of the `T`-interface, the path `(T, T'', T')` (pp. 13–14). -/
def pathTwo (t t'' t' : Pt) : List WEdge := [(t, t'', 0), (t'', t', 0)]

/-- The edges of the `A_i`- and `B_i`-interfaces. -/
def interfaceEdges (i : ℕ) : List WEdge :=
  pathTwo (A i) (A'' i) (A' i) ++ pathTwo (B i) (B'' i) (B' i)

/-- The edges of `F_0` other than the `A_0`- and `B_0`-interfaces (p. 14): `C_0` and `C'_0` are
joined to `C''_0, A_0, A'_0, B_0, B'_0`, and `A_0 C'_0`, `A'_0 C_0`, `C_0 B_0`, `C'_0 B'_0` have
weights `a`, `4`, `3`, `a - 1`, while the other edges have weight zero. -/
def edgesF0 (n : ℕ) : List WEdge :=
  [(C 0, C'' 0, 0), (C 0, A 0, 0), (C 0, A' 0, 4), (C 0, B 0, 3), (C 0, B' 0, 0),
   (C' 0, C'' 0, 0), (C' 0, A 0, aConst n), (C' 0, A' 0, 0), (C' 0, B 0, 0),
   (C' 0, B' 0, aConst n - 1)]

/-- The edges of the upper gadget of `F_i` other than its interfaces (Table 4 top and the
zero-weight list, p. 14), with `b = a 2^i`. -/
def edgesUpper (n i : ℕ) : List WEdge :=
  let b := aConst n * 2 ^ i
  [(A i, D i, 2 * b - 3), (X i, A i, 1), (X i, A' i, 2 * b - 3), (X i, C' i, 1),
   (X i, D i, 2 * b - 3), (X' i, A i, b - 1), (X' i, A' i, b), (X' i, C' i, b - 1),
   (X' i, D i, b),
   (A i, C' i, 0), (A' i, D i, 0), (C' i, D i, 0)]

/-- The edges of the lower gadget of `F_i` other than its interfaces (Table 4 bottom and the
zero-weight list, p. 14), with `c = 2^(j_i)`, `j_i = n + 1 - i`. -/
def edgesLower (n i : ℕ) : List WEdge :=
  let c := 2 ^ (n + 1 - i)
  [(B i, Y i, 3), (B' i, E i, c - 1), (B' i, Y' i, 1), (C i, E i, 1), (C i, Y' i, 2),
   (D' i, Y i, 4), (E i, Y i, c),
   (D' i, E i, 0), (C i, Y i, 0), (E i, Y' i, 0), (B i, E i, 0), (D' i, Y' i, 0),
   (B' i, D' i, 0), (B' i, C i, 0), (B' i, Y i, 0)]

/-- The edges of `F_i`, `i ∈ [n-1]`, other than those of the `X_i`- and `Y_i`-interfaces: the
`A_i`- and `B_i`-interfaces, the paths `(C'_i, C''_i, C_i)` and `(D'_i, D''_i, D_i)`, and the two
gadgets. -/
def edgesInterior (n i : ℕ) : List WEdge :=
  interfaceEdges i ++ pathTwo (C' i) (C'' i) (C i) ++ pathTwo (D' i) (D'' i) (D i) ++
    edgesUpper n i ++ edgesLower n i

/-- The edges of `F_n` other than those of the `X_n`- and `Y_n`-interfaces (p. 14): `C_n X_n` has
weight `a 2^n`, and `C_n X'_n`, `C_n Y_n`, `C_n Y'_n` have weight zero. -/
def edgesFn (n : ℕ) : List WEdge :=
  [(C n, X n, aConst n * 2 ^ n), (C n, X' n, 0), (C n, Y n, 0), (C n, Y' n, 0)]

/-- All weighted edges of `G_n`. Every edge of `G_n` is listed once. -/
def edgeList (n : ℕ) : List WEdge :=
  interfaceEdges 0 ++ edgesF0 n ++ (List.range' 1 (n - 1)).flatMap (edgesInterior n) ++ edgesFn n

/-- The weight of the pair `e` in `G_n`, or `none` if `e` is not an edge of `G_n`. -/
def edgeWeight? (n : ℕ) (e : Sym2 Pt) : Option ℕ :=
  ((edgeList n).find? (fun t => decide (s(t.1, t.2.1) = e))).map (fun t => t.2.2)

/-- The graph `G_n` of §4.1. -/
def G (n : ℕ) : SimpleGraph (Vtx n) :=
  SimpleGraph.fromEdgeSet {e | (edgeWeight? n (e.map Subtype.val)).isSome = true}

instance (n : ℕ) : DecidableRel (G n).Adj := fun u v =>
  decidable_of_iff ((edgeWeight? n (s(u, v).map Subtype.val)).isSome = true ∧ u ≠ v)
    (by simp [G])

/-- `M`, the largest edge weight of `G_n` (p. 14). -/
def maxWeight (n : ℕ) : ℕ := ((edgeList n).map (fun t => t.2.2)).foldr max 0

/-- The edge weights of the complete graph `G'_n` (p. 14): an edge of `G_n` keeps its weight and
every missing edge has weight `2M + 1`. On the edges of `G_n` this is the weight of `G_n`. -/
def weight (n : ℕ) (e : Sym2 (Vtx n)) : ℕ :=
  (edgeWeight? n (e.map Subtype.val)).getD (2 * maxWeight n + 1)

/-- The search space of tours of `G_n` with 2-swaps. -/
abbrev space (n : ℕ) : SearchSpace := tspSpace 2 (G n) (weight n)

/-- The search space of TSP with the 2-opt neighborhood on the complete graph `G'_n`. -/
abbrev completedSpace (n : ℕ) : SearchSpace := tspSpace 2 (⊤ : SimpleGraph (Vtx n)) (weight n)

/-- The edges of `G_n`-pairs among the given named pairs, as edges on the vertex type: those pairs
of `S` both of whose endpoints are vertices of `G_n`. -/
def lift (n : ℕ) (S : Finset (Sym2 Pt)) : Finset (Sym2 (Vtx n)) :=
  Finset.univ.filter (fun e => e.map Subtype.val ∈ S)

/-- An edge set on the vertex type, as a set of named pairs. -/
def raw {n : ℕ} (H : Finset (Sym2 (Vtx n))) : Finset (Sym2 Pt) :=
  H.image (Sym2.map Subtype.val)

/-- The edges of a path given by its list of vertices. -/
def pathEdges : List Pt → List (Sym2 Pt)
  | u :: v :: l => s(u, v) :: pathEdges (v :: l)
  | _ => []

/-- The path in `F_0` of the initial tour: `(A'_0 → A_0, C_0 → C'_0, B_0 → B'_0)` (p. 14). -/
def tourPathF0 : List Pt :=
  [A' 0, A'' 0, A 0, C 0, C'' 0, C' 0, B 0, B'' 0, B' 0]

/-- The upper path in `F_i` of the initial tour: `(A'_i → A_i, X_i → X'_i)` (p. 14). -/
def tourPathUpper (i : ℕ) : List Pt :=
  [A' i, A'' i, A i, X i, X'' i, X' i]

/-- The lower path in `F_i` of the initial tour:
`(Y'_i → Y_i, C_i → C'_i, D_i → D'_i, E_i, B_i → B'_i)` (p. 14). -/
def tourPathLower (i : ℕ) : List Pt :=
  [Y' i, Y'' i, Y i, C i, C'' i, C' i, D i, D'' i, D' i, E i, B i, B'' i, B' i]

/-- The path in `F_n` of the initial tour: `(Y'_n → Y_n, C_n, X_n → X'_n)` (p. 14). -/
def tourPathFn (n : ℕ) : List Pt :=
  [Y' n, Y'' n, Y n, C n, X n, X'' n, X' n]

/-- The initial tour `τ₀`: the union of the edges of the paths above (p. 14). -/
def tau0 (n : ℕ) : Finset (Sym2 (Vtx n)) :=
  lift n (pathEdges tourPathF0 ++
      (List.range' 1 (n - 1)).flatMap
        (fun i => pathEdges (tourPathUpper i) ++ pathEdges (tourPathLower i)) ++
      pathEdges (tourPathFn n)).toFinset

end TwoOptAllExp.TSP


