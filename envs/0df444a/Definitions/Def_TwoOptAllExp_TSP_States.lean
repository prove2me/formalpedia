-- Prove2me | Definitions.Def_TwoOptAllExp_TSP_States
-- name    : TwoOptAllExp_TSP_States
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:14:33.776204+00:00
-- url     : https://prove2.me/theorems/2101cf53-6d10-4db9-908b-a7dc61e12d30
-- title:
--   States of a tour, the edge set of an assignment, the validity conditions and Table 5
-- statement:
--   The **states** of a tour $\tau$ of $G_n$ are defined as follows. The state of $A_i$, $0\le i<n$, is $0$ if $A_i$ is adjacent in $\tau$ to a vertex of $F_i$ outside its interface, and $1$ if $A_i'$ is; the state of $B_i$ is defined in the same way. The state of $C_0$ is $0$ if its neighbor other than $C_0''$ lies in $[A_0]=\{A_0,A_0'\}$, and $1$ if it lies in $[B_0]$. For $i\in[n-1]$, the state of $D_i$ is $0$, $1$ or $2$ according as its neighbor other than $D_i''$ is $C_i'$, lies in $[A_i]$ or lies in $[X_i]$, and the state of $E_i$ is $0,1,2,3,4$ according as its neighbors are $\{D_i',[B_i]\}$, $\{C_i,[B_i]\}$, $\{C_i,D_i'\}$, $\{C_i,[Y_i]\}$, $\{D_i',[Y_i]\}$.
--
--   Conversely, an assignment of states determines an edge set. The state of an interface picks the endpoint that the gadget uses: $[A_i]$ is $A_i$ in state $0$ and $A_i'$ in state $1$, while $[X_i]$ is $X_i$ if $A_{i-1}=0$ and $X_i'$ if $A_{i-1}=1$, and the same holds for $[B_i]$ and $[Y_i]$. The edge set consists of the edges at the vertices $A_i'',B_i'',C_i'',D_i''$, of the pairs joining $C_0,C_0'$ to $[A_0],[B_0]$, of the pairing of $\{C_i',D_i,[X_i],[A_i]\}$ of Figure 5, of the edges at $E_i$ together with the remaining pair of $\{C_i,D_i',[Y_i],[B_i]\}$ of Figure 6, and of the edges joining $C_n$ to $[X_n]$ and $[Y_n]$.
--
--   An assignment is **valid** if for every $i\in[n-1]$: the pair $(D_i,E_i)$ is none of $(0,2),(1,0),(1,3),(2,1),(2,4)$; $D_i=2$ implies $A_i=0$; $E_i=2$ implies $(B_{i-1},B_i)\ne(1,0)$; and $E_i\in\{3,4\}$ implies $B_i=1$.
--
--   **Table 5** lists the changes of a single state that the paper proves to be improving, with conditions on the other states. A row $T:r_0\to r_1\to\dots\to r_m$ lists the change from every earlier to every later value.
--
--   These objects translate the search for improving 2-swaps into a finite calculus of states.
--
--   **Formalization Note** An assignment is a function on the state symbols with value $0$ on the symbols that do not exist for this $n$, so that equality of assignments is equality of states. The fall-through branches of `statesOf` (the value $1$ of an interface state, the value $2$ of $D_i$, the value $4$ of $E_i$) are correct on tours of $G_n$, the only arguments on which they are used. `ValidStates` is the list of conditions of Lemma 11 and does not refer to tours, so Lemma 11 is not circular.
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, Definition 10 and Figs. 5–6, pp. 16–17; conditions of Lemma 11, p. 17; Table 5, p. 19

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_LayerPath

namespace TwoOptAllExp.TSP

open Pt

/-- The state symbols of §4.3 (p. 16): `A_i`, `B_i` for `0 ≤ i < n`, `C_0`, and `D_i`, `E_i` for
`i ∈ [n-1]`. -/
inductive Var
  | A (i : ℕ) | B (i : ℕ) | C0 | D (i : ℕ) | E (i : ℕ)
  deriving DecidableEq, Repr

/-- The state symbols that exist for a given `n`. -/
def Var.Exists (n : ℕ) : Var → Prop
  | .A i | .B i => i < n
  | .C0 => True
  | .D i | .E i => 1 ≤ i ∧ i < n

/-- The number of values of a state: `A_i, B_i, C_0 ∈ {0, 1}`, `D_i ∈ {0, 1, 2}`,
`E_i ∈ {0, …, 4}`. -/
def Var.numValues : Var → ℕ
  | .A _ | .B _ | .C0 => 2
  | .D _ => 3
  | .E _ => 5

/-- An assignment of states. Symbols that do not exist for this `n` carry the value `0`, so that
equality of assignments is equality on the symbols that exist. -/
def IsAssignment (n : ℕ) (s : Var → ℕ) : Prop :=
  ∀ v, (v.Exists n → s v < v.numValues) ∧ (¬ v.Exists n → s v = 0)

/-- The state of `A_i` or `B_i` (Definition 10, p. 16): `0` if the vertex `T_i` is adjacent in the
edge set `R` to a vertex of `F_i` outside the interface `I` of `T_i`, and `1` otherwise, in which
case on a tour `T'_i` has such a neighbor. -/
def interfaceState (n i : ℕ) (R : Finset (Sym2 Pt)) (I : Finset Pt) (t : Pt) : ℕ :=
  if ∃ w ∈ layerVerts n i \ I, s(t, w) ∈ R then 0 else 1

/-- The states associated with a tour (**Definition 10**, pp. 16–17). -/
def statesOf (n : ℕ) (H : Finset (Sym2 (Vtx n))) : Var → ℕ
  | .A i => if i < n then interfaceState n i (raw H) (ifaceA i) (A i) else 0
  | .B i => if i < n then interfaceState n i (raw H) (ifaceB i) (B i) else 0
  | .C0 => if s(C 0, A 0) ∈ raw H ∨ s(C 0, A' 0) ∈ raw H then 0 else 1
  | .D i =>
    if 1 ≤ i ∧ i < n then
      if s(D i, C' i) ∈ raw H then 0
      else if s(D i, A i) ∈ raw H ∨ s(D i, A' i) ∈ raw H then 1
      else 2
    else 0
  | .E i =>
    if 1 ≤ i ∧ i < n then
      let toC := s(E i, C i) ∈ raw H
      let toD := s(E i, D' i) ∈ raw H
      let toB := s(E i, B i) ∈ raw H ∨ s(E i, B' i) ∈ raw H
      if toD ∧ toB then 0
      else if toC ∧ toB then 1
      else if toC ∧ toD then 2
      else if toC then 3
      else 4
    else 0

/-- The endpoint of the `A_i`-interface used by `F_i`: `A_i` in state `0` and `A'_i` in state `1`. -/
def endA (s : Var → ℕ) (i : ℕ) : Pt := if s (.A i) = 0 then A i else A' i

/-- The endpoint of the `B_i`-interface used by `F_i`. -/
def endB (s : Var → ℕ) (i : ℕ) : Pt := if s (.B i) = 0 then B i else B' i

/-- The endpoint of the `X_i`-interface used by `F_i`: the end of the interface that `F_{i-1}`
does not use, `X_i ≡ A'_{i-1}` in state `A_{i-1} = 0` and `X'_i ≡ A_{i-1}` in state `A_{i-1} = 1`. -/
def endX (s : Var → ℕ) (i : ℕ) : Pt := if s (.A (i - 1)) = 0 then X i else X' i

/-- The endpoint of the `Y_i`-interface used by `F_i`. -/
def endY (s : Var → ℕ) (i : ℕ) : Pt := if s (.B (i - 1)) = 0 then Y i else Y' i

/-- The edges of `F_0` selected by `C_0` (Definition 10): `C_0` is joined to one interface and
`C'_0` to the other. -/
def pairsF0 (s : Var → ℕ) : List (Sym2 Pt) :=
  if s .C0 = 0 then [s(C 0, endA s 0), s(C' 0, endB s 0)]
  else [s(C 0, endB s 0), s(C' 0, endA s 0)]

/-- The pairing of the upper gadget of `F_i` for each state of `D_i` (Fig. 5, p. 17). -/
def pairsUpper (s : Var → ℕ) (i : ℕ) : List (Sym2 Pt) :=
  match s (.D i) with
  | 0 => [s(D i, C' i), s(endX s i, endA s i)]
  | 1 => [s(D i, endA s i), s(C' i, endX s i)]
  | _ => [s(D i, endX s i), s(C' i, endA s i)]

/-- The pairing of the lower gadget of `F_i` for each state of `E_i` (Definition 10 and Fig. 6,
p. 17). -/
def pairsLower (s : Var → ℕ) (i : ℕ) : List (Sym2 Pt) :=
  match s (.E i) with
  | 0 => [s(E i, D' i), s(E i, endB s i), s(C i, endY s i)]
  | 1 => [s(E i, C i), s(E i, endB s i), s(D' i, endY s i)]
  | 2 => [s(E i, C i), s(E i, D' i), s(endY s i, endB s i)]
  | 3 => [s(E i, C i), s(E i, endY s i), s(D' i, endB s i)]
  | _ => [s(E i, D' i), s(E i, endY s i), s(C i, endB s i)]

/-- The fixed edges of Observation 8, those at the vertices `A''_i`, `B''_i`, `C''_i`
(`0 ≤ i < n`) and `D''_i` (`i ∈ [n-1]`). -/
def fixedEdges (n : ℕ) : List (Sym2 Pt) :=
  (List.range n).flatMap (fun i =>
    [s(A i, A'' i), s(A'' i, A' i), s(B i, B'' i), s(B'' i, B' i),
     s(C i, C'' i), s(C'' i, C' i)]) ++
  (List.range' 1 (n - 1)).flatMap (fun i => [s(D i, D'' i), s(D'' i, D' i)])

/-- The edge set determined by an assignment of states, as named pairs (p. 17): the fixed edges of
Observation 8, the pairings of Figs. 5 and 6 and of `C_0`, and the two edges at `C_n`. -/
def stateEdges (n : ℕ) (s : Var → ℕ) : Finset (Sym2 Pt) :=
  (fixedEdges n ++ pairsF0 s ++
    (List.range' 1 (n - 1)).flatMap (fun i => pairsUpper s i ++ pairsLower s i) ++
    [s(C n, endX s n), s(C n, endY s n)]).toFinset

/-- The edge set determined by an assignment of states, on the vertex type of `G_n`. -/
def tourOf (n : ℕ) (s : Var → ℕ) : Finset (Sym2 (Vtx n)) :=
  lift n (stateEdges n s)

/-- The four conditions of Lemma 11, p. 17. The statement of Lemma 11 is that they characterize
the assignments that determine a tour. -/
def ValidStates (n : ℕ) (s : Var → ℕ) : Prop :=
  ∀ i, 1 ≤ i → i < n →
    ((s (.D i), s (.E i)) ∉ ([(0, 2), (1, 0), (1, 3), (2, 1), (2, 4)] : List (ℕ × ℕ))) ∧
    (s (.D i) = 2 → s (.A i) = 0) ∧
    (s (.E i) = 2 → (s (.B (i - 1)), s (.B i)) ≠ (1, 0)) ∧
    (s (.E i) = 3 ∨ s (.E i) = 4 → s (.B i) = 1)

/-- `r` strictly precedes `r'` in the displayed order `T : r₀ → r₁ → ⋯ → r_m` (p. 19). -/
def Precedes (chain : List ℕ) (r r' : ℕ) : Prop := [r, r'].Sublist chain

/-- **Table 5**, p. 19: `Table5 n s v r r'` says that the change of the state `v` from `r` to `r'`
is listed in Table 5, the other states being those of `s`. -/
def Table5 (n : ℕ) (s : Var → ℕ) : Var → ℕ → ℕ → Prop
  | .A i, r, r' =>
    (i = n - 1 ∧ r = 0 ∧ r' = 1) ∨                                                  -- (a1)
    (i < n - 1 ∧ r = 0 ∧ r' = 1 ∧
      (s (.A (i + 1)), s (.D (i + 1))) ∈ ([(0, 2), (1, 0)] : List (ℕ × ℕ))) ∨       -- (a2)
    (i < n - 1 ∧ r = 1 ∧ r' = 0 ∧
      (s (.A (i + 1)), s (.D (i + 1))) ∈ ([(0, 0), (0, 1), (1, 1)] : List (ℕ × ℕ))) -- (a3)
  | .B i, r, r' =>
    (i = 0 ∧ r = 0 ∧ r' = 1 ∧ s .C0 = 1) ∨                                          -- (b1)
    (i = 0 ∧ r = 1 ∧ r' = 0 ∧ s .C0 = 0) ∨                                          -- (b2)
    (1 ≤ i ∧ r = 0 ∧ r' = 1 ∧ s (.E i) = 2) ∨                                       -- (b3)
    (1 ≤ i ∧ r = 1 ∧ r' = 0 ∧ (s (.E i) = 0 ∨ s (.E i) = 1))                        -- (b4)
  | .C0, r, r' =>
    (r = 0 ∧ r' = 1 ∧ s (.A 0) = 1) ∨                                               -- (c1)
    (r = 1 ∧ r' = 0 ∧ s (.A 0) = 0)                                                 -- (c2)
  | .D i, r, r' =>
    (Precedes [1, 2, 0] r r' ∧ s (.A i) = 0) ∨                                      -- (d1)
    (r = 0 ∧ r' = 1 ∧ s (.A i) = 1)                                                 -- (d2)
  | .E i, r, r' =>
    (Precedes [1, 2, 0] r r' ∧ (s (.B (i - 1)), s (.B i)) = (0, 0)) ∨               -- (e1)
    (Precedes [1, 3, 4, 0, 2] r r' ∧ (s (.B (i - 1)), s (.B i)) = (0, 1)) ∨         -- (e2)
    (r = 0 ∧ r' = 1 ∧ (s (.B (i - 1)), s (.B i)) = (1, 0)) ∨                        -- (e3)
    (Precedes [0, 1, 2, 3, 4] r r' ∧ (s (.B (i - 1)), s (.B i)) = (1, 1))           -- (e4)

end TwoOptAllExp.TSP


