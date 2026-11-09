-- Prove2me | Definitions.Def_TwoOptAllExp_TSP_Canonical
-- name    : TwoOptAllExp_TSP_Canonical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:18:57.994203+00:00
-- url     : https://prove2.me/theorems/6dcaf532-1dfd-4be7-b0e3-e7eab1c39c09
-- title:
--   The canonical sequence $P_n$, change labels and rearrangements
-- statement:
--   A swap is labelled by the state it changes: $A_i$, $B_i$, $C_0$ are flips of binary states, while $D_i^j$ and $E_i^j$ denote the change to state $j$ from state $j-1$, cyclically, so that $D_i^0$ goes from $2$ to $0$ and $E_i^0$ from $4$ to $0$.
--
--   The forward and return traversals are defined by $P_1=Q_1=A_0C_0B_0$,
--   $$P_2=A_1P_1E_1^1D_1^1Q_1E_1^2B_1,\qquad Q_2=P_1E_1^3D_1^0E_1^4Q_1E_1^0B_1,$$
--   and for $k\ge3$
--   $$P_k=A_{k-1}P_{k-1}E_{k-1}^1D_{k-1}^1A_{k-2}D_{k-2}^2Q_{k-1}E_{k-1}^2B_{k-1},$$
--   $$Q_k=P_{k-1}E_{k-1}^3D_{k-1}^0A_{k-2}D_{k-2}^2E_{k-1}^4Q_{k-1}E_{k-1}^0B_{k-1}.$$
--   The canonical sequence for $G_n$ is $P_n$. A change is **ordinary** if it is not some $E_j^4$, and $\hat P_n$ is $P_n$ without the occurrences of $E_j^4$.
--
--   For each $j$, the labels $D_j^0,E_j^4,E_j^0$ occur in $P_n$ in the cyclic order $D_j^0,E_j^4,E_j^0,D_j^0,E_j^4,E_j^0,\dots$, one triple for each block $Q_{j+1}$; the labels of one triple are **corresponding**. A list $L$ is a **rearrangement** of $P_n$ if it arises by moving each occurrence of $E_j^4$ anywhere between its corresponding $D_j^0$ and $E_j^0$, without changing the order of the ordinary changes. Equivalently, $L$ and $P_n$ have the same ordinary subsequence and, for each $j$, the same subsequence of labels $D_j^0,E_j^4,E_j^0$.
--
--   A move between tours **realizes** a label if exactly the state of the label changes, in the way the label names. After a list $L$ of changes, an occurrence of $E_i^4$ is **pending** if its corresponding $D_i^0$ has occurred and it has not been performed, which says that $L$ has more occurrences of $D_i^0$ than of $E_i^4$. The **next unperformed change** is the entry of $\hat P_n$ after the ordinary changes of $L$.
--
--   **Formalization Note** The traversals are defined for all $k\ge1$ and do not depend on $n$, so $Q_n$ is also defined; the paper does not use it. Since the $m$-th $E_j^4$ corresponds to the $m$-th $D_j^0$ and the $m$-th $E_j^0$, correspondence is expressed through subsequences and counts instead of positions.
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, canonical sequence and recursions (3)–(6), p. 21; rearrangement, p. 21

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_States

namespace TwoOptAllExp.TSP

/-- The labels of swaps (p. 21): `A i`, `B i`, `C0` are flips of the corresponding binary states,
and `D i j`, `E i j` stand for `D_i^j`, `E_i^j`, the change to state `j` from state `j - 1`
(cyclically). -/
inductive Label
  | A (i : ℕ) | B (i : ℕ) | C0 | D (i j : ℕ) | E (i j : ℕ)
  deriving DecidableEq, Repr

/-- The state changed by a label. -/
def Label.var : Label → Var
  | .A i => .A i
  | .B i => .B i
  | .C0 => .C0
  | .D i _ => .D i
  | .E i _ => .E i

/-- `l.Changes r r'`: the change of `l.var` from `r` to `r'` is the one named by `l`. A flip changes
the value; `D_i^j` goes from `j - 1` to `j` modulo `3`, and `E_i^j` modulo `5`. -/
def Label.Changes : Label → ℕ → ℕ → Prop
  | .A _, r, r' | .B _, r, r' | .C0, r, r' => r ≠ r'
  | .D _ j, r, r' => r = (j + 2) % 3 ∧ r' = j
  | .E _ j, r, r' => r = (j + 4) % 5 ∧ r' = j

/-- The traversals `(P_k, Q_k)`, by the recursions (3)–(6) of p. 21, for `k ≥ 1`. They do not
depend on `n`. -/
def traversals : ℕ → List Label × List Label
  | 0 => ([], [])
  | 1 => ([.A 0, .C0, .B 0], [.A 0, .C0, .B 0])
  | 2 =>
    let p := (traversals 1).1
    let q := (traversals 1).2
    ([.A 1] ++ p ++ [.E 1 1, .D 1 1] ++ q ++ [.E 1 2, .B 1],
     p ++ [.E 1 3, .D 1 0, .E 1 4] ++ q ++ [.E 1 0, .B 1])
  | k + 3 =>
    let p := (traversals (k + 2)).1
    let q := (traversals (k + 2)).2
    ([.A (k + 2)] ++ p ++ [.E (k + 2) 1, .D (k + 2) 1, .A (k + 1), .D (k + 1) 2] ++ q ++
       [.E (k + 2) 2, .B (k + 2)],
     p ++ [.E (k + 2) 3, .D (k + 2) 0, .A (k + 1), .D (k + 1) 2, .E (k + 2) 4] ++ q ++
       [.E (k + 2) 0, .B (k + 2)])

/-- The forward traversal `P_k`; the canonical sequence for `G_n` is `P_n` (p. 21). -/
def P (k : ℕ) : List Label := (traversals k).1

/-- The return traversal `Q_k`. -/
def Q (k : ℕ) : List Label := (traversals k).2

/-- A change is ordinary if it is not `E_j^4` for any `j` (p. 21). -/
def Label.isOrdinary : Label → Bool
  | .E _ 4 => false
  | _ => true

/-- `P̂_n`: `P_n` with all occurrences of `E_i^4` deleted (Lemma 13, p. 21). -/
def hatP (n : ℕ) : List Label := (P n).filter Label.isOrdinary

/-- The labels `D_j^0`, `E_j^4`, `E_j^0`. In `P_n` they occur for each `j` in the cyclic order
`D_j^0, E_j^4, E_j^0, D_j^0, E_j^4, E_j^0, …`, one such triple for each block `Q_{j+1}` of the
recursions (4) and (6): this is what "corresponding" means on p. 21. -/
def Label.isTriple (j : ℕ) (l : Label) : Bool :=
  l == .D j 0 || l == .E j 4 || l == .E j 0

/-- A rearrangement of `P` (p. 21): each occurrence of `E_j^4` is moved anywhere between its
corresponding `D_j^0` and `E_j^0`, without changing the order of the ordinary changes. -/
def IsRearrangement (P L : List Label) : Prop :=
  L.filter Label.isOrdinary = P.filter Label.isOrdinary ∧
    ∀ j, L.filter (Label.isTriple j) = P.filter (Label.isTriple j)

/-- The move from the tour `τ` to the tour `σ` of `G_n` is the change labelled `l`: exactly the
state `l.var` changes, in the way named by `l`. -/
def Realizes (n : ℕ) (τ σ : Finset (Sym2 (Vtx n))) (l : Label) : Prop :=
  (∀ v, v ≠ l.var → statesOf n σ v = statesOf n τ v) ∧
    l.Changes (statesOf n τ l.var) (statesOf n σ l.var)

/-- The sequence `t 0, …, t ℓ` of tours of `G_n` has the list of labels `L`. -/
def HasLabels (n ℓ : ℕ) (t : ℕ → (space n).Sol) (L : List Label) : Prop :=
  L.length = ℓ ∧ ∀ j, ∀ l, L[j]? = some l → Realizes n (t j).1 (t (j + 1)).1 l

/-- The next unperformed change of `P̂_n` after the changes `L`. -/
def nextChange (n : ℕ) (L : List Label) : Option Label :=
  (hatP n)[(L.filter Label.isOrdinary).length]?

/-- After the changes `L`, an occurrence of `E_i^4` is pending: its corresponding `D_i^0` has
occurred and it has not yet been performed. -/
def Pending (L : List Label) (i : ℕ) : Prop :=
  L.count (.E i 4) < L.count (.D i 0)

end TwoOptAllExp.TSP


