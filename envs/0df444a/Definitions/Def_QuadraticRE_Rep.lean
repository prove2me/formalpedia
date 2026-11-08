-- Prove2me | Definitions.Def_QuadraticRE_Rep
-- name    : QuadraticRE_Rep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:06:31.740248+00:00
-- url     : https://prove2.me/theorems/d3e32f9c-eb1d-4a9f-9343-0fc2b981cd5b
-- title:
--   Mod-2 branching programs, representations and the size $\sigma$
-- statement:
--   A **mod-2 branching program** on $N$ input bits is a directed acyclic graph without parallel edges, on vertices $\{0,\dots,k-1\}$, with a designated initial vertex $s$ and terminal vertex $t$, in which every edge is labelled by $1$, by a literal $x_i$, or by a literal $1+x_i$. On input $x\in\mathbb F_2^N$ it outputs the parity of the number of paths from $s$ to $t$ all of whose labels evaluate to $1$.
--
--   A **representation** of $f:\{0,1\}^N\to\{0,1\}^b$ is a list of $b$ such programs, one per output bit. Its **total size** is
--   $$\sigma=\sum_{\text{programs}}k+N+b .$$
--
--   These are the objects measured by the complexity bounds of Theorem 4.12.
--
--   **Formalization Note** A missing edge is `none` in the label table, so parallel edges cannot be written. The output is the number of vertex lists that are such paths, reduced mod 2; this set is finite because the graph is acyclic (proved in the verification file). It is not defined through a determinant. $s=t$ is allowed: the one-vertex path then counts once.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), §3.2, "Representations and size", p.14

import Mathlib
import Definitions.Def_QuadraticRE_SD

namespace QuadraticRE

/-- An edge label of a mod-2 branching program: the constant `1` or an input literal. -/
inductive Lit (N : ℕ) where
  | one : Lit N
  | pos (i : Fin N) : Lit N
  | neg (i : Fin N) : Lit N

/-- The value of a label on an input: `1`, `x_i` or `1 + x_i`. -/
def Lit.val {N : ℕ} (x : Fin N → F2) : Lit N → F2
  | .one => 1
  | .pos i => x i
  | .neg i => 1 + x i

/-- A mod-2 branching program, Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), §3.2, "Representations and size", p.14: a directed
acyclic graph without parallel edges, with designated initial and terminal vertices and edges
labelled by input literals or `1`.

**Formalization Note.** Vertices are `Fin k`. `label u v = none` means there is no edge, so parallel
edges cannot be written. `k ≥ 1` follows from the designated vertices. `s = t` is allowed (the empty
path counts once). -/
structure BP (N : ℕ) where
  k : ℕ
  s : Fin k
  t : Fin k
  label : Fin k → Fin k → Option (Lit N)
  acyclic : ∀ v, ¬ Relation.TransGen (fun u w => (label u w).isSome = true) v v

/-- A path from the initial to the terminal vertex, given by its vertex list, whose labels all
evaluate to one on `x`. -/
def BP.IsPath {N : ℕ} (P : BP N) (x : Fin N → F2) (p : List (Fin P.k)) : Prop :=
  p.head? = some P.s ∧ p.getLast? = some P.t ∧
    p.IsChain (fun u w => ∃ l, P.label u w = some l ∧ l.val x = 1)

/-- The output of a branching program, p.14: "the parity of the number of paths from the initial
vertex to the terminal vertex whose labels all evaluate to one".

**Formalization Note.** Defined by counting actual paths, not by a determinant. The set of paths is
finite because the graph is acyclic (proved in the verification file), so `Nat.card` is the count. -/
noncomputable def BP.eval {N : ℕ} (P : BP N) (x : Fin N → F2) : F2 :=
  ((Nat.card {p : List (Fin P.k) // P.IsPath x p} : ℕ) : F2)

/-- A representation of `f : {0,1}^N → {0,1}^b`, p.14: "one mod-2 branching program per output
bit"; `b` is the length of the list. -/
structure Rep where
  N : ℕ
  bps : List (BP N)

/-- The output length `b`. -/
def Rep.b (rep : Rep) : ℕ := rep.bps.length

/-- The total representation size `σ`, p.14: "the sum of the numbers of vertices in these programs
plus `N + b`". -/
def Rep.size (rep : Rep) : ℕ := (rep.bps.map BP.k).sum + rep.N + rep.b

/-- The function `f : {0,1}^N → {0,1}^b` represented by `rep`. -/
noncomputable def Rep.eval (rep : Rep) (x : Fin rep.N → F2) (i : Fin rep.b) : F2 :=
  (rep.bps.get i).eval x

end QuadraticRE


