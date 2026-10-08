-- Prove2me | Definitions.Def_MDPComplexity_PartiallyObserved_Construction
-- name    : MDPComplexity_PartiallyObserved_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:49:40.944748+00:00
-- url     : https://prove2.me/theorems/7ba5368f-3b02-4c89-b383-63af62703f01
-- title:
--   Proof of Theorem 6 (p. 448): the partially observed stationary process built from a quantified Boolean formula
-- statement:
--   Given a quantified Boolean formula $Q_1x_1 \cdots Q_nx_n\, F$ with clauses $C_1, \dots, C_m$, $m \ge 1$, the proof of Theorem 6 (p. 448) builds the following partially observed stationary Markov decision process.
--
--   **States.** The initial state $s_0$; six states $A_{ij}, A'_{ij}, T_{ij}, T'_{ij}, F_{ij}, F'_{ij}$ for each clause $i$ and variable $j$; $2m$ states $A_{i,n+1}, A'_{i,n+1}$; and one further state $\bot$ (the "new state"). So $|S| = 6mn + 2m + 2$. A primed state means that clause $C_i$ is not yet satisfied by the variables already set.
--
--   **Partition.** $\{s_0\}$; for each variable $j$ the set $A_j = \{A_{ij}, A'_{ij} : i = 1, \dots, m\}$ and the sets $T_j = \{T_{ij}\}_i$, $T'_j$, $F_j$, $F'_j$; each $A_{i,n+1}$ and each $A'_{i,n+1}$ in a set by itself; $\{\bot\}$.
--
--   **Decisions and transitions.**
--
--   1. At $s_0$ one decision, leading to $A'_{i1}$ with probability $1/m$ for each $i$.
--   2. If $x_j$ is existential, two decisions at $A_j$, one leading with certainty from $A_{ij}$ to $T_{ij}$ and from $A'_{ij}$ to $T'_{ij}$, the other from $A_{ij}$ to $F_{ij}$ and from $A'_{ij}$ to $F'_{ij}$. If $x_j$ is universal, one decision at $A_j$, leading from $A_{ij}$ to $T_{ij}$ or $F_{ij}$, and from $A'_{ij}$ to $T'_{ij}$ or $F'_{ij}$, with probability $1/2$ each.
--   3. One decision at $T_j, F_j, T'_j, F'_j$: from $T_{ij}$ and $F_{ij}$ to $A_{i,j+1}$; from $T'_{ij}$ to $A_{i,j+1}$ if $x_j$ occurs positively in $C_i$ and to $A'_{i,j+1}$ otherwise; from $F'_{ij}$ to $A_{i,j+1}$ if $x_j$ occurs negatively in $C_i$ and to $A'_{i,j+1}$ otherwise.
--   4. One decision at $A_{i,n+1}$, $A'_{i,n+1}$ and $\bot$, leading to $\bot$ with certainty.
--
--   **Costs.** The decision out of $A'_{i,n+1}$ costs $1$; every other decision costs $0$.
--
--   **Horizon.** $T = 2n + 2$. The process is at $s_0$ at time $0$, in $A_j$ at time $2j-1$, in $T_j, T'_j, F_j$ or $F'_j$ at time $2j$, and at $A_{i,n+1}$ or $A'_{i,n+1}$ at time $2n+1$, where the cost $1$ is paid if the chosen clause is still unsatisfied.
--
--   **Formalization Note.** The paper prints the horizon as $2m+2$ and calls it "just enough time for the process to reach one of $A_{i,n+1}$ or $A'_{i,n+1}$"; that time is $2n+1$, which depends on the number $n$ of variables, so we take $T = 2n+2$ (with $2m+2$ and $m < n$ the cost would never be incurred). The paper's decision sentence speaks of "the set $A'_j$" while its partition sentence puts $A_{ij}$ and $A'_{ij}$ in the single set $A_j$; we follow the partition sentence. The new state is unspecified in the paper; we give it its own set, one zero-cost decision and a self-loop. The construction needs $m \ge 1$ (hypothesis `hm`) for the uniform first step. In Lean, clause $i$ and variable $j$ are indices $i-1$, $j-1$; `Aend i`, `Aend' i` are $A_{i,n+1}$, $A'_{i,n+1}$; `lvlA i k`, `lvlA' i k` are $A_{i,k+1}$, $A'_{i,k+1}$ for $k \le n$; existential decisions are `Bool` (`true` towards $T$), universal and all other decision sets are `Unit`; `horizon n` is $2n+2$.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 448, proof of Theorem 6 (construction; horizon corrected from 2m + 2 to 2n + 2)

import Mathlib
import Definitions.Def_MDPComplexity_PartiallyObserved_Model
import Definitions.Def_MDPComplexity_PartiallyObserved_QSAT

namespace MDPComplexity.PartiallyObserved

/-- The states of the process built in the proof of Theorem 6 (p. 448). Clause `i : Fin m` is the
paper's `C_{i+1}`, variable `j : Fin n` the paper's `x_{j+1}`. `A i j`, `A' i j`, `T i j`, `T' i j`,
`F i j`, `F' i j` are the paper's `A_ij, A′_ij, T_ij, T′_ij, F_ij, F′_ij`; `Aend i`, `Aend' i` are
`A_{i,n+1}`, `A′_{i,n+1}`; `sink` is the "new state". -/
inductive St (n m : ℕ) where
  | s0
  | A (i : Fin m) (j : Fin n)
  | A' (i : Fin m) (j : Fin n)
  | T (i : Fin m) (j : Fin n)
  | T' (i : Fin m) (j : Fin n)
  | F (i : Fin m) (j : Fin n)
  | F' (i : Fin m) (j : Fin n)
  | Aend (i : Fin m)
  | Aend' (i : Fin m)
  | sink
  deriving DecidableEq, Fintype

/-- The sets of the partition Π (p. 448): `{s₀}`; for each variable `j` the set `A_j` (all `A_ij`
and `A′_ij`), `T_j`, `T′_j`, `F_j`, `F′_j`; the singletons `{A_{i,n+1}}` and `{A′_{i,n+1}}`; and
the singleton of the new state. -/
inductive Obs (n m : ℕ) where
  | s0
  | A (j : Fin n)
  | T (j : Fin n)
  | T' (j : Fin n)
  | F (j : Fin n)
  | F' (j : Fin n)
  | Aend (i : Fin m)
  | Aend' (i : Fin m)
  | sink
  deriving DecidableEq, Fintype

variable {n m : ℕ}

/-- The set of Π containing a state. -/
def St.obs : St n m → Obs n m
  | .s0 => .s0
  | .A _ j => .A j
  | .A' _ j => .A j
  | .T _ j => .T j
  | .T' _ j => .T' j
  | .F _ j => .F j
  | .F' _ j => .F' j
  | .Aend i => .Aend i
  | .Aend' i => .Aend' i
  | .sink => .sink

/-- The state `A_{i,k+1}` for `k ≤ n` (Lean level `k`; level `n` is `A_{i,n+1}`). -/
def lvlA (i : Fin m) (k : ℕ) : St n m :=
  if h : k < n then .A i ⟨k, h⟩ else .Aend i

/-- The state `A′_{i,k+1}` for `k ≤ n` (Lean level `k`; level `n` is `A′_{i,n+1}`). -/
def lvlA' (i : Fin m) (k : ℕ) : St n m :=
  if h : k < n then .A' i ⟨k, h⟩ else .Aend' i

/-- Decisions out of a set `A_j`: two (`Bool`, `true` leading to `T`) if `x_j` is existential,
one (`Unit`) if it is universal. -/
abbrev DecA (b : Bool) : Type := cond b Bool Unit

instance instFintypeDecA : (b : Bool) → Fintype (DecA b)
  | true => inferInstanceAs (Fintype Bool)
  | false => inferInstanceAs (Fintype Unit)

instance instNonemptyDecA : (b : Bool) → Nonempty (DecA b)
  | true => inferInstanceAs (Nonempty Bool)
  | false => inferInstanceAs (Nonempty Unit)

/-- The decision sets `D_z` of the construction. -/
def QBF.Dec (φ : QBF n m) : Obs n m → Type
  | .A j => DecA (φ.q j)
  | _ => Unit

instance QBF.instFintypeDec (φ : QBF n m) : (z : Obs n m) → Fintype (φ.Dec z)
  | .A j => instFintypeDecA (φ.q j)
  | .s0 => inferInstanceAs (Fintype Unit)
  | .T _ => inferInstanceAs (Fintype Unit)
  | .T' _ => inferInstanceAs (Fintype Unit)
  | .F _ => inferInstanceAs (Fintype Unit)
  | .F' _ => inferInstanceAs (Fintype Unit)
  | .Aend _ => inferInstanceAs (Fintype Unit)
  | .Aend' _ => inferInstanceAs (Fintype Unit)
  | .sink => inferInstanceAs (Fintype Unit)

instance QBF.instNonemptyDec (φ : QBF n m) : (z : Obs n m) → Nonempty (φ.Dec z)
  | .A j => instNonemptyDecA (φ.q j)
  | .s0 => inferInstanceAs (Nonempty Unit)
  | .T _ => inferInstanceAs (Nonempty Unit)
  | .T' _ => inferInstanceAs (Nonempty Unit)
  | .F _ => inferInstanceAs (Nonempty Unit)
  | .F' _ => inferInstanceAs (Nonempty Unit)
  | .Aend _ => inferInstanceAs (Nonempty Unit)
  | .Aend' _ => inferInstanceAs (Nonempty Unit)
  | .sink => inferInstanceAs (Nonempty Unit)

/-- The step out of a state of `A_j` towards `t` (the `T` state) or `f` (the `F` state): if `x_j` is
existential the decision chooses with certainty; if universal, the single decision leads to `t` and
`f` with equal probability. -/
noncomputable def stepA : (b : Bool) → DecA b → St n m → St n m → PMF (St n m)
  | true, d, t, f => PMF.pure (cond (d : Bool) t f)
  | false, _, t, f => (PMF.uniformOfFintype Bool).map (fun c => if c then t else f)

/-- The transition law of the construction (p. 448). -/
noncomputable def QBF.trans (φ : QBF n m) (hm : 0 < m) :
    (s : St n m) → φ.Dec s.obs → PMF (St n m)
  | .s0, _ =>
      (@PMF.uniformOfFintype (Fin m) _ ⟨⟨0, hm⟩⟩).map (fun i => lvlA' i 0)
  | .A i j, d => stepA (φ.q j) d (.T i j) (.F i j)
  | .A' i j, d => stepA (φ.q j) d (.T' i j) (.F' i j)
  | .T i j, _ => PMF.pure (lvlA i (j.val + 1))
  | .F i j, _ => PMF.pure (lvlA i (j.val + 1))
  | .T' i j, _ =>
      PMF.pure (if (j, true) ∈ φ.clause i then lvlA i (j.val + 1) else lvlA' i (j.val + 1))
  | .F' i j, _ =>
      PMF.pure (if (j, false) ∈ φ.clause i then lvlA i (j.val + 1) else lvlA' i (j.val + 1))
  | .Aend _, _ => PMF.pure .sink
  | .Aend' _, _ => PMF.pure .sink
  | .sink, _ => PMF.pure .sink

/-- The costs of the construction: the decision out of `A′_{i,n+1}` costs 1, every other decision
costs 0 (p. 448). -/
def QBF.cost (φ : QBF n m) : (z : Obs n m) → φ.Dec z → ℝ
  | .Aend' _, _ => 1
  | _, _ => 0

/-- The partially observed stationary process built from a quantified formula `φ` with `m ≥ 1`
clauses in the proof of Theorem 6 (p. 448). -/
noncomputable def QBF.toPOMDP (φ : QBF n m) (hm : 0 < m) : POMDP (St n m) (Obs n m) where
  obs := St.obs
  D := φ.Dec
  c := φ.cost
  p := φ.trans hm

/-- The horizon of the construction, `T = 2n + 2` (the paper prints `2m + 2`; see the note in the
mission: the process reaches `A_{i,n+1}` or `A′_{i,n+1}` at time `2n + 1`). -/
def horizon (n : ℕ) : ℕ := 2 * n + 2

end MDPComplexity.PartiallyObserved


