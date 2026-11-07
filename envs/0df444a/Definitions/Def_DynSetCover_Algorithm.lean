-- Prove2me | Definitions.Def_DynSetCover_Algorithm
-- name    : DynSetCover_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:32.146701+00:00
-- url     : https://prove2.me/theorems/68e08ae6-c61d-462e-9877-2ae15055c811
-- title:
--   §5 — the faster algorithm: states, operations, priorities, work charges, budget, admissible runs and update boundaries
-- statement:
--   Fix a capacity $N\ge2$ with $|A_t|\le N$ at all times, and put $L=\lceil\log_2(2N)\rceil$, $\eta=1/L$. The **floored volume** of an element $e$ at level $i$ is
--   $$\mathrm{vol}(e,i)=\max\{2^{\,i-b(e)},\eta\},\qquad \mathrm{vol}(X,i)=\sum_{e\in X}\mathrm{vol}(e,i).$$
--
--   A **state** consists of the active set $A_t$, an actual level $\ell(e)\in\mathbb Z$ for each element, and a finite set of retained **copies**. A copy $Q$ has an underlying set $S_Q$ of cost $C_Q=c(S_Q)$, an accounting level $q_Q$, a destination level $h_Q$, and lists $U_Q$ (assigned elements at level $h_Q$), $R_Q$ (assigned elements waiting at $h_Q-1$) and $P_Q$ (elements pending transfer into $Q$); $\mathrm{cov}(Q)=U_Q\cup R_Q$. The **physical cover** is the set of input sets with a retained copy. With $A_t(r)=\{e\in A_t:\ell(e)=r\}$, a nonempty uniform copy is **deficient** if $2^{h_Q}\mathrm{vol}(\mathrm{cov}(Q),h_Q)<C_Q/64$ and funded otherwise.
--
--   The operations, with priority, category and work charge:
--   1. **Opening** $(S,r)$, applicable when $2^r\mathrm{vol}(S\cap A_t(r),r)\ge c(S)$: a fresh copy with $q_Q=h_Q=r-1$, $U_Q=R_Q=\emptyset$, $P_Q=S\cap A_t(r)$. Priority $r$, category 2, charge 1.
--   2. **Decrement continuation** into $Q$ ($e\in P_Q$): $e$ leaves $P_Q$ and its old copy, joins $U_Q$, $\ell(e)\leftarrow h_Q$. Priority $h_Q+1$, category 3, charge $\eta$.
--   3. **Starting increment** of a nonempty deficient copy with $P_Q=R_Q=\emptyset$: $h_Q\leftarrow h_Q+1$, the old $U_Q$ minus one element $e$ becomes $R_Q$, $U_Q=\{e\}$, $\ell(e)\leftarrow h_Q$. Priority $q_Q$, category 1, charge $\eta$.
--   4. **Increment continuation** ($P_Q=\emptyset$, $e\in R_Q$): $e$ moves to $U_Q$, $\ell(e)\leftarrow h_Q$. Priority $q_Q$, category 1, charge $\eta$.
--   5. **Commit** of a nonempty funded copy with $P_Q=R_Q=\emptyset$ and $q_Q<h_Q$: $q_Q\leftarrow h_Q$. Priority $q_Q$ (old), category 1, charge 1.
--   6. **Deletion** of a copy with $U_Q=R_Q=P_Q=\emptyset$. Priority $q_Q$, category 1, charge 1.
--
--   An arrival of $e$ activates $e$ and creates a fresh copy $Q$ of $S_e$ with $q_Q=h_Q=\ell(e)=b(e)-1$ and $U_Q=\{e\}$; a departure removes $e$ from the active set and from every list. After each input update the algorithm repeatedly executes a **selected** operation, one that is applicable and maximal in (priority, category), with a fresh budget of $2048$ work points; it stops when no operation is applicable or the selected operation's charge exceeds the remaining budget. A state is **clean at $i$** if no applicable operation has priority at least $i$. The states where it stops are the **update boundaries**.
--
--   **Formalization Note** Copies are pairs (fresh identifier, set index); lists are finite sets. The paper breaks ties inside a (priority, category) class FIFO and moves the head element of a list; here every such choice is allowed (an **admissible run**), and the cheapest sets are any fixed choice. `IsState` collects the states of admissible runs (with their remaining budget), `IsBoundary` their update boundaries; the capacity condition $|A_t|\le N$ is checked at every update.
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), §3.1.1, p.15 (PDF 17); §3.1.3, pp.17–21 (PDF 19–23), (21), (22), input updates; §5, pp.38–42 (PDF 40–44), Modifications 3–4, (37), table p.41, scheduling and work budget

import Mathlib
import Definitions.Def_DynSetCover_Rounding
import Definitions.Def_DynSetCover_Updates

namespace DynSetCover

/-! # The faster algorithm of §5 as a relation on admissible runs

Paul, Solomon, *Weighted Set Cover with Constant Worst-Case Recourse* (STOC 2027 submission,
sha256 a671756b…): copies and assignments §3.1.1, p.15 (PDF 17); rounding, the opening and
deficiency conditions (21), (22), accounting levels, input updates §3.1.3, pp.17–21
(PDF 19–23); Modifications 3 and 4, the operations, the priority and work-point table and the
scheduling rule of §5, pp.38–42 (PDF 40–44).

A **state** records the active set `A_t`, the actual level `ℓ(e)` of each element, and the
retained copies `S_t`. A copy `Q` has an underlying input set `S_Q`, an accounting level `q_Q`,
a destination level `h_Q`, and three element lists: `U_Q` (assigned, at level `h_Q`), `R_Q`
(assigned, waiting at `h_Q − 1`) and `P_Q` (pending transfer into `Q`, still assigned
elsewhere). The physical cover is the set of input sets with at least one retained copy.

**Formalization Note.**
* A copy is a pair `(id, s)` of a fresh identifier and its underlying input set index
  `S_Q = s`; fresh identifiers come from the counter `next`. Lists are stored as finite sets
  (their order is used only for tie-breaking).
* The capacity `N` is a parameter; `L = ⌈log₂(2N)⌉ = Nat.clog 2 (2N)`, `η = 1/L`, and the
  floored volume is `vol(e, i) = max{2^{i−b(e)}, η}` (37). All quantities are real numbers.
* The paper breaks ties inside a (priority, category) class FIFO and moves "the head element"
  of a list. No proof in §§5–6 uses either rule. This development quantifies over every
  **admissible run**: each executed operation is applicable and maximal in (priority, category
  order); a continuation or starting increment may move any element of its list; the update
  stops when no operation is applicable or the chosen maximal operation's work charge exceeds
  the remaining budget of `2048` points. The paper's FIFO run is one admissible run.
* The cheapest sets `S_e` are a parameter `ce` (any fixed choice, `Instance.IsCheapest`). -/

variable (inst : Instance)

/-- A copy: a fresh identifier and the index of its underlying input set `S_Q`. -/
abbrev Copy := ℕ × Fin inst.m

/-- A state of the §5 algorithm. -/
structure State where
  /-- the active set `A_t` -/
  active : Finset (Fin inst.u)
  /-- the actual level `ℓ(e)` -/
  level : Fin inst.u → ℤ
  /-- the retained copies `S_t` -/
  copies : Finset (Copy inst)
  /-- the next fresh copy identifier -/
  next : ℕ
  /-- the accounting level `q_Q` -/
  q : Copy inst → ℤ
  /-- the destination level `h_Q` -/
  h : Copy inst → ℤ
  /-- `U_Q`: assigned elements at actual level `h_Q` -/
  U : Copy inst → Finset (Fin inst.u)
  /-- `R_Q`: assigned elements waiting at actual level `h_Q − 1` -/
  R : Copy inst → Finset (Fin inst.u)
  /-- `P_Q`: elements pending transfer into `Q` -/
  P : Copy inst → Finset (Fin inst.u)

namespace State

/-- The initial state: no element is active and no copy is retained. -/
def init : State inst :=
  ⟨∅, fun _ => 0, ∅, 0, fun _ => 0, fun _ => 0, fun _ => ∅, fun _ => ∅, fun _ => ∅⟩

end State

/-- `L = ⌈log₂(2N)⌉` (p.38). -/
noncomputable def capL (N : ℕ) : ℕ := Nat.clog 2 (2 * N)

/-- `η = 1/L` (p.38). -/
noncomputable def eta (N : ℕ) : ℝ := 1 / (capL N : ℝ)

/-- The floored volume `vol(e, i) = max{2^{i−b(e)}, η}` (37), p.42. -/
noncomputable def vol (N : ℕ) (e : Fin inst.u) (i : ℤ) : ℝ := max ((2 : ℝ) ^ (i - inst.base e)) (eta N)

/-- `vol(X, i) = Σ_{e∈X} vol(e, i)`. -/
noncomputable def volSet (N : ℕ) (X : Finset (Fin inst.u)) (i : ℤ) : ℝ := ∑ e ∈ X, vol inst N e i

/-- The copy cost `C_Q = c(S_Q)`. -/
noncomputable def costQ (Q : Copy inst) : ℝ := inst.c Q.2

/-- The opening batch `S ∩ A_t(r)`, where `A_t(r) = {e ∈ A_t : ℓ(e) = r}` (p.17); it
includes pending elements. -/
noncomputable def batch (s : State inst) (S : Fin inst.m) (r : ℤ) : Finset (Fin inst.u) :=
  (inst.S S).filter (fun e => e ∈ s.active ∧ s.level e = r)

/-- `cov_t(Q) = U_Q ∪ R_Q`, the elements assigned to `Q` (p.39). -/
noncomputable def cov (s : State inst) (Q : Copy inst) : Finset (Fin inst.u) := s.U Q ∪ s.R Q

/-- The deficiency condition (22), p.18, with floored volume (p.42):
`2^{h_Q} vol(cov_t(Q), h_Q) < C_Q / 64`. A nonempty uniform copy is *funded* otherwise. -/
noncomputable def Deficient (N : ℕ) (s : State inst) (Q : Copy inst) : Prop :=
  (2 : ℝ) ^ (s.h Q) * volSet inst N (cov inst s Q) (s.h Q) < costQ inst Q / 64

/-- The internal operations of §5 (p.39–41). -/
inductive Op where
  /-- opening `(S, r)` -/
  | opening (S : Fin inst.m) (r : ℤ)
  /-- decrement continuation into `Q`, transferring `e ∈ P_Q` -/
  | decCont (Q : Copy inst) (e : Fin inst.u)
  /-- starting increment of `Q`, moving `e` first -/
  | startInc (Q : Copy inst) (e : Fin inst.u)
  /-- increment continuation of `Q`, moving `e ∈ R_Q` -/
  | incCont (Q : Copy inst) (e : Fin inst.u)
  /-- commit `Q` -/
  | commit (Q : Copy inst)
  /-- deletion of the empty copy `Q` -/
  | delete (Q : Copy inst)

variable {inst}

namespace Op

/-- The copy a copy operation (starting increment, increment continuation, commit, deletion)
acts on. -/
noncomputable def copyOf : Op inst → Option (Copy inst)
  | startInc Q _ => some Q
  | incCont Q _ => some Q
  | commit Q => some Q
  | delete Q => some Q
  | _ => none

/-- Openings, commits and deletions (work charge 1). -/
noncomputable def isHeavy : Op inst → Bool
  | opening _ _ => true
  | commit _ => true
  | delete _ => true
  | _ => false

/-- Individual element movements: decrement continuations, starting increments and increment
continuations (work charge `η`). -/
noncomputable def isMove : Op inst → Bool
  | decCont _ _ => true
  | startInc _ _ => true
  | incCont _ _ => true
  | _ => false

/-- Copy additions and deletions among scheduled operations: openings and deletions. -/
noncomputable def changesCopies : Op inst → Bool
  | opening _ _ => true
  | delete _ => true
  | _ => false

/-- The tie-breaking category: decrement continuation (3) ≻ opening (2) ≻ copy operation (1)
(p.40). -/
noncomputable def cat : Op inst → ℕ
  | decCont _ _ => 3
  | opening _ _ => 2
  | _ => 1

end Op

variable (inst)

/-- Applicability, exactly as in §5, pp.39–42: an opening needs the opening condition (21)
`2^r vol(S ∩ A_t(r), r) ≥ c(S)` (tested even when a copy of `S` is retained); a copy with
`P_Q ≠ ∅` has only its decrement continuation; a starting increment needs a nonempty uniform
deficient copy; an increment continuation needs `R_Q ≠ ∅`; a commit needs a nonempty uniform
funded copy with `q_Q < h_Q`; a deletion needs `U_Q = R_Q = P_Q = ∅`. -/
noncomputable def Applicable (N : ℕ) (s : State inst) : Op inst → Prop
  | .opening S r => inst.c S ≤ (2 : ℝ) ^ r * volSet inst N (batch inst s S r) r
  | .decCont Q e => Q ∈ s.copies ∧ e ∈ s.P Q
  | .startInc Q e => Q ∈ s.copies ∧ s.P Q = ∅ ∧ s.R Q = ∅ ∧ s.U Q ≠ ∅ ∧
      Deficient inst N s Q ∧ e ∈ s.U Q
  | .incCont Q e => Q ∈ s.copies ∧ s.P Q = ∅ ∧ e ∈ s.R Q
  | .commit Q => Q ∈ s.copies ∧ s.P Q = ∅ ∧ s.R Q = ∅ ∧ s.U Q ≠ ∅ ∧
      ¬ Deficient inst N s Q ∧ s.q Q < s.h Q
  | .delete Q => Q ∈ s.copies ∧ s.U Q = ∅ ∧ s.R Q = ∅ ∧ s.P Q = ∅

/-- The priority, evaluated before execution (table, p.41): opening `(S, r)` has `r`; a
decrement continuation into `Q` has `h_Q + 1`; the copy operations have `q_Q`. -/
noncomputable def prio (s : State inst) : Op inst → ℤ
  | .opening _ r => r
  | .decCont Q _ => s.h Q + 1
  | .startInc Q _ => s.q Q
  | .incCont Q _ => s.q Q
  | .commit Q => s.q Q
  | .delete Q => s.q Q

/-- The work charge (table, p.41): `1` for an opening, commit or deletion, `η = 1/L` for an
element movement. -/
noncomputable def charge (N : ℕ) : Op inst → ℝ
  | .opening _ _ => 1
  | .commit _ => 1
  | .delete _ => 1
  | _ => eta N

/-- `o` is selected in state `s`: it is applicable and maximal in (priority, category order)
among the applicable operations (p.40). -/
noncomputable def Selected (N : ℕ) (s : State inst) (o : Op inst) : Prop :=
  Applicable inst N s o ∧ ∀ o', Applicable inst N s o' →
    prio inst s o' < prio inst s o ∨ (prio inst s o' = prio inst s o ∧ o'.cat ≤ o.cat)

/-- The state is *clean at `i`* if no applicable operation has priority `≥ i` (p.26). -/
noncomputable def CleanAt (N : ℕ) (s : State inst) (i : ℤ) : Prop :=
  ∀ o, Applicable inst N s o → prio inst s o < i

/-- Execution of an internal operation (pp.39–40). -/
noncomputable def exec (s : State inst) : Op inst → State inst
  | .opening S r =>
      let Q : Copy inst := (s.next, S)
      { s with copies := insert Q s.copies, next := s.next + 1,
               q := Function.update s.q Q (r - 1), h := Function.update s.h Q (r - 1),
               U := Function.update s.U Q ∅, R := Function.update s.R Q ∅,
               P := Function.update s.P Q (batch inst s S r) }
  | .decCont Q e =>
      { s with level := Function.update s.level e (s.h Q),
               U := fun Q' => if Q' = Q then insert e ((s.U Q').erase e) else (s.U Q').erase e,
               R := fun Q' => (s.R Q').erase e,
               P := Function.update s.P Q ((s.P Q).erase e) }
  | .startInc Q e =>
      { s with h := Function.update s.h Q (s.h Q + 1),
               level := Function.update s.level e (s.h Q + 1),
               R := Function.update s.R Q ((s.U Q).erase e),
               U := Function.update s.U Q {e} }
  | .incCont Q e =>
      { s with level := Function.update s.level e (s.h Q),
               R := Function.update s.R Q ((s.R Q).erase e),
               U := Function.update s.U Q (insert e (s.U Q)) }
  | .commit Q => { s with q := Function.update s.q Q (s.h Q) }
  | .delete Q => { s with copies := s.copies.erase Q }

/-- An input update (p.21, carried over to §5, p.40): an arrival of `e` activates `e` and
creates a fresh copy `Q` of `S_e` with `q_Q = h_Q = ℓ(e) = b(e) − 1`, `U_Q = {e}`,
`R_Q = P_Q = ∅`; a departure of `e` removes `e` from the active set and from every list
containing it, and deletes no copy. -/
noncomputable def applyUpdate (ce : Fin inst.u → Fin inst.m) (s : State inst) : Upd inst.u → State inst
  | .ins e =>
      let Q : Copy inst := (s.next, ce e)
      { s with active := insert e s.active,
               level := Function.update s.level e (inst.base e - 1),
               copies := insert Q s.copies, next := s.next + 1,
               q := Function.update s.q Q (inst.base e - 1),
               h := Function.update s.h Q (inst.base e - 1),
               U := Function.update s.U Q {e}, R := Function.update s.R Q ∅,
               P := Function.update s.P Q ∅ }
  | .del e =>
      { s with active := s.active.erase e,
               U := fun Q => (s.U Q).erase e, R := fun Q => (s.R Q).erase e,
               P := fun Q => (s.P Q).erase e }

/-- An input update is admissible in `s`: it is valid for the active set, and the active set
afterwards has at most `N` elements (the capacity, p.38). -/
noncomputable def UpdateOK (N : ℕ) (s : State inst) (x : Upd inst.u) : Prop :=
  x.ValidAt s.active ∧ (x.apply s.active).card ≤ N

/-- `Phase N s b ops s' b'`: starting in `s` with remaining budget `b`, the selected operations
`ops` are executed in order, each fitting the remaining budget, reaching `s'` with remaining
budget `b'`. -/
inductive Phase (N : ℕ) : State inst → ℝ → List (Op inst) → State inst → ℝ → Prop
  | refl (s : State inst) (b : ℝ) : Phase N s b [] s b
  | step {s : State inst} {b : ℝ} {o : Op inst} {ops : List (Op inst)} {s' : State inst} {b' : ℝ} :
      Selected inst N s o → charge inst N o ≤ b →
      Phase N (exec inst s o) (b - charge inst N o) ops s' b' → Phase N s b (o :: ops) s' b'

/-- The repair phase stops in `s` with remaining budget `b` (p.41): no operation is
applicable, or the selected maximal operation does not fit the remaining budget ("it is not
substituted by another “cheaper” operation"). -/
noncomputable def Stops (N : ℕ) (s : State inst) (b : ℝ) : Prop :=
  (∀ o, ¬ Applicable inst N s o) ∨ ∃ o, Selected inst N s o ∧ b < charge inst N o

/-- Processing one input update: apply it, then run a repair phase with a fresh budget of
`2048` points until it stops (p.40). -/
noncomputable def Process (N : ℕ) (ce : Fin inst.u → Fin inst.m) (s : State inst) (x : Upd inst.u)
    (s' : State inst) : Prop :=
  UpdateOK inst N s x ∧ ∃ ops b, Phase inst N (applyUpdate inst ce s x) 2048 ops s' b ∧ Stops inst N s' b

/-- `bs` lists the update boundaries `bs 0, …, bs σ.length` of an admissible run on `σ`. -/
noncomputable def IsRun (N : ℕ) (ce : Fin inst.u → Fin inst.m) (σ : List (Upd inst.u)) (bs : ℕ → State inst) :
    Prop :=
  bs 0 = State.init inst ∧ ∀ t (ht : t < σ.length), Process inst N ce (bs t) (σ[t]) (bs (t + 1))

/-- `s` is an **update boundary** (the state in which the algorithm returns its cover) of some
admissible run. -/
noncomputable def IsBoundary (N : ℕ) (ce : Fin inst.u → Fin inst.m) (s : State inst) : Prop :=
  ∃ σ bs, IsRun inst N ce σ bs ∧ bs σ.length = s

/-- `s` is a **state** (after an input update or a completed operation) of some admissible
run, with remaining budget `b`; the initial state has budget `0`. -/
noncomputable def IsState (N : ℕ) (ce : Fin inst.u → Fin inst.m) (s : State inst) (b : ℝ) : Prop :=
  (s = State.init inst ∧ b = 0) ∨
    ∃ s₀ x ops, IsBoundary inst N ce s₀ ∧ UpdateOK inst N s₀ x ∧
      Phase inst N (applyUpdate inst ce s₀ x) 2048 ops s b

/-- The physical cover: the input sets with at least one retained copy (`µ_t(S) > 0`). -/
noncomputable def physCover (s : State inst) : Finset (Fin inst.m) := s.copies.image Prod.snd

end DynSetCover


