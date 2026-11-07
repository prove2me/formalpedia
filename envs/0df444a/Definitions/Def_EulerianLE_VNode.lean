-- Prove2me | Definitions.Def_EulerianLE_VNode
-- name    : EulerianLE_VNode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:44.915201+00:00
-- url     : https://prove2.me/theorems/a712baa6-0220-4da4-8a16-f746fe3b6cb5
-- title:
--   Virtual nodes of the OR protocol on an oriented circuit
-- statement:
--   A **virtual node** of the OR protocol is an OR instance (Program 7 or 8) running in a thread of some node $v$ (a concurrent branch, or the main thread) on the port pair with incoming CW port $i$ and outgoing CW port $j$. Its program point at a time of an execution is read from the node's state.
--
--   For inputs $b_1,\dots,b_k$ of the participants $x_1,\dots,x_k$, the **predicted output** of $x_h$ is $0$ if every $b_h$ is $0$ (in particular if $k=0$), and otherwise $(1,\text{witness})$ for $x_m$ with $m$ the least index such that $b_m=1$ and $(1,\text{non-witness})$ for every other instance, the initiator $x_0$ included.
--
--   These are the objects of Lemma 32, where an oriented circuit is given by its virtual nodes in CW order.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), App. C.5, p.43 (PDF p.45), Lemma 32; Programs 7, 8, p.22

import Mathlib
import Definitions.Def_EulerianLE_Run
import Definitions.Def_EulerianLE_Code

namespace EulerianLE

variable {G : Network}

/-- A virtual node of the OR protocol on an oriented circuit (Frei, Gelles, Ghazy, Nolin, STOC 2027
submission (manuscript sha256 90954a93…), §C.5, p.43): an OR instance at node `v`, running in the
thread `loc` of `v`'s program (`some n`: the `n`-th concurrent branch; `none`: the main thread), on
the port pair with incoming CW port `i` and outgoing CW port `j`. -/
structure VNode (G : Network) where
  v : G.V
  loc : Option ℕ
  i : Fin (G.deg v)
  j : Fin (G.deg v)

/-- The incoming CW port of a virtual node, as a port of the network. -/
def VNode.inPort (x : VNode G) : G.Port := ⟨x.v, x.i⟩

/-- The outgoing CW port of a virtual node, as a port of the network. -/
def VNode.outPort (x : VNode G) : G.Port := ⟨x.v, x.j⟩

/-- The stack of a thread of an interpreted program. -/
def RunState.thread {deg : ℕ} {S : Type} (st : RunState deg S) : Option ℕ → Option (List (Frame deg S))
  | none => if st.brs.isNone then some st.main else none
  | some n => st.brs.bind fun bs => bs[n]?

/-- The program point of the OR instance on the ports `(i, j)` in the thread `loc`, if that thread is
running such an instance. -/
def RunState.orLine {deg : ℕ} {S : Type} (st : RunState deg S) (loc : Option ℕ) (i j : Fin deg) :
    Option (ORLine deg) :=
  match st.thread loc with
  | some (.orf ⟨i', j', l⟩ _ :: _) => if i' = i ∧ j' = j then some l else none
  | _ => none

variable {S Out : G.V → Type} {code : ∀ v, Code (G.deg v) (S v)} {s₀ : ∀ v, S v}
  {fin : ∀ v, Ctx (G.deg v) (S v) → Out v}

/-- The node programs of interpreted program texts. -/
def codeProgs (code : ∀ v, Code (G.deg v) (S v)) (s₀ : ∀ v, S v)
    (fin : ∀ v, Ctx (G.deg v) (S v) → Out v) : ∀ v, NodeProg (G.deg v) (Out v) :=
  fun v => (code v).prog (s₀ v) (fin v)

variable {tag : Tag (codeProgs code s₀ fin)}

/-- The stack of the thread of the virtual node `x` at time `t`. -/
def Run.threadAt (ρ : Run (codeProgs code s₀ fin) tag) (x : VNode G) (t : ℕ) :
    Option (List (Frame (G.deg x.v) (S x.v))) :=
  match (ρ.cfg t).status x.v with
  | .running st => (st : RunState (G.deg x.v) (S x.v)).thread x.loc
  | _ => none

/-- The program point of the OR instance of the virtual node `x` at time `t` (`none` if it is not
running: it has not started, or its thread has moved on after returning). -/
def Run.orLineAt (ρ : Run (codeProgs code s₀ fin) tag) (x : VNode G) (t : ℕ) : Option (ORLine (G.deg x.v)) :=
  match (ρ.cfg t).status x.v with
  | .running st => (st : RunState (G.deg x.v) (S x.v)).orLine x.loc x.i x.j
  | _ => none

/-- The output that Lemma 32 (p.43) predicts for `x_h`, from the inputs `b` of `x_1, …, x_k` (`b 0` is
not used): `0` if every `b_h` is `0` (in particular if `k = 0`), and otherwise `(1, witness)` for
`x_m` with `m` the least index with `b_m = 1` and `(1, non-witness)` for every other instance. -/
def orExpected {k : ℕ} (b : Fin (k + 1) → Bool) (h : Fin (k + 1)) : OrOut :=
  match (List.finRange (k + 1)).find? (fun m => decide (m ≠ 0) && b m) with
  | none => .zero
  | some m => .one (decide (h = m))

end EulerianLE


