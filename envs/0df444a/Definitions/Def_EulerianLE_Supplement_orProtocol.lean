-- Prove2me | Definitions.Def_EulerianLE_Supplement_orProtocol
-- name    : EulerianLE_Supplement_orProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:17:45.050781+00:00
-- url     : https://prove2.me/theorems/40a98b73-2891-4146-8d6c-e88a5861fda3
-- title:
--   The OR protocol on oriented rings (Programs 9 and 10)
-- statement:
--   The OR protocol computes the bitwise OR of input bits $b_0,\dots,b_{n-1}$ around an oriented ring $v_0,\dots,v_{n-1}$ and designates a witness. The OR initiator $v_0$ runs Program 9 on its input $b_0$; every other node $v_i$ runs Program 10 on $b_i$.
--
--   **Program 9** (initiator, input $b$). If $b=1$: Send(CCW, 1); BlockingRecv(CCW, 1); Send(CW, 1); BlockingRecv(CW, 1); output (1, witness). Else: Send(CW, 1); wait until a pulse arrives; if the pulse is CW: BlockingRecv(CW, 1); Send(CW, 1); BlockingRecv(CW, 1); output 0; else: BlockingRecv(CCW, 1); Send(CCW, 1); BlockingRecv(CW, 1); output (1, non-witness).
--
--   **Program 10** (participant, input $b$). Wait until a pulse arrives. If the first pulse is CW: BlockingRecv(CW, 1); if $b=0$: Send(CW, 1); wait until a pulse arrives; if the second pulse is CW: BlockingRecv(CW, 1); Send(CW, 1); output 0; else BlockingRecv(CCW, 1); Send(CCW, 1); output (1, non-witness); if $b=1$: Send(CCW, 1); BlockingRecv(CCW, 1); Send(CW, 1); output (1, witness). Else (the first pulse is CCW): BlockingRecv(CCW, 1); Send(CCW, 1); BlockingRecv(CW, 1); Send(CW, 1); output (1, non-witness).
--
--   Here Send(X, 1) sends one pulse through port X; in BlockingRecv(X, 1) and "the pulse is X", X is the direction in which the pulse travels, so a CW pulse is received at the receiver's CCW port and a CCW pulse at its CW port. Producing an output terminates the program.
--
--   **Formalization Note** The programs are automata in the mission's `NodeProg` model with output type `OrOut`: `.zero` is 0, `.one true` is (1, witness), `.one false` is (1, non-witness). "Wait until a pulse arrives" is a non-consuming test of both ports, the CCW port (a CW pulse) first; the protocol never has pulses at both ports when it waits.
-- source:
--   Frei, Gelles, Ghazy, Nolin, Composable Content-Oblivious Leader Election on Eulerian Graphs, STOC 2027 submission (manuscript sha256 90954a93…), App. D, Programs 9 and 10, pp.48–50 (PDF pp.50–52)

import Mathlib
import Definitions.Def_EulerianLE_Network
import Definitions.Def_EulerianLE_NodeProg
import Definitions.Def_EulerianLE_Code

namespace EulerianLE.Supplement

/-- The program points of Program 9, named after its lines. -/
inductive P9 : Type
  | l2 | l3 | l4 | l5 | l6 | l8 | l9 | l11 | l12 | l13 | l14 | l16 | l17 | l18 | l19
  deriving DecidableEq

/-- Wait until a pulse is queued at port `i` and consume it (the receive instruction of Programs 9, 10). -/
def recvAt {deg : ℕ} (i : Fin deg) : Guard deg := ⟨1, {i}, true⟩

/-- A non-consuming test for at least one pulse at port `i`. -/
def peekAt {deg : ℕ} (i : Fin deg) : Guard deg := ⟨1, {i}, false⟩

/-- **Program 9** (OR protocol with witness indication for rings, OR initiator; Frei, Gelles, Ghazy,
Nolin, *Composable Content-Oblivious Leader Election on Eulerian Graphs*, STOC 2027 submission
(manuscript sha256 90954a93…), App. D, p.49, PDF p.51), with input bit `b`, CW port `cw` and CCW port
`ccw`:

```
1  if b = 1:
2    Send(CCW, 1)
3    BlockingRecv(CCW, 1)   // CCW pulse completes a full traversal of the ring
4    Send(CW, 1)
5    BlockingRecv(CW, 1)
6    output 1, witness
7  else:
8    Send(CW, 1)            // a probe CW pulse
9    wait until a pulse arrives
10   if the pulse is CW:
11     BlockingRecv(CW, 1)
12     Send(CW, 1)
13     BlockingRecv(CW, 1)
14     output 0
15   else:
16     BlockingRecv(CCW, 1)
17     Send(CCW, 1)
18     BlockingRecv(CW, 1)
19     output 1, non-witness
```

**Formalization Note (directions).** `Send(CW, 1)` sends one pulse through the CW port. In
`BlockingRecv(X, 1)` and "the pulse is CW", `X` is the direction in which the pulse travels: a CW pulse
arrives at the receiver's CCW port and a CCW pulse at its CW port (line 3: the CCW pulse sent at line 2
"completes a full traversal of the ring" and so returns through the CW port). So `BlockingRecv(CW, 1)`
consumes a pulse at `ccw`, `BlockingRecv(CCW, 1)` one at `cw`, and line 9 tests both ports without
consuming, the CCW port (a CW pulse) first. Line 1 is decided by the initial state; `output` completes
the program, with `.zero` for "0", `.one true` for "1, witness" and `.one false` for "1, non-witness". -/
def program9 {deg : ℕ} (cw ccw : Fin deg) (b : Bool) : NodeProg deg OrOut where
  State := P9
  init := if b then .l2 else .l8
  step
    | .l2 => .send ccw .l3
    | .l3 => .test [recvAt cw] none fun _ _ => .l4
    | .l4 => .send cw .l5
    | .l5 => .test [recvAt ccw] none fun _ _ => .l6
    | .l6 => .complete (.one true)
    | .l8 => .send cw .l9
    | .l9 => .test [peekAt ccw, peekAt cw] none fun n _ => if n = 0 then .l11 else .l16
    | .l11 => .test [recvAt ccw] none fun _ _ => .l12
    | .l12 => .send cw .l13
    | .l13 => .test [recvAt ccw] none fun _ _ => .l14
    | .l14 => .complete .zero
    | .l16 => .test [recvAt cw] none fun _ _ => .l17
    | .l17 => .send ccw .l18
    | .l18 => .test [recvAt ccw] none fun _ _ => .l19
    | .l19 => .complete (.one false)

/-- The program points of Program 10, named after its lines. -/
inductive P10 : Type
  | l1 | l3 | l5 | l6 | l8 | l9 | l10 | l12 | l13 | l14 | l16 | l17 | l18 | l19
  | l21 | l22 | l23 | l24 | l25
  deriving DecidableEq

/-- **Program 10** (OR protocol with witness indication for rings, participants; App. D, p.50, PDF
p.52), with input bit `b`, CW port `cw` and CCW port `ccw`:

```
1  wait until a pulse arrives
2  if the first pulse is a CW pulse:
3    BlockingRecv(CW, 1)
4    if b = 0:
5      Send(CW, 1)          // forward probe CW pulse
6      wait until a pulse arrives
7      if the second pulse is a CW pulse:
8        BlockingRecv(CW, 1)
9        Send(CW, 1)
10       output 0
11     else:
12       BlockingRecv(CCW, 1)
13       Send(CCW, 1)
14       output 1, non-witness
15   else:                  // b = 1: this node is the witness
16     Send(CCW, 1)
17     BlockingRecv(CCW, 1)
18     Send(CW, 1)
19     output 1, witness
20 else:                    // the first pulse that arrives is a CCW pulse
21   BlockingRecv(CCW, 1)
22   Send(CCW, 1)
23   BlockingRecv(CW, 1)
24   Send(CW, 1)
25   output 1, non-witness
```

**Formalization Note.** Directions as in `program9`: a CW pulse is tested and consumed at `ccw`, a CCW
pulse at `cw`. The test of line 4 (`b`, fixed input) is folded into the transition after line 3. -/
def program10 {deg : ℕ} (cw ccw : Fin deg) (b : Bool) : NodeProg deg OrOut where
  State := P10
  init := .l1
  step
    | .l1 => .test [peekAt ccw, peekAt cw] none fun n _ => if n = 0 then .l3 else .l21
    | .l3 => .test [recvAt ccw] none fun _ _ => if b then .l16 else .l5
    | .l5 => .send cw .l6
    | .l6 => .test [peekAt ccw, peekAt cw] none fun n _ => if n = 0 then .l8 else .l12
    | .l8 => .test [recvAt ccw] none fun _ _ => .l9
    | .l9 => .send cw .l10
    | .l10 => .complete .zero
    | .l12 => .test [recvAt cw] none fun _ _ => .l13
    | .l13 => .send ccw .l14
    | .l14 => .complete (.one false)
    | .l16 => .send ccw .l17
    | .l17 => .test [recvAt cw] none fun _ _ => .l18
    | .l18 => .send cw .l19
    | .l19 => .complete (.one true)
    | .l21 => .test [recvAt cw] none fun _ _ => .l22
    | .l22 => .send ccw .l23
    | .l23 => .test [recvAt ccw] none fun _ _ => .l24
    | .l24 => .send cw .l25
    | .l25 => .complete (.one false)

/-- The **OR protocol** on a ring labelled `e : Fin n ≃ V` (App. D, p.48, PDF p.50): the OR initiator
`v₀ = e 0` runs Program 9 on its input `b 0`, and every other node `vᵢ = e i` runs Program 10 on its
input `b i`; each program uses its node's designated CW and CCW ports. -/
def orProtocol (G : Network) (n : ℕ) (hn : 0 < n) (e : Fin n ≃ G.V) (cw ccw : ∀ v, Fin (G.deg v))
    (b : Fin n → Bool) : ∀ v, NodeProg (G.deg v) OrOut :=
  fun v => if e.symm v = ⟨0, hn⟩ then program9 (cw v) (ccw v) (b (e.symm v))
    else program10 (cw v) (ccw v) (b (e.symm v))

end EulerianLE.Supplement


