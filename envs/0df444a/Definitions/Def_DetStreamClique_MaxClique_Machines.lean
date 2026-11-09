-- Prove2me | Definitions.Def_DetStreamClique_MaxClique_Machines
-- name    : DetStreamClique_MaxClique_Machines
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:57:54.141971+00:00
-- url     : https://prove2.me/theorems/4a2380cb-7874-4734-9888-0c8bb553411c
-- title:
--   Deterministic streaming machines and one-way protocols
-- statement:
--   A deterministic streaming machine has an initial memory state, an update map from the next input and current state to a new state, and an output map on the final state. Running it folds the update once over the input list. Local computation is unrestricted. A deterministic one-way protocol consists of Alice's message as a function of her input alone, and Bob's output as a function of that message and his input alone.
--
--   A finite memory or message alphabet $S$ fits in $s$ bits when
--   $$|S|\le 2^s.$$
--
--   The input, output and state types are separate parameters, so this interface is reusable for other streaming and communication problems. Memory bounds and correctness are predicates applied outside the structures; neither structure assumes any lower bound or target theorem.
-- source:
--   Adithya Diddapur, Deterministic Streaming Lower Bounds for Approximate Maximum Clique and Maximum Independent Set, STOC 2027 submission #248 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/248.pdf, §1 and §2.1, pp. 2, 6

import Mathlib

namespace DetStreamClique.MaxClique

/-- A deterministic one-pass machine. Computation between items is unrestricted. -/
structure StreamingMachine (Input Output State : Type) where
  init : State
  update : Input → State → State
  output : State → Output

def StreamingMachine.run {I O S : Type} (a : StreamingMachine I O S) (xs : List I) : O :=
  a.output (xs.foldl (fun st e => a.update e st) a.init)

/-- Alice sees only her input; Bob sees only the message and his own input. -/
structure OneWayProtocol (AliceInput BobInput Message Output : Type) where
  send : AliceInput → Message
  receive : Message → BobInput → Output

/-- A fixed alphabet encodable using at most s bits. -/
def FitsBits (State : Type) [Fintype State] (s : ℕ) : Prop :=
  Fintype.card State ≤ 2 ^ s

end DetStreamClique.MaxClique


