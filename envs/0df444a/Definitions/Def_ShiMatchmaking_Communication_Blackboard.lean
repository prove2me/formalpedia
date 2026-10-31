-- Prove2me | Definitions.Def_ShiMatchmaking_Communication_Blackboard
-- name    : ShiMatchmaking_Communication_Blackboard
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:46:42.450993+00:00
-- url     : https://prove2.me/theorems/cec17f0a-3419-4534-a101-1daee39e8930
-- title:
--   Deterministic blackboard and one-round communication protocols
-- statement:
--   A deterministic blackboard protocol has an agent set $A$, a private input type for each agent, and an output type. It specifies a fixed initial speaker, a public controller taking a history of complete messages to either the next speaker or an output, and a message rule for each agent depending only on that agent's private input and the preceding history. Messages are arbitrary finite binary strings, including the empty string. The first designated agent sends a message; subsequent messages are appended in order. The controller sees the sequence of messages, including their boundaries.
--
--   Termination means that after finitely many messages the controller returns an output. The terminal history is the first such history; after termination the iterative history stays fixed. The result is the controller's output at that history. The concatenated transcript forgets message boundaries. Total bits are the sum of all message lengths, so empty messages cost zero. There is no hypothesis that the result can be recovered from the concatenated transcript. On a nonterminating input only, the terminal-history function is totalized by the empty history and the result by the controller there or a default; matchmaking protocols will require termination on every supported input.
--
--   A one-round protocol specifies one finite message per agent depending solely on that agent's private input, and a deterministic output function of the entire tuple of messages. Its bit count is the sum of the lengths of these messages. No running-time, coding, nonempty-message, or prefix-free restriction is included in either protocol type. These definitions are independent of assignment markets.
-- source:
--   Peng Shi (2023), Optimal Matchmaking Strategy in Two-Sided Marketplaces, Management Science, DOI 10.1287/mnsc.2022.4444, supplied published 65-page artifact; Definitions 3 and 5, PDF/printed pp. 23 and 25; transcript convention, Appendix D.5, p. 40.

import Mathlib

namespace ShiMatchmaking.Communication

abbrev Message := List Bool
abbrev History := List Message

/-- Definition 3: a fixed first speaker, public history controller, local send rules.
No coding, message-length, or running-time restriction is imposed. -/
structure Blackboard (A : Type) (Local : A → Type) (Output : Type) where
  first : A
  control : History → Sum A Output
  send : (a : A) → Local a → History → Message

/-- The initial message is mandatory. After stopping the history stays fixed. -/
def Blackboard.historyAt {A : Type} {Local : A → Type} {Output : Type}
    (P : Blackboard A Local Output) (y : (a : A) → Local a) : ℕ → History
  | 0 => [P.send P.first (y P.first) []]
  | t + 1 =>
    let h := P.historyAt y t
    match P.control h with
    | .inl a => h ++ [P.send a (y a) h]
    | .inr _ => h

def Blackboard.Terminates {A : Type} {Local : A → Type} {Output : Type}
    (P : Blackboard A Local Output) (y : (a : A) → Local a) : Prop :=
  ∃ t, ∃ o, P.control (P.historyAt y t) = Sum.inr o

/-- First terminal history; [] is only a totalization for nonterminating inputs. -/
noncomputable def Blackboard.history {A : Type} {Local : A → Type} {Output : Type}
    (P : Blackboard A Local Output) (y : (a : A) → Local a) : History := by
  classical
  exact if h : P.Terminates y then P.historyAt y (Nat.find h) else []

noncomputable def Blackboard.result {A : Type} {Local : A → Type} {Output : Type}
    [Inhabited Output] (P : Blackboard A Local Output) (y : (a : A) → Local a) : Output :=
  match P.control (P.history y) with
  | .inl _ => default
  | .inr o => o

/-- Concatenation forgets message boundaries. It need not determine the result. -/
noncomputable def Blackboard.transcript {A : Type} {Local : A → Type} {Output : Type}
    (P : Blackboard A Local Output) (y : (a : A) → Local a) : Message :=
  (P.history y).flatten

noncomputable def Blackboard.bits {A : Type} {Local : A → Type} {Output : Type}
    (P : Blackboard A Local Output) (y : (a : A) → Local a) : ℕ :=
  ((P.history y).map List.length).sum

/-- Definition 5: every message depends on its sender's input alone. -/
structure Simultaneous (A : Type) (Local : A → Type) (Output : Type) where
  send : (a : A) → Local a → Message
  output : (A → Message) → Output

def Simultaneous.messages {A : Type} {Local : A → Type} {Output : Type}
    (P : Simultaneous A Local Output) (y : (a : A) → Local a) : A → Message :=
  fun a => P.send a (y a)

def Simultaneous.result {A : Type} {Local : A → Type} {Output : Type}
    (P : Simultaneous A Local Output) (y : (a : A) → Local a) : Output :=
  P.output (P.messages y)

def Simultaneous.bits {A : Type} [Fintype A] {Local : A → Type} {Output : Type}
    (P : Simultaneous A Local Output) (y : (a : A) → Local a) : ℕ :=
  ∑ a, (P.messages y a).length

end ShiMatchmaking.Communication


