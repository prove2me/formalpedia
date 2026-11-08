-- Prove2me | Definitions.Def_EntangledPIR_Strategy
-- name    : EntangledPIR_Strategy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:07:59.890139+00:00
-- url     : https://prove2.me/theorems/59110cde-0fb6-473a-8f58-55d0c8830237
-- title:
--   Messages, instruments in Kraus form, and strategies of a server
-- statement:
--   A message is a bit string of at most $L$ bits. An instrument from a register $\mathsf{In}$ to a register $\mathsf{Out}$ with outcomes $o$ is given by Kraus operators $K_{o,c}$, with $\sum_{o,c}K_{o,c}^\dagger K_{o,c}=1$, and acts by $\rho\mapsto\sum_cK_{o,c}\rho K_{o,c}^\dagger$ on outcome $o$. A strategy of a server specifies its registers at each round and, for each round, classical history and current message of the client, an instrument whose outcome is its message to the client. A channel is a map with a trace-preserving Kraus form.
--
--   The strategy of a server may depend on the database and the public parameters. It cannot depend on the index or the random string of the client.
--
--   **Formalization Note** The type of a strategy has neither the index nor the random string in it. Fresh registers enter through a larger output register. Instruments past the last round exist in the type and are never executed.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), §2.1, p.10; A.1, p.53

import Mathlib

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), §2.1,
p.10: messages, instruments, strategies of a server.
-/

open Matrix

namespace EntangledPIR

/-- A classical message of at most `L` bits. Messages are bit lists; a server's alphabet in a round
is `BitStr L`. **Formalization Note.** The client rejects messages longer than their prescribed
lengths (A.1, p.53). With `L` above every prescribed length, all over-long messages are represented
by the strings of length `L`, which the client rejects the same way. -/
abbrev BitStr (L : ℕ) : Type := {l : List Bool // l.length ≤ L}

noncomputable instance (L : ℕ) : Fintype (BitStr L) :=
  have : Finite (BitStr L) := (List.finite_length_le Bool L).to_subtype
  Fintype.ofFinite _

/-- The message `l` as an element of `BitStr L`. The client's messages have length at most `L`, so
the truncation never acts on them (proved in the verification file). -/
def BitStr.ofList (L : ℕ) (l : List Bool) : BitStr L := ⟨l.take L, List.length_take_le L l⟩

/-- **An instrument**, in Kraus form with a classical outcome `o : O`, from register `In` to register
`Out` (Out may contain fresh registers): `ρ ↦ ∑_{c} K_{o,c} ρ K_{o,c}^†` on outcome `o`, with the
completeness relation `∑_{o,c} K_{o,c}^† K_{o,c} = 1`. Every finite-dimensional instrument has this
form. The Kraus index `c` plays the role of the environment that the paper's Stinespring remark
keeps, p.10. -/
structure Instrument (In Out O : Type) [Fintype In] [DecidableEq In] [Fintype Out] [Fintype O] where
  /-- the Kraus index -/
  Idx : Type
  /-- the Kraus index is finite -/
  [fin : Fintype Idx]
  /-- the Kraus operators -/
  K : O → Idx → Matrix Out In ℂ
  /-- completeness -/
  complete : ∑ o, ∑ c, (K o c)ᴴ * K o c = 1

attribute [instance] Instrument.fin

/-- The classical history of a server at the start of a round: for each earlier round, the message
that it received from the client and the message that it sent. -/
abbrev ServerHistory : Type := List (List Bool × List Bool)

/-- **A strategy of a server**, p.10: register types `Reg r` that it holds at the start of round `r`,
and, for each round `r`, classical history `h` and message `cur` received in this round, an instrument
from `Reg r` to `Reg (r+1)`, whose outcome is its message to the client. The registers and the
instruments are arbitrary and finite-dimensional.

**Formalization Note.** The type has no index and no random string of the client, so a strategy cannot
depend on them; it is chosen after the database and the public parameters, so it may depend on them.
Rounds are numbered from `0`; instruments after the last round of the schedule exist in the type and
are never executed. -/
structure Strategy (L : ℕ) where
  /-- the registers at the start of each round -/
  Reg : ℕ → Type
  /-- they are finite-dimensional -/
  [fin : ∀ r, Fintype (Reg r)]
  /-- they have decidable equality on basis states -/
  [dec : ∀ r, DecidableEq (Reg r)]
  /-- the instrument of each round, given the classical history and the current message -/
  instr : (r : ℕ) → ServerHistory → List Bool → Instrument (Reg r) (Reg (r + 1)) (BitStr L)

attribute [instance] Strategy.fin Strategy.dec

/-- A channel from operators on `In` to operators on `Out`, p.9: a map with a Kraus form that
preserves the trace. -/
def IsChannel {In Out : Type} [Fintype In] [DecidableEq In] [Fintype Out]
    (Γ : Matrix In In ℂ → Matrix Out Out ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (K : ι → Matrix Out In ℂ),
    (∑ c, (K c)ᴴ * K c = 1) ∧ ∀ X, Γ X = ∑ c, K c * X * (K c)ᴴ

end EntangledPIR


