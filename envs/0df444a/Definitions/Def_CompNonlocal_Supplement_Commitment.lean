-- Prove2me | Definitions.Def_CompNonlocal_Supplement_Commitment
-- name    : CompNonlocal_Supplement_Commitment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:02:17.709141+00:00
-- url     : https://prove2.me/theorems/9e8283a0-1e2e-4295-af1b-22bc258e6c89
-- title:
--   QCCC bit commitment schemes: syntax (Definition 6)
-- statement:
--   A **QCCC bit commitment scheme** consists of a commit protocol $\mathrm{Com}=(\mathrm{Com.Sen},\mathrm{Com.Rec})$ and two algorithms $\mathrm{Open}$, $\mathrm{Ver}$:
--
--   1. $\mathrm{Com}(1^\kappa,b)$ is a classical-communication protocol between a quantum committer holding $b\in\{0,1\}$ and a quantum receiver, over $R(\kappa)$ rounds (the committer speaks in even rounds, the receiver in odd ones). It produces a public classical transcript $T$ and private quantum registers $C$ (committer) and $R$ (receiver).
--   2. $\mathrm{Open}(1^\kappa,b,T,C)\to d$ outputs a classical opening string $d$.
--   3. $\mathrm{Ver}(1^\kappa,T,R,b,d)\to\{0,1\}$ accepts or rejects the opening.
--
--   Derived objects: the message lengths, the finite set of transcripts, the unnormalized registers $C$ and $R$ after a transcript $T$ (their traces multiply to $\Pr[T]$ in an honest execution), the effect of "Open outputs $d$" on $C$, and the effect of "Ver accepts $(b,d)$" on $R$.
--
--   **Formalization Note** Each party is one circuit family run in all its rounds (`partyMem`); a message is the party's full classical output, so message lengths are fixed at each $\kappa$. Ver accepts when its first output bit is $1$. There is no shared setup.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Definition 6, p.22

import Mathlib
import Definitions.Def_CompNonlocal_Family
import Definitions.Def_CompNonlocal_ICirc_effectOn
import Definitions.Def_CompNonlocal_Supplement_partyMem

set_option autoImplicit false

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- QCCC bit commitment schemes: the syntax. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 6, p.22: "A QCCC bit commitment
scheme consists of a commit protocol and two algorithms (Com = (Com.Sen, Com.Rec), Open, Ver) …
Com(1^κ, b) is a classical-communication protocol between a QPT committer holding b ∈ {0, 1} and a
QPT receiver. It produces a public classical transcript T and private registers C, R held by the
committer and receiver, respectively. Open(1^κ, b, T, C) → d is a QPT algorithm that outputs a
classical opening string d. … Ver(1^κ, T, R, b, d) → {0, 1} is a QPT algorithm that accepts or
rejects the opening."

The commit phase has `R κ` rounds; the committer (`Com`, playing Com.Sen) speaks in the even rounds
and the receiver (`Rec`, playing Com.Rec) in the odd rounds, each through `partyMem` (one circuit per
party, round number as input). The derived objects in this module, at security parameter `κ`:
`msgLen κ j`, the length of the message of round `j`; `Trans κ`, the finite set of transcripts;
`tl t`, a transcript as a list of messages; `comMem κ b T` and `recMem κ T`, the unnormalized
private registers `C` and `R` after the transcript `T` (their traces multiply to `Pr[T]` in an
honest commitment to `b`); `openEff κ b T d`, the effect on `C` of "Open outputs `d`";
`verEff κ b T d`, the effect on `R` of "Ver accepts the opening `(b, d)`".

**Formalization Note** A message of a party is its full classical output, so its length is fixed
at each `κ` (a party with nothing to say sends the empty string). The committer reads `[b]`, the
receiver nothing, as private classical input. Open reads `[b] ++ T` and `C`; Ver reads
`[b] ++ T ++ d` and `R` and accepts when its first output bit is `1`. There is no shared setup:
both parties start from `|0⟩`. -/
structure Commitment where
  /-- The committer's round circuit (Com.Sen). -/
  Com : Family
  /-- The receiver's round circuit (Com.Rec). -/
  Rec : Family
  /-- The opening algorithm `Open`. -/
  Open : Family
  /-- The verification algorithm `Ver`. -/
  Ver : Family
  /-- The number of rounds of the commit phase. -/
  R : ℕ → ℕ

namespace Commitment

/-- The length of the message of round `j`: the committer's in even rounds, the receiver's in odd. -/
def msgLen (P : Commitment) (κ j : ℕ) : ℕ :=
  if j % 2 = 0 then (P.Com κ).outC.length else (P.Rec κ).outC.length

/-- The transcripts of the commit phase. -/
abbrev Trans (P : Commitment) (κ : ℕ) : Type := (j : Fin (P.R κ)) → Bits (P.msgLen κ j)

/-- A transcript as the list of its messages. -/
def tl {P : Commitment} {κ : ℕ} (t : P.Trans κ) : List Str := List.ofFn fun j => List.ofFn (t j)

/-- The honest committer's unnormalized register `C` after the transcript `T`, committing to `b`. -/
noncomputable def comMem (P : Commitment) (κ : ℕ) (b : Bool) (T : List Str) :
    Matrix (Bits (P.Com κ).outQ.length) (Bits (P.Com κ).outQ.length) ℂ :=
  partyMem (P.Com κ) (fun j => decide (j % 2 = 0)) [b] T T.length

/-- The honest receiver's unnormalized register `R` after the transcript `T`. -/
noncomputable def recMem (P : Commitment) (κ : ℕ) (T : List Str) :
    Matrix (Bits (P.Rec κ).outQ.length) (Bits (P.Rec κ).outQ.length) ℂ :=
  partyMem (P.Rec κ) (fun j => decide (j % 2 = 1)) [] T T.length

/-- The effect on the committer's register of "Open(1^κ, b, T, C) outputs `d`". -/
noncomputable def openEff (P : Commitment) (κ : ℕ) (b : Bool) (T : List Str) (d : Str) :
    Matrix (Bits (P.Com κ).outQ.length) (Bits (P.Com κ).outQ.length) ℂ :=
  (P.Open κ).effectOn (P.Com κ).outQ.length ([b] ++ T.flatten) (fun o => decide (o = d))

/-- The effect on the receiver's register of "Ver(1^κ, T, R, b, d) = 1". -/
noncomputable def verEff (P : Commitment) (κ : ℕ) (b : Bool) (T : List Str) (d : Str) :
    Matrix (Bits (P.Rec κ).outQ.length) (Bits (P.Rec κ).outQ.length) ℂ :=
  (P.Ver κ).effectOn (P.Rec κ).outQ.length ([b] ++ T.flatten ++ d) (fun o => o.headD false)

end Commitment

end CompNonlocal.Supplement


