-- Prove2me | Definitions.Def_EntangledPIR_execState
-- name    : EntangledPIR_execState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:12:16.531331+00:00
-- url     : https://prove2.me/theorems/57202fa4-a60c-4bd2-8e3d-3be54a56cc9a
-- title:
--   The execution, and the view of a server
-- statement:
--   The execution of the client with two strategies, from an initial state $\rho_0$. For a fixed index and random string, `execState` is the subnormalized state of the registers of both servers after $r$ rounds on the branch where the servers' messages are $\tau$; its trace is the probability of $\tau$. In a round, each server applies its instrument, given its classical history and the current message of the client, to its own registers, so the Kraus operators are $K_{\mathsf A}\otimes K_{\mathsf B}$.
--
--   The view of A after round $r$ on index $x$ is the classical-quantum state
--
--   $$\mathrm{View}_{\mathsf A}(x)=\mathbb E_{\text{tape}}\sum_\tau|h_{\mathsf A}(\tau)\rangle\langle h_{\mathsf A}(\tau)|\otimes\mathrm{Tr}_{\mathsf B}\,\rho_{r,\tau},$$
--
--   where $h_{\mathsf A}$ is the classical history of A (all messages received and sent). It is not conditioned on acceptance. The view of B is the same with the roles exchanged. `viewAMid` is the view of A right after it receives the client's message of a round, before its instrument of that round.
--
--   **Formalization Note** The schedule continues with empty messages after an abort; strategies that idle there recover the view at the end of the execution. The round is the timing information.
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), §2.1, §2.2, pp.10–11; A.1, p.53

import Definitions.Def_EntangledPIR_clientStep
import Definitions.Def_EntangledPIR_Strategy
import Definitions.Def_EntangledPIR_CopyB
import Definitions.Def_WildeQIT_partialTrace

/-!
Mantri, *Private Information Retrieval from Two Entangled Servers*, manuscript (Nov. 2026), §2, pp.10–11:
the execution of the client with two servers, and the view of a server.
-/

open Matrix
open scoped Kronecker

namespace EntangledPIR

/-- The classical messages of `r` rounds: a pair per round. In an execution it holds the pair
(message of A, message of B); in a view, the pair (message received, message sent). -/
abbrev Transcript (L r : ℕ) : Type := Fin r → BitStr L × BitStr L

/-- The messages of the servers as lists, the form in which the client reads them. -/
def Transcript.toSrv {L r : ℕ} (τ : Transcript L r) : List (List Bool × List Bool) :=
  List.ofFn fun s => ((τ s).1.1, (τ s).2.1)

section
variable (n m lam : ℕ) (x tape : List Bool)

/-- The client in the round after the server messages `srv`. -/
noncomputable def clientAt (srv : List (List Bool × List Bool)) : ClientOutput :=
  clientStep ⟨n, m, lam, x, tape, srv⟩

/-- The classical history of A given the server messages `srv`: the client's message to A in each
earlier round and A's message. -/
noncomputable def histA (srv : List (List Bool × List Bool)) : ServerHistory :=
  srv.mapIdx fun s p => ((clientAt n m lam x tape (srv.take s)).toA, p.1)

/-- The classical history of B given the server messages `srv`. -/
noncomputable def histB (srv : List (List Bool × List Bool)) : ServerHistory :=
  srv.mapIdx fun s p => ((clientAt n m lam x tape (srv.take s)).toB, p.2)

variable {L : ℕ}

/-- The register `H_A` of the view of A: its classical history as a value of the finite type
`Transcript`, the pair (received from the client, sent to the client) per round. -/
noncomputable def viewHistA {r : ℕ} (τ : Transcript L r) : Transcript L r :=
  fun s => (BitStr.ofList L (clientAt n m lam x tape ((Transcript.toSrv τ).take s)).toA, (τ s).1)

/-- The same for B. -/
noncomputable def viewHistB {r : ℕ} (τ : Transcript L r) : Transcript L r :=
  fun s => (BitStr.ofList L (clientAt n m lam x tape ((Transcript.toSrv τ).take s)).toB, (τ s).2)

variable (SA SB : Strategy L)

/-- The first `r` rounds of a transcript of `r + 1` rounds. -/
def Transcript.init {r : ℕ} (τ : Transcript L (r + 1)) : Transcript L r := fun s => τ s.castSucc

/-- **The execution**, pp.10–11: for fixed index `x` and random string `tape`, the subnormalized
state of the registers of both servers after `r` rounds, on the branch where the servers' messages
are `τ`. Its trace is the probability of `τ`. In round `r`, each server applies the instrument of its
strategy, given its classical history and the current message of the client, to its own registers:
`K_A ⊗ K_B` on the two tensor factors, which are all the servers can do, as they have no direct
channel. A message of the client depends on `x`, `tape` and the earlier messages of the servers. -/
noncomputable def execState (ρ₀ : Matrix (SA.Reg 0 × SB.Reg 0) (SA.Reg 0 × SB.Reg 0) ℂ) :
    (r : ℕ) → Transcript L r → Matrix (SA.Reg r × SB.Reg r) (SA.Reg r × SB.Reg r) ℂ
  | 0, _ => ρ₀
  | r + 1, τ =>
    let τ' : Transcript L r := Transcript.init τ
    let srv := Transcript.toSrv τ'
    let o := τ (Fin.last r)
    let IA := SA.instr r (histA n m lam x tape srv) (clientAt n m lam x tape srv).toA
    let IB := SB.instr r (histB n m lam x tape srv) (clientAt n m lam x tape srv).toB
    ∑ cA, ∑ cB,
      (IA.K o.1 cA ⊗ₖ IB.K o.2 cB) * execState ρ₀ r τ' * (IA.K o.1 cA ⊗ₖ IB.K o.2 cB)ᴴ

end

section
variable {n m lam : ℕ} {L : ℕ} (SA SB : Strategy L)
  (ρ₀ : Matrix (SA.Reg 0 × SB.Reg 0) (SA.Reg 0 × SB.Reg 0) ℂ)

/-- **The view of A**, p.11: its state after `r` rounds on index `x`, for the initial state `ρ₀` and
strategies `SA`, `SB`. It is the classical-quantum state on `H_A ⊗ Reg_A` with `H_A` the classical
history of A (all messages sent and received, in which abort also shows), averaged over the random
string, with everything else traced out and summed: the registers of B and the messages not seen by
A. It is not conditioned on acceptance (Remark 2.2).

**Formalization Note.** The schedule is the same for every run: after the client stops, its messages
are empty and a server may still act, which only adds channels that are the same for all indices, and
idle strategies recover the view "at the end of the execution if it ends earlier". The round number is
the timing information, A.1. -/
noncomputable def viewA (r : ℕ) (x : Bits n) :
    Matrix (Transcript L r × SA.Reg r) (Transcript L r × SA.Reg r) ℂ :=
  ((2 : ℂ) ^ tapeLen n lam)⁻¹ • ∑ tape : Bits (tapeLen n lam), ∑ τ : Transcript L r,
    classicalBlock (viewHistA n m lam (List.ofFn x) (List.ofFn tape) τ)
      (WildeQIT.partialTraceRight
        (execState n m lam (List.ofFn x) (List.ofFn tape) SA SB ρ₀ r τ))

/-- **The view of B**, p.11: the same with the roles of the servers exchanged. -/
noncomputable def viewB (r : ℕ) (x : Bits n) :
    Matrix (Transcript L r × SB.Reg r) (Transcript L r × SB.Reg r) ℂ :=
  ((2 : ℂ) ^ tapeLen n lam)⁻¹ • ∑ tape : Bits (tapeLen n lam), ∑ τ : Transcript L r,
    classicalBlock (viewHistB n m lam (List.ofFn x) (List.ofFn tape) τ)
      (WildeQIT.partialTraceLeft
        (execState n m lam (List.ofFn x) (List.ofFn tape) SA SB ρ₀ r τ))

/-- The view of A at the moment it has received the client's message of round `r`, before its
instrument of that round: the state after `r` rounds with the current message in a further classical
register. For the schedule of `clientStep`, `r = 3` is the view right after step 5(a), Claim C.4. -/
noncomputable def viewAMid (r : ℕ) (x : Bits n) :
    Matrix ((Transcript L r × BitStr L) × SA.Reg r) ((Transcript L r × BitStr L) × SA.Reg r) ℂ :=
  ((2 : ℂ) ^ tapeLen n lam)⁻¹ • ∑ tape : Bits (tapeLen n lam), ∑ τ : Transcript L r,
    classicalBlock
      (viewHistA n m lam (List.ofFn x) (List.ofFn tape) τ,
        BitStr.ofList L
          (clientAt n m lam (List.ofFn x) (List.ofFn tape) (Transcript.toSrv τ)).toA)
      (WildeQIT.partialTraceRight
        (execState n m lam (List.ofFn x) (List.ofFn tape) SA SB ρ₀ r τ))

end

end EntangledPIR


