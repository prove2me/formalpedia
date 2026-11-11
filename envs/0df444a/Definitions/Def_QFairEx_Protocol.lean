-- Prove2me | Definitions.Def_QFairEx_Protocol
-- name    : QFairEx_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:03.692147+00:00
-- url     : https://prove2.me/theorems/11bda42d-1df6-477c-8f55-8e3a8e3f6a9d
-- title:
--   Fair-exchange protocol with a classical trusted party, alternating rounds (Definition 4.1)
-- statement:
--   A **protocol** for two exchange parties $P_0,P_1$ and a classical trusted party $\mathrm{CTTP}$, with input registers $\iota_0,\iota_1$ (the registers verified by $\mathrm{Ver}_0,\mathrm{Ver}_1$), consists of:
--
--   1. register and alphabet types: $P_b$ holds the quantum register $\iota_b\times W_b$ and a classical memory in $K_b$; CTTP holds only a classical state in $C$; the message slots carry $Q_b$ (quantum) and $D_b$ (classical) from $P_b$ to $P_{1-b}$, $B_b$ from $P_b$ to CTTP, and $A_b$ from CTTP to $P_b$;
--   2. a round bound $T$;
--   3. an auxiliary initial cq-state on $K_0\times K_1\times C$ and $W_0\times W_1$, independent of the inputs;
--   4. for every round $r$, with scheduled sender $S(r)=P_0$ for odd $r$ and $P_1$ for even $r$: the sender's generation instrument (retained state, message to CTTP, message to the other party), computed from its state at the end of round $r-1$; the sender's processing after receiving CTTP's message; the non-sender's processing when the scheduled message arrived and, separately, when it was omitted (recorded `abort`); CTTP's generation kernel (messages to both parties); CTTP's processing kernel, which receives the sender's message or `abort`;
--   5. for each party a final decision instrument with outcomes acc (quantum output on $\mathrm{Ver}_{1-b}$'s register) and rej (output on $\mathrm{Ver}_b$'s register).
--
--   The scheduled slots in round $r$ are exactly $S(r)\to\overline{S(r)}$, $S(r)\to\mathrm{CTTP}$, $\mathrm{CTTP}\to P_0$, $\mathrm{CTTP}\to P_1$; an empty payload is an ordinary message value, distinct from an omission, and the non-sender has no slot. The physical conditions on these data are the separate predicate `Protocol.IsValid`.
--
--   **Formalization Note** Classical alphabets are arbitrary types; quantum registers are finite. Each process keeps one register type for all rounds: round-dependent finite registers embed isometrically into one of maximal dimension and round-dependent alphabets into their sum type, so this loses no protocol. The round fields take the round number; only the values the schedule uses enter the executions. The decision instrument after round $T$ stands for the end of the round-$T$ processing. There is no security parameter: perfect security has zero error.
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), §4.1, pp.18–20, Definition 4.1 (p.19) and the settings paragraph (p.20); §3.1, p.13

import Mathlib

namespace QFairEx

/-- **A quantum fair exchange protocol with a classical trusted party in the alternating-round
model** (Definition 4.1).
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), §4.1, pp.18–20, Definition 4.1 (p.19), the settings paragraph
(p.20); §3.1 (p.13).

The input spaces are the registers of the verifiers `Ver₀`, `Ver₁`, with bases `ι0`, `ι1`.
Party `P_b` holds the quantum register `ι_b × W_b` (its input register, plus a work register
`W_b`) and a classical memory in `K_b`; the trusted party `CTTP` holds only a classical state in
`C`. Rounds are `r = 1, …, T`; the scheduled sender `S(r)` is `P₀` for odd `r` and `P₁` for even
`r`. In round `r` the scheduled slots are exactly `S(r) → S(r)‾` (a quantum register `Q_b` together
with a classical part `D_b`), `S(r) → CTTP` (classical, `B_b`), `CTTP → P₀` (`A0`) and
`CTTP → P₁` (`A1`). The fields, for round number `r`:

* `gen0 r` (odd `r`): P₀'s message generation, an instrument from (memory `K0`, register
  `ι0 × W0`) to (retained memory, message to CTTP, classical part of the message to P₁) =
  `K0 × B0 × D0` and (retained register, quantum message) = `(ι0 × W0) × Q0`. It uses only P₀'s
  state at the end of round `r − 1` and fresh randomness.
* `send0 r` (odd `r`): P₀'s local processing after sending; classical input (retained memory,
  CTTP's message `A0`).
* `recv0 r` (even `r`): P₀'s local processing when P₁'s message `(d, Q1)` arrived; classical
  input (memory, `A0`, `d : D1`), quantum input (register, `Q1`).
* `abort0 r` (even `r`): P₀'s local processing when the scheduled message from P₁ was omitted
  (the recorded `abort`); classical input (memory, `A0`).
* `gen1`, `send1` (even `r`), `recv1`, `abort1` (odd `r`): the same for P₁.
* `ttpGen r`: CTTP's message generation, a kernel from its state to (retained state, message to
  P₀, message to P₁).
* `ttpRecv0 r` (odd `r`), `ttpRecv1 r` (even `r`): CTTP's processing; it receives
  `some b` for a delivered message and `none` for an omitted one (`abort`).
* `aux`: the auxiliary initialization, a cq-state on the classical memories `K0 × K1 × C` and
  the work registers `W0 × W1`, fixed by the protocol and independent of the inputs.
* `outAcc0`, `outRej0`: P₀'s final decision instrument after round `T`, with outcome `acc`
  (quantum output in Ver₁'s register `ι1`) or `rej` (quantum output in Ver₀'s register `ι0`);
  `outAcc1`, `outRej1` for P₁ (acc ↦ `ι0`, rej ↦ `ι1`).

Validity (instrument, kernel and state conditions) is the separate predicate
`Protocol.IsValid`.

**Formalization Note.**
1. *Generality.* Classical alphabets (`K_b`, `C`, `A_b`, `B_b`, `D_b`) are arbitrary types;
   quantum registers (`ι_b`, `W_b`, `Q_b`) are finite (`Fintype`, required where used). The
   parties' steps are arbitrary completely positive instruments; CTTP has no quantum register and
   sends and receives only classical messages.
2. *Fixed register types.* Each process keeps one register type and one memory type for all
   rounds. Round-dependent finite registers embed isometrically into one of maximal dimension and
   round-dependent alphabets into their sum type, so a protocol with round-dependent registers is
   simulated with identical output law.
3. *Round-indexed fields.* Every step field takes the round number `r : ℕ`; only the values the
   schedule uses (`1 ≤ r ≤ T`, right parity) enter the executions and the validity predicate.
4. *Omissions.* An omitted scheduled message is a separate branch (`abort0`, `abort1`,
   `ttpRecv · (·, none)`), distinct from any payload value (an "empty payload" is an ordinary
   value of the message type). No omission is recorded for unscheduled slots: the non-sender has
   no outgoing slot.
5. *Final output.* The decision instrument after round `T` stands for the end of P_b's round-`T`
   processing; composing it into that step gives the same outputs.
6. *No security parameter.* Perfect security has zero error, so `κ` plays no role. -/
structure Protocol (ι0 ι1 : Type) where
  /-- P₀'s work register. -/
  W0 : Type
  /-- P₁'s work register. -/
  W1 : Type
  /-- Quantum part of P₀'s message to P₁. -/
  Q0 : Type
  /-- Quantum part of P₁'s message to P₀. -/
  Q1 : Type
  [instFintypeW0 : Fintype W0]
  [instFintypeW1 : Fintype W1]
  [instFintypeQ0 : Fintype Q0]
  [instFintypeQ1 : Fintype Q1]
  [instDecEqW0 : DecidableEq W0]
  [instDecEqW1 : DecidableEq W1]
  [instDecEqQ0 : DecidableEq Q0]
  [instDecEqQ1 : DecidableEq Q1]
  /-- P₀'s classical memory. -/
  K0 : Type
  /-- P₁'s classical memory. -/
  K1 : Type
  /-- CTTP's classical state. -/
  C : Type
  /-- Classical message P₀ → CTTP. -/
  B0 : Type
  /-- Classical message P₁ → CTTP. -/
  B1 : Type
  /-- Classical message CTTP → P₀. -/
  A0 : Type
  /-- Classical message CTTP → P₁. -/
  A1 : Type
  /-- Classical part of P₀'s message to P₁. -/
  D0 : Type
  /-- Classical part of P₁'s message to P₀. -/
  D1 : Type
  /-- The round bound `T`. -/
  T : ℕ
  /-- Auxiliary initialization: a cq-state on `K0 × K1 × C` and `W0 × W1`. -/
  aux : K0 × K1 × C → Matrix (W0 × W1) (W0 × W1) ℂ
  /-- P₀'s message generation in round `r` (odd). -/
  gen0 : ℕ → K0 → K0 × B0 × D0 →
    Matrix (ι0 × W0) (ι0 × W0) ℂ → Matrix ((ι0 × W0) × Q0) ((ι0 × W0) × Q0) ℂ
  /-- P₁'s message generation in round `r` (even). -/
  gen1 : ℕ → K1 → K1 × B1 × D1 →
    Matrix (ι1 × W1) (ι1 × W1) ℂ → Matrix ((ι1 × W1) × Q1) ((ι1 × W1) × Q1) ℂ
  /-- P₀'s processing after sending (odd `r`). -/
  send0 : ℕ → K0 × A0 → K0 → Matrix (ι0 × W0) (ι0 × W0) ℂ → Matrix (ι0 × W0) (ι0 × W0) ℂ
  /-- P₁'s processing after sending (even `r`). -/
  send1 : ℕ → K1 × A1 → K1 → Matrix (ι1 × W1) (ι1 × W1) ℂ → Matrix (ι1 × W1) (ι1 × W1) ℂ
  /-- P₀'s processing on receiving P₁'s message (even `r`). -/
  recv0 : ℕ → K0 × A0 × D1 → K0 →
    Matrix ((ι0 × W0) × Q1) ((ι0 × W0) × Q1) ℂ → Matrix (ι0 × W0) (ι0 × W0) ℂ
  /-- P₁'s processing on receiving P₀'s message (odd `r`). -/
  recv1 : ℕ → K1 × A1 × D0 → K1 →
    Matrix ((ι1 × W1) × Q0) ((ι1 × W1) × Q0) ℂ → Matrix (ι1 × W1) (ι1 × W1) ℂ
  /-- P₀'s processing after an omitted message from P₁ (even `r`). -/
  abort0 : ℕ → K0 × A0 → K0 → Matrix (ι0 × W0) (ι0 × W0) ℂ → Matrix (ι0 × W0) (ι0 × W0) ℂ
  /-- P₁'s processing after an omitted message from P₀ (odd `r`). -/
  abort1 : ℕ → K1 × A1 → K1 → Matrix (ι1 × W1) (ι1 × W1) ℂ → Matrix (ι1 × W1) (ι1 × W1) ℂ
  /-- CTTP's message generation in round `r`. -/
  ttpGen : ℕ → C → C × A0 × A1 → ℝ
  /-- CTTP's processing in odd rounds (`none` = omitted message of P₀). -/
  ttpRecv0 : ℕ → C × Option B0 → C → ℝ
  /-- CTTP's processing in even rounds (`none` = omitted message of P₁). -/
  ttpRecv1 : ℕ → C × Option B1 → C → ℝ
  /-- P₀'s accepting branch; output in Ver₁'s register. -/
  outAcc0 : K0 → Matrix (ι0 × W0) (ι0 × W0) ℂ → Matrix ι1 ι1 ℂ
  /-- P₀'s rejecting branch; output in Ver₀'s register. -/
  outRej0 : K0 → Matrix (ι0 × W0) (ι0 × W0) ℂ → Matrix ι0 ι0 ℂ
  /-- P₁'s accepting branch; output in Ver₀'s register. -/
  outAcc1 : K1 → Matrix (ι1 × W1) (ι1 × W1) ℂ → Matrix ι0 ι0 ℂ
  /-- P₁'s rejecting branch; output in Ver₁'s register. -/
  outRej1 : K1 → Matrix (ι1 × W1) (ι1 × W1) ℂ → Matrix ι1 ι1 ℂ

attribute [instance] Protocol.instFintypeW0 Protocol.instFintypeW1 Protocol.instFintypeQ0
  Protocol.instFintypeQ1 Protocol.instDecEqW0 Protocol.instDecEqW1 Protocol.instDecEqQ0
  Protocol.instDecEqQ1

end QFairEx


