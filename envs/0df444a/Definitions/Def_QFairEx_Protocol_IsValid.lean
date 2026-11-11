-- Prove2me | Definitions.Def_QFairEx_Protocol_IsValid
-- name    : QFairEx_Protocol_IsValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:14.778087+00:00
-- url     : https://prove2.me/theorems/5edb12c8-50e6-424d-98db-b2da2d278229
-- title:
--   Validity of a protocol: instruments, kernels, normalized auxiliary state
-- statement:
--   A protocol is **valid** when its data are physical:
--
--   1. $T\ge 1$;
--   2. the auxiliary initialization is a normalized cq-state: every block is positive semidefinite and the block traces sum to $1$;
--   3. in every round $1\le r\le T$, CTTP's generation step is a Markov kernel;
--   4. in every odd round $1\le r\le T$ (sender $P_0$), $P_0$'s generation and post-sending processing and $P_1$'s two receiving steps (message present, message omitted) are completely positive instruments, and CTTP's processing is a Markov kernel;
--   5. in every even round, the same with $P_0$ and $P_1$ exchanged;
--   6. each party's final decision has two completely positive branches, acc and rej, whose traces add up to the input trace.
--
--   Validity makes every classical sum in the executions converge, so the executions and outputs are genuine probabilities and states.
--
--   **Formalization Note** Only the round fields the schedule uses are constrained.
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Definition 4.1, p.19 ("The protocol specifies a public round bound T ≥ 1"); §3.1, p.13

import Mathlib
import Definitions.Def_QFairEx_IsCPInstrument
import Definitions.Def_QFairEx_Protocol
open scoped ComplexOrder

namespace QFairEx

/-- **A valid protocol of the model of Definition 4.1.**
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), §4.1, pp.18–20, Definition 4.1 (p.19: "The protocol specifies a
public round bound T ≥ 1"); §3.1, p.13 (states are density operators, operations completely
positive, channels trace preserving).

`P.IsValid` collects the physical conditions on the data of `Π`:
1. `T ≥ 1`;
2. the auxiliary initialization is a normalized cq-state: every block positive semidefinite,
   block traces summing to `1`;
3. in every round `1 ≤ r ≤ T`, CTTP's generation is a Markov kernel;
4. in every odd round `1 ≤ r ≤ T` (sender P₀): `gen0 r`, `send0 r`, `recv1 r`, `abort1 r` are
   completely positive instruments and `ttpRecv0 r` is a Markov kernel;
5. in every even round `1 ≤ r ≤ T` (sender P₁): `gen1 r`, `send1 r`, `recv0 r`, `abort0 r` are
   completely positive instruments and `ttpRecv1 r` is a Markov kernel;
6. each party's final decision is an instrument with the two branches `acc`, `rej`: both
   branches completely positive, their traces summing to the input trace.

**Formalization Note.** Only the round fields the schedule uses are constrained; the other
values of the round-indexed fields never enter an execution. -/
structure Protocol.IsValid {ι0 ι1 : Type} [Fintype ι0] [Fintype ι1] (P : Protocol ι0 ι1) :
    Prop where
  one_le_T : 1 ≤ P.T
  aux_posSemidef : ∀ k, (P.aux k).PosSemidef
  aux_hasSum : HasSum (fun k => (P.aux k).trace) 1
  ttpGen_kernel : ∀ r, 1 ≤ r → r ≤ P.T → IsMarkovKernel (P.ttpGen r)
  gen0_inst : ∀ r, 1 ≤ r → r ≤ P.T → r % 2 = 1 → IsCPInstrument (P.gen0 r)
  send0_inst : ∀ r, 1 ≤ r → r ≤ P.T → r % 2 = 1 → IsCPInstrument (P.send0 r)
  recv1_inst : ∀ r, 1 ≤ r → r ≤ P.T → r % 2 = 1 → IsCPInstrument (P.recv1 r)
  abort1_inst : ∀ r, 1 ≤ r → r ≤ P.T → r % 2 = 1 → IsCPInstrument (P.abort1 r)
  ttpRecv0_kernel : ∀ r, 1 ≤ r → r ≤ P.T → r % 2 = 1 → IsMarkovKernel (P.ttpRecv0 r)
  gen1_inst : ∀ r, 1 ≤ r → r ≤ P.T → r % 2 = 0 → IsCPInstrument (P.gen1 r)
  send1_inst : ∀ r, 1 ≤ r → r ≤ P.T → r % 2 = 0 → IsCPInstrument (P.send1 r)
  recv0_inst : ∀ r, 1 ≤ r → r ≤ P.T → r % 2 = 0 → IsCPInstrument (P.recv0 r)
  abort0_inst : ∀ r, 1 ≤ r → r ≤ P.T → r % 2 = 0 → IsCPInstrument (P.abort0 r)
  ttpRecv1_kernel : ∀ r, 1 ≤ r → r ≤ P.T → r % 2 = 0 → IsMarkovKernel (P.ttpRecv1 r)
  outAcc0_cp : ∀ k, IsCPMap (P.outAcc0 k)
  outRej0_cp : ∀ k, IsCPMap (P.outRej0 k)
  out0_tp : ∀ k ρ, (P.outAcc0 k ρ).trace + (P.outRej0 k ρ).trace = ρ.trace
  outAcc1_cp : ∀ k, IsCPMap (P.outAcc1 k)
  outRej1_cp : ∀ k, IsCPMap (P.outRej1 k)
  out1_tp : ∀ k ρ, (P.outAcc1 k ρ).trace + (P.outRej1 k ρ).trace = ρ.trace

end QFairEx


