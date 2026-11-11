-- Prove2me | Definitions.Def_QMA2ClassicalSep_Main_QueryModel
-- name    : QMA2ClassicalSep_Main_QueryModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:02:15.231446+00:00
-- url     : https://prove2.me/theorems/c3bc659c-768c-4972-b210-532f76167f8c
-- title:
--   Query verifiers for oracle (2) and the one-query protocol of Proposition 4.2
-- statement:
--   A **query verifier** with witness basis $W$ (for $m$ witness qubits, $W=\{0,1\}^m$) and a finite workspace basis $E$ acts on $\mathbb C^W\otimes(\text{query register})\otimes\mathbb C^E$. It starts in $|w\rangle|0\rangle|e_0\rangle$, applies arbitrary unitaries $U_0,\dots,U_q$ interleaved with $q$ applications of $U_O$ (oracle (2), acting on the query register), and accepts with the orthogonal projector $\Pi$:
--   $$
--   \Pr[\text{accept}]=\big\|\Pi\,U_q\,U_O\,U_{q-1}\cdots U_O\,U_0\,(|w\rangle|0\rangle|e_0\rangle)\big\|^2 .
--   $$
--   This is the general (non-uniform) model of Theorem 6.1: any number of workspace qubits, any unitaries, one query per application of $U_O$.
--
--   **The protocol of Proposition 4.2** has witness basis $V$, receives $|\psi\rangle=|\alpha\rangle_A|\beta\rangle_B$, and uses one query. $U_0$ moves the witness into the vertex register, puts the $p$ register into the uniform superposition over $[N]$ ($H^{\otimes k}$ on $|0\rangle$; this register is never touched again, which is the uniformly random choice of $p$) and the direction qubit into $|+\rangle$. After the query, $U_1$ applies CZ between the direction qubit and the sign bit and then a controlled-SWAP, controlled by the direction qubit, of the vertex register and the neighbor register. The accepting projector is $|+\rangle\langle+|$ on the direction qubit.
--
--   **Formalization Note** The unitaries of the protocol are given as explicit matrices; their unitarity is part of the statement of Proposition 4.2.
-- source:
--   Sabee Grewal, Saachi Mutreja, Kabir Tomer, A classical oracle separation between QMA and QMA(2), STOC 2027 submission #618 (October 2026), SHA-256 79883d9d08b98b41b1bb600a6644f3f578ecb803702383a9f2a58d5bc7dacedf, Section 4, p. 17 (query access, one query per application of U_O) and Proposition 4.2 with its proof, pp. 17–18; Theorem 6.1 and its proof, pp. 24, 28

import Definitions.Def_QMA2ClassicalSep_Main_Instance

set_option autoImplicit false

/-!
# Query verifiers for oracle (2), and the one-query protocol of Proposition 4.2

Grewal, Mutreja, Tomer, STOC 2027 submission #618: Section 4, p. 17 (query access
`U_O |p, z, v, w⟩ = |p, z, v, w ⊕ O(p, z, v)⟩`, one application of `U_O` is one query);
Proposition 4.2 and its proof, pp. 17–18; Theorem 6.1, p. 24 and its proof, p. 28 (a QMA verifier
with `m` witness qubits making `q` queries, with acceptance operator `A(ω)` and acceptance
probability `⟨w|A(ω)|w⟩`).
-/

namespace QMA2ClassicalSep.Main

variable {k ℓ : ℕ}

/-- The state space `𝒲 ⊗ (query register) ⊗ (workspace)` of a query verifier with witness
basis `Wt` and workspace basis `E`. -/
abbrev QSpace (k ℓ : ℕ) (Wt E : Type) := Wt × QReg k ℓ × E

/-- `U_O` acting on the query register of the full space, identity on witness and workspace. -/
noncomputable def oracleFull {Wt E : Type} [DecidableEq Wt] [DecidableEq E]
    (inst : SignedInstance k ℓ) : Matrix (QSpace k ℓ Wt E) (QSpace k ℓ Wt E) ℂ :=
  fun s' s => if s'.1 = s.1 ∧ s'.2.2 = s.2.2 ∧ s'.2.1 = inst.queryMap s.2.1 then 1 else 0

/-- The initial vector `|w⟩ ⊗ |0⟩ ⊗ |e₀⟩`. -/
noncomputable def initVec {Wt E : Type} [DecidableEq E] (w : Wt → ℂ) (e₀ : E) :
    QSpace k ℓ Wt E → ℂ :=
  fun s => w s.1 * (if s.2.1 = qzero k ℓ ∧ s.2.2 = e₀ then 1 else 0)

/-- The state after `U_j O U_{j−1} ⋯ O U_0` (with `j` oracle calls). -/
noncomputable def runState {Wt E : Type} [Fintype Wt] [Fintype E]
    (U : ℕ → Matrix (QSpace k ℓ Wt E) (QSpace k ℓ Wt E) ℂ)
    (O : Matrix (QSpace k ℓ Wt E) (QSpace k ℓ Wt E) ℂ) (ψ₀ : QSpace k ℓ Wt E → ℂ) :
    ℕ → QSpace k ℓ Wt E → ℂ
  | 0 => (U 0).mulVec ψ₀
  | j + 1 => (U (j + 1)).mulVec (O.mulVec (runState U O ψ₀ j))

/-- Acceptance probability `‖Π U_q O U_{q−1} ⋯ O U_0 ψ₀‖²` of a `q`-query computation with
unitaries `U_0, …, U_q` (as raw matrices) and accepting projector `Π`. -/
noncomputable def accRaw {Wt E : Type} [Fintype Wt] [Fintype E]
    (U : ℕ → Matrix (QSpace k ℓ Wt E) (QSpace k ℓ Wt E) ℂ) (q : ℕ)
    (P O : Matrix (QSpace k ℓ Wt E) (QSpace k ℓ Wt E) ℂ) (ψ₀ : QSpace k ℓ Wt E → ℂ) : ℝ :=
  ∑ s, Complex.normSq ((P.mulVec (runState U O ψ₀ q)) s)

/-- A (non-uniform) **query verifier** for instances of Problem 4.1 with witness basis `Wt` and
an arbitrary finite workspace `E`: arbitrary unitaries `U_0, …, U_q` on the whole space,
interleaved with `q` applications of `U_O` (oracle (2)), a workspace initial basis state `e₀`
(the query register starts in `|0⟩`), and an accepting orthogonal projector `Π`. -/
structure QueryVerifier (k ℓ : ℕ) (Wt E : Type) [Fintype Wt] [DecidableEq Wt] [Fintype E]
    [DecidableEq E] where
  q : ℕ
  U : Fin (q + 1) → Matrix.unitaryGroup (QSpace k ℓ Wt E) ℂ
  e₀ : E
  P : Matrix (QSpace k ℓ Wt E) (QSpace k ℓ Wt E) ℂ
  P_herm : P.IsHermitian
  P_idem : P * P = P

/-- Acceptance probability `⟨w|A(ω)|w⟩` of a query verifier on witness `w`, with oracle access
to the instance `inst`. -/
noncomputable def QueryVerifier.acc {Wt E : Type} [Fintype Wt] [DecidableEq Wt] [Fintype E]
    [DecidableEq E] (V : QueryVerifier k ℓ Wt E) (inst : SignedInstance k ℓ) (w : Wt → ℂ) : ℝ :=
  accRaw (fun j => if h : j < V.q + 1 then (V.U ⟨j, h⟩).1 else 1)
    V.q V.P (oracleFull inst) (initVec w V.e₀)

/-! ## The one-query QMA(2) protocol of Proposition 4.2 (witness basis `V`, trivial workspace) -/

/-- `(−1)^{p·p'} / √(2^k)`, the entries of `H^{⊗k}`. -/
noncomputable def hadK (p' p : PIdx k) : ℂ :=
  (if (Finset.univ.filter (fun i => p' i = true ∧ p i = true)).card % 2 = 1 then -1 else 1) /
    (Real.sqrt (2 ^ k) : ℂ)

/-- The entries of the one-qubit Hadamard gate. -/
noncomputable def had1 (z' z : Bool) : ℂ :=
  (if z' && z then -1 else 1) / (Real.sqrt 2 : ℂ)

/-- First unitary of the protocol: move the witness `|ψ⟩ = |α⟩|β⟩` into the vertex register
(swap of the witness and vertex registers), put the `p` register in the uniform superposition
over `[N]` (`H^{⊗k}` on `|0⟩`; the `p` register is never touched again, so this is the uniformly
random choice of `p`), and the direction qubit `z` in `|+⟩` (`H` on `|0⟩`). -/
noncomputable def protoU0 : Matrix (QSpace k ℓ (Vtx ℓ) Unit) (QSpace k ℓ (Vtx ℓ) Unit) ℂ :=
  fun s' s =>
    if s'.1 = s.2.1.1.2.2 ∧ s'.2.1.1.2.2 = s.1 ∧ s'.2.1.2 = s.2.1.2 then
      hadK s'.2.1.1.1 s.2.1.1.1 * had1 s'.2.1.1.2.1 s.2.1.1.2.1
    else 0

/-- Second unitary of the protocol: the CZ gate between the direction qubit `z` and the
sign-bit register `t`, followed by the controlled-SWAP of the vertex register and the neighbor
(answer-vertex) register with control `z`. -/
noncomputable def protoU1 : Matrix (QSpace k ℓ (Vtx ℓ) Unit) (QSpace k ℓ (Vtx ℓ) Unit) ℂ :=
  fun s' s =>
    let z := s.2.1.1.2.1
    let t := s.2.1.2.2
    if s'.1 = s.1 ∧ s'.2.1.1.1 = s.2.1.1.1 ∧ s'.2.1.1.2.1 = z ∧ s'.2.1.2.2 = t ∧
        (if z then s'.2.1.1.2.2 = s.2.1.2.1 ∧ s'.2.1.2.1 = s.2.1.1.2.2
         else s'.2.1.1.2.2 = s.2.1.1.2.2 ∧ s'.2.1.2.1 = s.2.1.2.1) then
      (if z && t then -1 else 1)
    else 0

/-- The accepting projector: the direction qubit is measured in the `{|+⟩, |−⟩}` basis and the
verifier accepts on `|+⟩`; this is `|+⟩⟨+|` on `z` tensored with the identity. -/
noncomputable def protoP : Matrix (QSpace k ℓ (Vtx ℓ) Unit) (QSpace k ℓ (Vtx ℓ) Unit) ℂ :=
  fun s' s =>
    if s'.1 = s.1 ∧ s'.2.1.1.1 = s.2.1.1.1 ∧ s'.2.1.1.2.2 = s.2.1.1.2.2 ∧ s'.2.1.2 = s.2.1.2 then
      1 / 2
    else 0

/-- The unitaries `U_0, U_1` of the protocol (identity afterwards). -/
noncomputable def protoU (j : ℕ) : Matrix (QSpace k ℓ (Vtx ℓ) Unit) (QSpace k ℓ (Vtx ℓ) Unit) ℂ :=
  if j = 0 then protoU0 else if j = 1 then protoU1 else 1

/-- Acceptance probability of the one-query protocol on the unentangled witnesses `|α⟩_A`,
`|β⟩_B`, with oracle access to `inst`. -/
noncomputable def protoAcc (inst : SignedInstance k ℓ) (α β : Coord ℓ → ℂ) : ℝ :=
  accRaw protoU 1 protoP (oracleFull inst) (initVec (k := k) (prodVec α β) ())

end QMA2ClassicalSep.Main


