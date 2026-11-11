-- Prove2me | Definitions.Def_PelagicFF_OneWayQProtocol
-- name    : PelagicFF_OneWayQProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:44.545198+00:00
-- url     : https://prove2.me/theorems/b3d39bc6-095e-43df-988b-5d876ef7d9ac
-- title:
--   Quantum one-way protocols with $m$ qubits, shared randomness and no entanglement
-- statement:
--   A **quantum one-way protocol** for a two-party search problem with input sets $X$, $Y$ and output set $Z$ ($Z$ finite) using $m$ qubits consists of
--
--   1. a finite set of public coin values $r$ with a probability law;
--   2. for each coin value $r$ and Alice input $x$, a density operator $\rho_{r,x}$ (positive semidefinite, trace one) on the $2^m$-dimensional space of $m$ qubits, which Alice sends to Bob;
--   3. for each coin value $r$ and Bob input $y$, a measurement $\{M_{r,y,z}\}_{z\in Z}$ on $m$ qubits: positive semidefinite operators summing to the identity.
--
--   Bob outputs the measurement outcome. The success probability on input $(x,y)$ for a relation $R$ is
--   $$\Pr[\text{success}]=\sum_r\Pr[r]\sum_{z\in R(x,y)}\operatorname{Re}\operatorname{tr}\big(M_{r,y,z}\,\rho_{r,x}\big).$$
--
--   The players share randomness but no prior entanglement: the state depends only on Alice's input and the coins, and the measurement only on Bob's input and the coins. Mixed states and POVMs absorb private randomness.
--
--   **Formalization Note** States are matrices indexed by `Fin m → Bool`; density operators and POVMs are the published `WildeQIT.IsDensityOperator` and `ShadowTomography.QuantumLB.POVM` (whose `prob` is the Born-rule sum above).
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §2.1, p.14 (communication models: shared randomness, no prior entanglement); §4.1, p.27 (one-way quantum protocol)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_QuantumLB_POVM

namespace PelagicFF

/-- **Quantum one-way protocol with `m` qubits, shared randomness and no entanglement.**

arXiv:2610.05585 (held version, sha256 4564aef3…), §2.1, p.14: Alice receives `x ∈ X`, Bob receives
`y ∈ Y`, and Bob must output `z ∈ Z`; "In all communication models we consider, the players have
access to shared randomness but no prior entanglement." In a quantum one-way protocol Alice sends a
quantum message to Bob, who measures it and outputs the outcome (§4.1, p.27).

Fields: a finite public-coin type `Coin` with law `coin`; for every coin value `r` and Alice input
`x`, the message `state r x`, a density operator on `m` qubits (index type `Fin m → Bool`, so the
dimension is exactly `2^m`); for every coin value and Bob input `y`, a measurement `meas r y` with
outcomes in `Z`, a POVM (positive semidefinite elements summing to the identity: published
`ShadowTomography.QuantumLB.POVM`).

**Formalization Note.** No entanglement: the state depends on `(r, x)` only and the measurement on
`(r, y)` only. Mixed states cover Alice's private randomness, and POVMs cover Bob's. -/
structure OneWayQProtocol (X Y Z : Type) [Fintype Z] (m : ℕ) where
  /-- The public-coin space. -/
  Coin : Type
  /-- The public-coin space is finite. -/
  [coinFintype : Fintype Coin]
  /-- The law of the public coins. -/
  coin : PMF Coin
  /-- Alice's `m`-qubit message on coins `r` and input `x`. -/
  state : Coin → X → Matrix (Fin m → Bool) (Fin m → Bool) ℂ
  /-- Every message is a density operator. -/
  state_density : ∀ r x, WildeQIT.IsDensityOperator (state r x)
  /-- Bob's measurement on coins `r` and input `y`. -/
  meas : Coin → Y → ShadowTomography.QuantumLB.POVM Z (Fin m → Bool)

attribute [instance] OneWayQProtocol.coinFintype

namespace OneWayQProtocol

variable {X Y Z : Type} [Fintype Z] {m : ℕ}

/-- Success probability of `P` for the relation `R` on the input `(x, y)`:
`∑_r Pr[r] · ∑_{z ∈ R(x,y)} Re tr(M_{r,y,z} ρ_{r,x})` (Born rule, averaged over the public coins). -/
noncomputable def succProb (P : OneWayQProtocol X Y Z m) (R : X → Y → Z → Prop) (x : X) (y : Y) : ℝ :=
  ∑ r, (P.coin r).toReal * (P.meas r y).prob (P.state r x) (R x y)

end OneWayQProtocol

end PelagicFF


