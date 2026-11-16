-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_NoiseLayer
-- name    : AutoQMem_Lindblad_Supplement_NoiseLayer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:40:01.689327+00:00
-- url     : https://prove2.me/theorems/02d92688-e687-44b7-8446-e1faaeb8772e
-- title:
--   Synchronous Pauli noise layer $N_*$ of rate $\eta$
-- statement:
--   A **synchronous Pauli noise layer** on $n$ qubits is the product channel $N_*=N_{1*}\otimes\cdots\otimes N_{n*}$ with
--   $$N_{i*}(\rho)=(1-\theta_{X,i}-\theta_{Y,i}-\theta_{Z,i})\rho+\theta_{X,i}X_i\rho X_i+\theta_{Y,i}Y_i\rho Y_i+\theta_{Z,i}Z_i\rho Z_i ,$$
--   where $\theta_{P,i}\ge0$ and $\theta_{X,i}+\theta_{Y,i}+\theta_{Z,i}\le1$. It has **rate $\eta$** if $\theta_{P,i}\le\eta$ for every qubit $i$ and every $P\in\{X,Y,Z\}$.
--
--   This is the noise model of the synchronous 4D Toom memory (Theorem 3).
--
--   **Formalization Note** The tensor product is written as the composition of the single-qubit factors embedded in the $n$-qubit space; they act on different qubits and commute. $P_i\rho P_i^\dagger$ is used, which equals $P_i\rho P_i$ for Hermitian Paulis.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.37, eqs. (72)–(73), p. 27 (PDF p. 29)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_pauliAt
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

/-- **Synchronous Pauli noise layer.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from
Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.37, eq. (72),
p. 27 (PDF 29): "A synchronous Pauli noise layer is a product channel N_* = N_{1*} ⊗ ⋯ ⊗ N_{n*} with
N_{i*}(ρ) = (1 − θ_{X,i} − θ_{Y,i} − θ_{Z,i})ρ + θ_{X,i} X_iρX_i + θ_{Y,i} Y_iρY_i + θ_{Z,i} Z_iρZ_i,
where θ_{P,i} ≥ 0 and θ_{X,i} + θ_{Y,i} + θ_{Z,i} ≤ 1."

The map itself is `NoiseLayer.apply`; the rate is `NoiseLayer.HasRate`. -/
structure NoiseLayer (n : ℕ) : Type where
  /-- `θ_{X,i}`. -/
  θX : Fin n → ℝ
  /-- `θ_{Y,i}`. -/
  θY : Fin n → ℝ
  /-- `θ_{Z,i}`. -/
  θZ : Fin n → ℝ
  /-- `θ_{X,i} ≥ 0`. -/
  nonnegX : ∀ i, 0 ≤ θX i
  /-- `θ_{Y,i} ≥ 0`. -/
  nonnegY : ∀ i, 0 ≤ θY i
  /-- `θ_{Z,i} ≥ 0`. -/
  nonnegZ : ∀ i, 0 ≤ θZ i
  /-- `θ_{X,i} + θ_{Y,i} + θ_{Z,i} ≤ 1`. -/
  sum_le : ∀ i, θX i + θY i + θZ i ≤ 1

namespace NoiseLayer

variable {n : ℕ}

/-- The single-qubit factor `N_{i*}` of eq. (72), acting on qubit `i` of the n-qubit space.

**Formalization Note.** `P_i ρ P_i†` with `P_i = pauliAt P i`; the Paulis are Hermitian, so this
is the paper's `P_i ρ P_i`. -/
noncomputable def siteChannel (N : NoiseLayer n) (i : Fin n) (ρ : Op n) : Op n :=
  ((1 - N.θX i - N.θY i - N.θZ i : ℝ) : ℂ) • ρ
    + ((N.θX i : ℝ) : ℂ) • (pauliAt .X i * ρ * (pauliAt .X i)ᴴ)
    + ((N.θY i : ℝ) : ℂ) • (pauliAt .Y i * ρ * (pauliAt .Y i)ᴴ)
    + ((N.θZ i : ℝ) : ℂ) • (pauliAt .Z i * ρ * (pauliAt .Z i)ᴴ)

/-- The product channel `N_* = N_{1*} ⊗ ⋯ ⊗ N_{n*}` (Definition 2.37).

**Formalization Note.** Written as the composition `N_{0*} ∘ N_{1*} ∘ ⋯ ∘ N_{(n-1)*}` of the
single-qubit factors embedded in the n-qubit space; the factors act on distinct qubits and commute,
so this composition is the tensor product channel (in any order). -/
noncomputable def apply (N : NoiseLayer n) : Op n → Op n :=
  (List.finRange n).foldr (fun i g => N.siteChannel i ∘ g) id

/-- **Rate η** (Definition 2.37): "We say that the noise layer has rate η if θ_{P,i} ≤ η for every
qubit i and every P ∈ {X, Y, Z}." -/
def HasRate (N : NoiseLayer n) (η : ℝ) : Prop :=
  ∀ i, N.θX i ≤ η ∧ N.θY i ≤ η ∧ N.θZ i ≤ η

end NoiseLayer

end AutoQMem.Lindblad.Supplement


