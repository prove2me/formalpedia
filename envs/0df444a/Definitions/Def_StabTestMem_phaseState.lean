-- Prove2me | Definitions.Def_StabTestMem_phaseState
-- name    : StabTestMem_phaseState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:34.358239+00:00
-- url     : https://prove2.me/theorems/23a996fc-ad28-4275-a91d-c19f4c233bfe
-- title:
--   Degree-2 phase state $|\psi_A\rangle$
-- statement:
--   For $A\in\mathbb F_2^{n\times n}$, the **degree-2 phase state** is
--
--   $$|\psi_A\rangle=2^{-n/2}\sum_{x\in\mathbb F_2^n}(-1)^{x^\top Ax}|x\rangle .$$
--
--   These are stabilizer states; for uniformly random upper-triangular $A$ they form the hard ensemble of the lower bound.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §3.2, p. 19; Eq. (78), p. 37

import Definitions.Def_QAlgorithms_Defs_Basic

namespace StabTestMem

open QAlgorithms

/-- **The degree-2 phase state `|ψ_A⟩ = 2^{−n/2} Σ_x (−1)^{x^⊤Ax} |x⟩`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §3.2, p. 19: "|ψ_A⟩ :=
2^{−n/2} Σ_{x∈F_2^n} (−1)^{x^T Ax} |x⟩. That is, |ψ_A⟩ is a degree 2 phase state", and Eq. (78),
p. 37.

Amplitude at the basis string `x`: `2^{−n/2} (−1)^{Σ_{i,j} x_i A_{ij} x_j}`, the exponent computed
in `F₂`. -/
noncomputable def phaseState {n : ℕ} (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun x =>
    ((Real.sqrt (2 ^ n))⁻¹ : ℂ) *
      (-1 : ℂ) ^ (∑ i, ∑ j, (if x i then (1 : ZMod 2) else 0) * A i j *
        (if x j then (1 : ZMod 2) else 0)).val

end StabTestMem


