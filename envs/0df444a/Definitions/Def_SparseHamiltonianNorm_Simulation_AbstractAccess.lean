-- Prove2me | Definitions.Def_SparseHamiltonianNorm_Simulation_AbstractAccess
-- name    : SparseHamiltonianNorm_Simulation_AbstractAccess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:45.874372+00:00
-- url     : https://prove2.me/theorems/b07893a6-ce92-476e-a10b-efef5d24e20a
-- title:
--   Binary Cayley access for an arbitrary finite address space
-- statement:
--   An operator on $\mathbb C^e$ is represented on the minimal binary register, acting as the given matrix on encoded addresses and as identity on unused addresses. An abstract simulation circuit has only the address-space Cayley operator as its oracle, with inverse and controlled queries counted by the published syntax.
--
--   Ordinary gates may depend on the public embedding $V$ and scalar parameters, and the circuit is selected before the hidden matrix $M$. This interface applies to arbitrary finite dimensions and does not specialize the abstract simulation theorem to sparse-entry lifts.
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), pp.13,18,24, Eqs. (31), (61), (80); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_SparseLift

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace SparseHamiltonianNorm.Simulation
open QAlgorithms
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Extend an operator on C^e to its binary register by identity off the encoded subspace. -/
def binaryExtension {e : ℕ} (A : Matrix (Fin e) (Fin e) ℂ) :
    Matrix (Qubits (addressBits e)) (Qubits (addressBits e)) ℂ :=
  Matrix.of fun y z => if h : bitsToNat y < e ∧ bitsToNat z < e then A ⟨_, h.1⟩ ⟨_, h.2⟩
    else if y = z then 1 else 0

/-- Oracle is only the Cayley unitary on E. Public ordinary gates may depend on V. -/
abbrev CayleyCircuit (n e w : ℕ) :=
  OracleCircuit oneTwoQubitGateSet (fun _ : Fin 1 => addressBits e) (w + addressBits n)

end SparseHamiltonianNorm.Simulation


