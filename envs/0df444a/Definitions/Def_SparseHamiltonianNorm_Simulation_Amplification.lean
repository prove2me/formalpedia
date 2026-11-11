-- Prove2me | Definitions.Def_SparseHamiltonianNorm_Simulation_Amplification
-- name    : SparseHamiltonianNorm_Simulation_Amplification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:17.161664+00:00
-- url     : https://prove2.me/theorems/62669932-c75b-4328-8cc2-81eccc801eb0
-- title:
--   Clean-qubit embedding and three-call oracle syntax
-- statement:
--   For an $s$-qubit system and $a$ clean ancillas, the embedding is
--   $$J_{a,s}\psi=|0^a\rangle\otimes\psi.$$
--   The amplification circuit is a finite oracle circuit over one- and two-qubit unitaries. Its sole oracle is the supplied $(a+s)$-qubit circuit, and its workspace adds one attenuation qubit before the original ancillas. The syntax counts the supplied circuit and its adjoint as oracle calls. It asserts neither an approximation bound nor the existence of amplification.
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), p.11, Lemma 5 and Eq. (24); Appendix A, p.39; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_SparseAccess

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace SparseHamiltonianNorm.Simulation
open QAlgorithms
attribute [local instance] Classical.propDecidable Classical.decEq

/-- All clean ancillas before the full qubit system, for Lemma 5. -/
def cleanQubitInput (a s : ℕ) : Matrix (Qubits (a + s)) (Qubits s) ℂ :=
  Matrix.of fun z j => if (qubitsAppendEquiv a s z).1 = (fun _ => false) ∧
    (qubitsAppendEquiv a s z).2 = j then 1 else 0

/-- One macro oracle is the supplied finite circuit A0; inverse and controlled calls count. -/
abbrev AmplificationCircuit (a s : ℕ) :=
  OracleCircuit oneTwoQubitGateSet (fun _ : Fin 1 => a + s) ((1 + a) + s)

end SparseHamiltonianNorm.Simulation


