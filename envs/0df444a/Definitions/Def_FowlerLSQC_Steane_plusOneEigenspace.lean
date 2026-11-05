-- Prove2me | Definitions.Def_FowlerLSQC_Steane_plusOneEigenspace
-- name    : FowlerLSQC_Steane_plusOneEigenspace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:15.226729+00:00
-- url     : https://prove2.me/theorems/ab88fda3-a21c-42c3-a571-61dcd1ccb694
-- title:
--   The subspace stabilized by a Pauli operator
-- statement:
--   For an $n$-qubit Pauli operator $P$, the vectors stabilized by $P$ form the complex subspace
--
--   $$\{\psi\in\mathbb C^{2^n} : P\psi=\psi\}$$
--
--   of the whole $n$-qubit space. Apart from the zero vector, these are the $+1$ eigenvectors of $P$.
--
--   A vector is simultaneously stabilized by several operators exactly when it lies in the intersection of their subspaces, which is how the source's phrase "simultaneously stabilized" is expressed in this mission.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, §10.2, p.113 (PDF p.131); §10.3, p.120 (PDF p.138)

import Definitions.Def_QAlgorithms_Defs_Stabilizer

namespace FowlerLSQC.Steane

open QAlgorithms QAlgorithms.Stabilizer

/-- Fowler, *Towards Large-Scale Quantum Computation*, arXiv:quant-ph/0506126v1, §10.2, p.113
(PDF p.131), and §10.3, p.120 (PDF p.138): the vectors stabilized by a Pauli operator `P`, namely
its `+1` eigenspace `{ψ | Pψ = ψ}`, as a complex subspace of the whole `n`-qubit space.

**Formalization Note.** The zero vector belongs to it, so this is the eigenspace together with `0`.
"Simultaneously stabilized" is the infimum of these subspaces. -/
noncomputable def plusOneEigenspace {n : ℕ} (P : PauliString n) :
    Submodule ℂ (EuclideanSpace ℂ (Qubits n)) where
  carrier := {ψ | act P.toMatrix ψ = ψ}
  add_mem' := by
    intro a b ha hb
    change act P.toMatrix a = a at ha
    change act P.toMatrix b = b at hb
    change act P.toMatrix (a + b) = a + b
    have h : act P.toMatrix (a + b) = act P.toMatrix a + act P.toMatrix b := by
      simp [act, Matrix.mulVec_add]
    rw [h, ha, hb]
  zero_mem' := by
    simp [act]
  smul_mem' := by
    intro c a ha
    change act P.toMatrix a = a at ha
    change act P.toMatrix (c • a) = c • a
    have h : act P.toMatrix (c • a) = c • act P.toMatrix a := by
      simp [act, Matrix.mulVec_smul]
    rw [h, ha]

end FowlerLSQC.Steane


