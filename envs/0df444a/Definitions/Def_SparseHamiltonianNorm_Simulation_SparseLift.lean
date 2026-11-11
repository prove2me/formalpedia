-- Prove2me | Definitions.Def_SparseHamiltonianNorm_Simulation_SparseLift
-- name    : SparseHamiltonianNorm_Simulation_SparseLift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:27.992192+00:00
-- url     : https://prove2.me/theorems/2a0c6e08-f5f9-41b2-ad41-789dce386b36
-- title:
--   Sparse-entry lift and Cayley operator
-- statement:
--   The public isometry sends a system basis vector $|i\rangle$ to the uniform superposition of its first $d$ list positions. In row-column coordinates, the lifted operator maps the transpose-paired addresses using weight $\sqrt d\,H_{ij}/(2\Lambda)$, including the scalar diagonal convention. Conjugating by the location permutation returns this operator to list coordinates.
--
--   For any Hermitian finite matrix $M$, define
--   $$\operatorname{Cay}(M)=(M+iI/2)(M-iI/2)^{-1},\qquad H=2\sqrt d\,\Lambda V^\dagger MV.$$
--   The compressed second-moment predicate is $V^\dagger M^2V\preceq I/4$, expressed as positive semidefiniteness of the difference. No lifting identity, unitarity assertion, or approximation estimate is built into these operational definitions.
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), pp.11–13, Eqs. (25)–(32); p.18, Eq. (61); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_SparseAccess

open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace SparseHamiltonianNorm.Simulation
open scoped BigOperators ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eq. (25), with list positions shifted from 1,...,N to Fin N. -/
def sparseV (N d : ℕ) : Matrix (Fin N × Fin N) (Fin N) ℂ :=
  Matrix.of fun il j => if il.1 = j ∧ il.2.val < d then (1 / Real.sqrt d : ℝ) else 0

/-- Eq. (8) on the full address space. -/
def locationMatrix {N : ℕ} (f : Fin N → Equiv.Perm (Fin N)) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  Matrix.of fun ij kl => if ij.1 = kl.1 ∧ ij.2 = f kl.1 kl.2 then 1 else 0

/-- Eq. (26), including the diagonal convention: weighted transpose-pair swap. -/
def liftedRowColumn {N : ℕ} (d : ℕ) (Λ : ℝ) (H : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  Matrix.of fun ij kl => if ij.1 = kl.2 ∧ ij.2 = kl.1 then
    (Real.sqrt d / (2 * Λ) : ℝ) * H ij.1 ij.2 else 0

/-- The actual sparse-entry lift, not a matrix constrained by compressed identities. -/
def sparseM {N : ℕ} (d : ℕ) (Λ : ℝ) (H : Matrix (Fin N) (Fin N) ℂ)
    (f : Fin N → Equiv.Perm (Fin N)) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  (locationMatrix f).conjTranspose * liftedRowColumn d Λ H * locationMatrix f

/-- The source Cayley query, Eq. (31). In every use M is Hermitian, so the inverse is genuine. -/
def cayley {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℂ) : Matrix I I ℂ :=
  (M + (Complex.I / 2) • 1) * (M - (Complex.I / 2) • 1)⁻¹

/-- Loewner upper bound V† M² V ⪯ I/4, expressed as positive semidefiniteness. -/
def CompressedMoment {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (V : Matrix I J ℂ) (M : Matrix I I ℂ) : Prop :=
  ((1 / 4 : ℂ) • (1 : Matrix J J ℂ) - V.conjTranspose * (M * M) * V).PosSemidef

/-- Abstract compressed Hamiltonian, Eq. (61). -/
def compressedH {I J : Type*} [Fintype I] [Fintype J]
    (d : ℕ) (Λ : ℝ) (V : Matrix I J ℂ) (M : Matrix I I ℂ) : Matrix J J ℂ :=
  (2 * Real.sqrt d * Λ : ℝ) • (V.conjTranspose * M * V)

end SparseHamiltonianNorm.Simulation


