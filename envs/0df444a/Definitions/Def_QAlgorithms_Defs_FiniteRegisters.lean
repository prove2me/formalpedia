-- Prove2me | Definitions.Def_QAlgorithms_Defs_FiniteRegisters
-- name    : QAlgorithms_Defs_FiniteRegisters
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:13:40.93668+00:00
-- url     : https://prove2.me/theorems/8c1ed9df-969d-4889-ab61-b569655cfca2
-- title:
--   FiniteRegisters
-- statement:
--   FiniteRegisters
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\FiniteRegisters.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- For D≥1 let r=Nat.clog 2 D. Source: arxiv-1610.06546v3 PDF p.3; arxiv-2405.06051v6 PDF p.4; arxiv-2405.06051v6 PDF p.12; arxiv-1804.05058v1 PDF p.5. -/
def finiteRegisterEmbedding (D : ℕ) : Matrix (Qubits (Nat.clog 2 D)) (Fin D) ℂ :=
  Matrix.of fun z j => if z = natToBits (Nat.clog 2 D) j then 1 else 0

/-- For a finite-register isometry J and unitary V on its source, define padUnitary_J(V)=J V J† + I−J J† on the full qubit register. Source: arxiv-1610.06546v3 PDF p.3; arxiv-1610.06546v3 PDF p.4; arxiv-2405.06051v6 PDF p.4; arxiv-2405.06051v6 PDF p.12; arxiv-1804.05058v1 PDF p.5. -/
def extendEncodedUnitary {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (J : Matrix κ ι ℂ) (V : Matrix ι ι ℂ) : Matrix κ κ ℂ := J * V * Jᴴ + 1 - J * Jᴴ

/-- For a nonempty finite register X with fixed computational basis, Phi_X = (sqrt(card X))^(-1) sum_i |i>|i> on X x X; its density is pureDensity Phi_X. Source: arxiv-2405.06051v6 PDF p.3. -/
def finiteMaxEntangled (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι] :
    EuclideanSpace ℂ (ι × ι) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then ((Real.sqrt (Fintype.card ι))⁻¹ : ℂ) else 0

/-- Sanity test. Source: arxiv-1610.06546v3 PDF p.3; arxiv-1610.06546v3 PDF p.4; arxiv-2405.06051v6 PDF p.4; arxiv-2405.06051v6 PDF p.12; arxiv-1804.05058v1 PDF p.5. -/
example : Nat.clog 2 1 = 0 := by decide

/-- Sanity test. Source: arxiv-1610.06546v3 PDF p.3; arxiv-1610.06546v3 PDF p.4; arxiv-2405.06051v6 PDF p.4; arxiv-2405.06051v6 PDF p.12; arxiv-1804.05058v1 PDF p.5. -/
example : finiteMaxEntangled Unit ((), ()) = 1 := by simp [finiteMaxEntangled]

/-- Sanity test. Source: arxiv-1610.06546v3 PDF p.3; arxiv-1610.06546v3 PDF p.4; arxiv-2405.06051v6 PDF p.4; arxiv-2405.06051v6 PDF p.12; arxiv-1804.05058v1 PDF p.5. -/
example {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (J : Matrix κ ι ℂ) : extendEncodedUnitary J 1 = 1 := by simp [extendEncodedUnitary]

/-- Sanity test. Source: arxiv-1610.06546v3 PDF p.3; arxiv-1610.06546v3 PDF p.4; arxiv-2405.06051v6 PDF p.4; arxiv-2405.06051v6 PDF p.12; arxiv-1804.05058v1 PDF p.5. -/
example {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (J : Matrix κ ι ℂ) (V : Matrix ι ι ℂ) (z : κ) (hz : ∀ j, J z j = 0) (y : κ) :
    extendEncodedUnitary J V z y = (1 : Matrix κ κ ℂ) z y := by
  simp [extendEncodedUnitary, Matrix.mul_apply, hz]

/-- The singleton physical register has zero wires. Source: arxiv-2405.06051v6 PDF p.4. -/
example : finiteRegisterEmbedding 1 (fun _ => false) 0 = 1 := by
  have h : (fun _ : Fin (Nat.clog 2 1) => false) = natToBits (Nat.clog 2 1) (0 : Fin 1) := by
    funext i
    exact False.elim (Nat.not_lt_zero _ (i.isLt.trans_eq (by decide : Nat.clog 2 1 = 0)))
  simp only [finiteRegisterEmbedding, Matrix.of_apply, h, if_pos]
end QAlgorithms


