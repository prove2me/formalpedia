-- Prove2me | Definitions.Def_QAlgorithms_Defs_Qubitization
-- name    : QAlgorithms_Defs_Qubitization
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:32.503675+00:00
-- url     : https://prove2.me/theorems/770839d3-7ed5-4599-9f8f-a76b054fe31d
-- title:
--   Qubitization
-- statement:
--   Qubitization
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\Qubitization.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- For N,d≥1 and G on ℂ^d, set g=G|0⟩. Source: arxiv-1610.06546v3 PDF p.3; arxiv-1610.06546v3 PDF p.4; arxiv-1610.06546v3 PDF p.5. -/
def standardFormSignal {N d : ℕ} [NeZero N] [NeZero d]
    (U : Matrix (Fin d × Fin N) (Fin d × Fin N) ℂ) (G : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  let g := act G (ket (0 : Fin d))
  let J : Matrix (Fin d × Fin N) (Fin N) ℂ :=
    Matrix.of fun p j => if p.2 = j then g p.1 else 0
  Jᴴ * U * J

/-- Operational helper factorialFeasible_nonempty for the source construction. Source: arxiv-1610.06546v3 PDF p.3; arxiv-1610.06546v3 PDF p.15. -/
theorem factorialFeasible_nonempty (t eps : ℝ) (heps : 0 < eps) :
    {q : ℕ | 1 ≤ q ∧ 4 * |t| ^ q / ((q.factorial : ℝ) * 2 ^ q) ≤ eps}.Nonempty := by
  have h := ((Real.summable_pow_div_factorial (|t| / 2)).tendsto_atTop_zero).const_mul 4
  have hsmall := (show Filter.Tendsto (fun q : ℕ => 4 * ((|t| / 2) ^ q / (q.factorial : ℝ))) Filter.atTop (nhds 0) by simpa using h).eventually_lt_const heps
  obtain ⟨q, hall⟩ := Filter.eventually_atTop.1
    (hsmall.and (Filter.eventually_ge_atTop 1))
  obtain ⟨hq, hbound⟩ := hall q le_rfl
  refine ⟨q, hbound, ?_⟩
  have e : 4 * |t| ^ q / ((q.factorial : ℝ) * 2 ^ q) =
      4 * ((|t| / 2) ^ q / (q.factorial : ℝ)) := by rw [div_pow]; ring
  rw [e]
  exact hq.le

/-- For real t and ε>0, define Q(t,ε)=sInf{q:ℕ | 1≤q ∧ 4*|t|^q/((Nat.factorial q:ℝ)*(2:ℝ)^q)≤ε}. Source: arxiv-1610.06546v3 PDF p.3; arxiv-1610.06546v3 PDF p.15. -/
def factorialQueryScale (t eps : ℝ) (heps : 0 < eps) : ℕ :=
  sInf {q : ℕ | 1 ≤ q ∧ 4 * |t| ^ q / ((q.factorial : ℝ) * 2 ^ q) ≤ eps}

/-- Given a full circuit unitary V on auxiliary plus system plus b≤2 new qubits, initialize all auxiliaries to zero, keep the arbitrary system input, and project the outgoing auxiliaries onto zero. Source: arxiv-1610.06546v3 PDF p.5; arxiv-1610.06546v3 PDF p.14; arxiv-1610.06546v3 PDF p.15; arxiv-1610.06546v3 PDF p.16. -/
def simulationSuccessOperator {N : ℕ} (a b : ℕ)
    (V : Matrix (Qubits a × (Qubits (Nat.clog 2 N) × Qubits b))
      (Qubits a × (Qubits (Nat.clog 2 N) × Qubits b)) ℂ) :
    Matrix (Qubits (Nat.clog 2 N)) (Fin N) ℂ :=
  Matrix.of fun z j => V (0, (z, 0)) (0, (natToBits (Nat.clog 2 N) j, 0))

/-- Sanity test. Source: arxiv-1610.06546v3 PDF p.3; arxiv-1610.06546v3 PDF p.15. -/
example (eps : ℝ) (heps : 0 < eps) : factorialQueryScale 0 eps heps = 1 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨by omega, by simp; exact heps.le⟩
  · exact (Nat.sInf_mem (factorialFeasible_nonempty 0 eps heps)).1

end QAlgorithms


