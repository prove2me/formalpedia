-- Prove2me | Definitions.Def_QAlgorithms_Defs_TaylorSimulationData
-- name    : QAlgorithms_Defs_TaylorSimulationData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:09.049359+00:00
-- url     : https://prove2.me/theorems/98cb01e5-3853-4b7e-a31a-728957823212
-- title:
--   TaylorSimulationData
-- statement:
--   TaylorSimulationData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\TaylorSimulationData.lean

import Definitions.Def_QAlgorithms_Defs_PositiveLCU
import Definitions.Def_QAlgorithms_Defs_CircuitResources
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.TaylorSimulation

/-- QAlgorithms.TaylorSimulation.UnitaryDecomposition: arxiv-1412.4687v1 PDF p.1, arxiv-1412.4687v1 PDF p.2. Source domains are explicit below. -/
structure UnitaryDecomposition (I : Type*) [Fintype I] [DecidableEq I] where
  L : ℕ
  alpha : Fin L → ℝ
  positive : ∀ i, 0 < alpha i
  terms : Fin L → Matrix.unitaryGroup I ℂ
  hermitian : (∑ i, (alpha i : ℂ) • (terms i : Matrix I I ℂ)).IsHermitian

/-- QAlgorithms.TaylorSimulation.UnitaryDecomposition.hamiltonian: arxiv-1412.4687v1 PDF p.1, arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.4, arxiv-1412.4687v1 PDF p.3. Source domains are explicit below. -/
def UnitaryDecomposition.hamiltonian {I : Type*} [Fintype I] [DecidableEq I]
    (H : UnitaryDecomposition I) : Matrix I I ℂ := ∑ i, (H.alpha i : ℂ) • (H.terms i : Matrix I I ℂ)

/-- QAlgorithms.TaylorSimulation.signedControlledSelect: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.4. Source domains are explicit below. -/
def signedControlledSelect {I : Type*} [Fintype I] [DecidableEq I]
    (H : UnitaryDecomposition I) : Matrix (Bool × (Fin H.L × I)) (Bool × (Fin H.L × I)) ℂ :=
  controlled (Matrix.of fun p q => if p.1 = q.1 then
    -Complex.I * (H.terms q.1 : Matrix I I ℂ) p.2 q.2 else 0)

/-- QAlgorithms.TaylorSimulation.truncatedOperator: arxiv-1412.4687v1 PDF p.2, arxiv-1412.4687v1 PDF p.3. Source domains are explicit below. -/
def truncatedOperator {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (dt : ℝ) (K : ℕ) : Matrix I I ℂ :=
  ∑ k ∈ Finset.range (K+1), ((k.factorial : ℂ)⁻¹) • (-(Complex.I*(dt : ℂ)) • H)^k

/-- QAlgorithms.TaylorSimulation.factorialTail: arxiv-1412.4687v1 PDF p.3. Source domains are explicit below. -/
def factorialTail (K : ℕ) : ℝ := ∑' k : ℕ, (Real.log 2)^(K+1+k) / ((K+1+k).factorial : ℝ)

/-- QAlgorithms.TaylorSimulation.orderForPrecision: arxiv-1412.4687v1 PDF p.3. Source domains are explicit below. -/
def orderForPrecision (tau : ℝ) (positive : 0 < tau) : ℕ := sInf {K | factorialTail K ≤ tau}

/-- Exponential-factorial tails vanish, so the least cutoff never uses the empty-set default.
Source: arxiv-1412.4687v1 PDF p.3, equation (19). -/
theorem factorialTail_feasible (tau : ℝ) (positive : 0 < tau) : ∃ K, factorialTail K ≤ tau := by
  have ht := tendsto_sum_nat_add (fun k : ℕ => (Real.log 2)^k/(k.factorial : ℝ))
  obtain ⟨M,hM⟩ := Filter.eventually_atTop.mp (ht.eventually_lt_const positive)
  refine ⟨M, ?_⟩
  have hb := (hM (M+1) (Nat.le_succ M)).le
  simpa [factorialTail,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hb

example {I : Type*} [Fintype I] [DecidableEq I] (H : Matrix I I ℂ) (dt : ℝ) :
    truncatedOperator H dt 0 = 1 := by simp [truncatedOperator, Finset.sum_range_succ]

example {I : Type*} [Fintype I] [DecidableEq I] (H : Matrix I I ℂ) :
    truncatedOperator H 0 1 = 1 := by simp [truncatedOperator, Finset.sum_range_succ]



end QAlgorithms.TaylorSimulation


