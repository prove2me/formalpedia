-- Prove2me | Definitions.Def_QAlgorithms_Defs_HeraldedLinearSystems
-- name    : QAlgorithms_Defs_HeraldedLinearSystems
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:24:32.480051+00:00
-- url     : https://prove2.me/theorems/708560cd-2eba-4583-84e3-7286389c2152
-- title:
--   HeraldedLinearSystems
-- statement:
--   HeraldedLinearSystems
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\HeraldedLinearSystems.lean

import Definitions.Def_QAlgorithms_Defs_LinearSystemTargets
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Defs_LinearSystemAccess
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms

/-- QAlgorithms.CKSFourier.IsPureHeraldedSolution: arxiv-1511.02306v2 PDF p.3, arxiv-1511.02306v2 PDF p.9, arxiv-1511.02306v2 PDF p.10. Source domains are explicit below. -/
def CKSFourier.IsPureHeraldedSolution {N w : ℕ} (hN : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : IsUnit A)
    (b : EuclideanSpace ℂ (Fin N)) (hb : b ≠ 0)
    (phi : EuclideanSpace ℂ (Bool × (Qubits (Nat.clog 2 N) × Qubits w))) (eps : ℝ) : Prop :=
  IsState phi ∧ 0 ≤ eps ∧
    let p := ∑ z : Qubits (Nat.clog 2 N) × Qubits w, prob phi (true,z)
    1/2 ≤ p ∧ ∃ approximate : EuclideanSpace ℂ (Fin N), IsState approximate ∧
      ‖approximate-linearSystemSolution hN A hA b hb‖ ≤ eps ∧
      ∃ garbage : EuclideanSpace ℂ (Qubits w), IsState garbage ∧
        ∀ z, phi (true,z)/(Real.sqrt p : ℂ) = padState (Nat.clog 2 N) approximate z.1*garbage z.2

/-- QAlgorithms.OptimalQLSP.IsTraceHeraldedSolution: arxiv-2609.35660v1 PDF p.1, arxiv-2609.35660v1 PDF p.9, arxiv-2609.35660v1 PDF p.16. Source domains are explicit below. -/
def OptimalQLSP.IsTraceHeraldedSolution {N : ℕ} (hN : 0 < N)
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : IsUnit A)
    (b : EuclideanSpace ℂ (Fin N)) (hb : b ≠ 0)
    (success failure : Matrix (Fin N) (Fin N) ℂ) (eps : ℝ) : Prop :=
  success.PosSemidef ∧ failure.PosSemidef ∧ success.trace.re+failure.trace.re = 1 ∧
    0 ≤ eps ∧ 1/2 ≤ success.trace.re ∧
    traceDistance ((success.trace.re : ℂ)⁻¹ • success)
      (pureDensity (linearSystemSolution hN A hA b hb)) ≤ eps

example {N : ℕ} (hN : 0 < N) (A : Matrix (Fin N) (Fin N) ℂ) (hA : IsUnit A)
    (b : EuclideanSpace ℂ (Fin N)) (hb : b ≠ 0) (failure : Matrix (Fin N) (Fin N) ℂ) (eps : ℝ) :
    ¬ OptimalQLSP.IsTraceHeraldedSolution hN A hA b hb 0 failure eps := by
  intro h
  have hp := h.2.2.2.2.1
  norm_num at hp

end QAlgorithms


