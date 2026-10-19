-- Prove2me | Definitions.Def_QAlgorithms_Defs_CKSFourierSimulation
-- name    : QAlgorithms_Defs_CKSFourierSimulation
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:25:47.586697+00:00
-- url     : https://prove2.me/theorems/de0b3e59-10b0-4843-85d8-1dbd8ab33c55
-- title:
--   CKSFourierSimulation
-- statement:
--   CKSFourierSimulation
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\CKSFourierSimulation.lean

import Definitions.Def_QAlgorithms_Defs_CKSFourierData
import Definitions.Def_QAlgorithms_Defs_LinearSystemAccess
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.CKSFourier

/-- QAlgorithms.CKSFourier.selectEvolution: arxiv-1511.02306v2 PDF p.8, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
def selectEvolution {I : Type*} [Fintype I] [DecidableEq I]
    (G : Grid) (A : Matrix I I ℂ) (hA : A.IsHermitian) : Matrix (G.Index × I) (G.Index × I) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then
    (if q.1.2.val = G.K then (1 : Matrix I I ℂ) p.2 q.2 else
      Complex.I*(Real.sign (G.z q.1.2) : ℂ)*
        NormedSpace.exp (-(Complex.I*(G.y q.1.1*G.z q.1.2 : ℝ)) • A) p.2 q.2)
    else 0

/-- QAlgorithms.CKSFourier.IsCoherentSelectSimulation: arxiv-1511.02306v2 PDF p.4, arxiv-1511.02306v2 PDF p.12, arxiv-1511.02306v2 PDF p.15. Source domains are explicit below. -/
def IsCoherentSelectSimulation {I : Type*} [Fintype I] [DecidableEq I]
    (G : Grid) (A : Matrix I I ℂ) (hA : A.IsHermitian)
    (w : ℕ) (V : Matrix ((G.Index × I) × Qubits w) ((G.Index × I) × Qubits w) ℂ)
    (eta : ℝ) : Prop :=
  0 < eta ∧ V ∈ Matrix.unitaryGroup _ ℂ ∧
    let J : Matrix ((G.Index × I) × Qubits w) (G.Index × I) ℂ :=
      Matrix.of fun z x => if z = (x,0) then 1 else 0
    specNorm (V*J-J*selectEvolution G A hA) ≤ eta

example {I : Type*} [Fintype I] [DecidableEq I] (G : Grid)
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (j : Fin G.J) (x y : I) :
    selectEvolution G A hA ((j,⟨G.K,by omega⟩),x) ((j,⟨G.K,by omega⟩),y) =
      (1 : Matrix I I ℂ) x y := by simp [selectEvolution]



end QAlgorithms.CKSFourier


