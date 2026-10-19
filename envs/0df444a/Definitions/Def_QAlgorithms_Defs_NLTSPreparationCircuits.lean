-- Prove2me | Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
-- name    : QAlgorithms_Defs_NLTSPreparationCircuits
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:27:05.019882+00:00
-- url     : https://prove2.me/theorems/cb675e76-57d6-45ba-9649-7419a087b4ac
-- title:
--   NLTSPreparationCircuits
-- statement:
--   NLTSPreparationCircuits
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\NLTSPreparationCircuits.lean

import Definitions.Def_QAlgorithms_Defs_NLTSCodeGeometry
import Definitions.Def_QAlgorithms_Defs_SpectralFilter
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.NLTS

/-- arxiv-2206.13228v4 PDF p.5; arxiv-2206.13228v4 PDF p.9. -/
structure LayeredPreparationCircuit (n : ℕ) where
  ancillas : ℕ
  layers : List (Circuit oneTwoQubitGateSet (n+ancillas))
  disjoint : ∀ layer ∈ layers, layer.Pairwise fun g h =>
    Disjoint (Finset.univ.map g.wires) (Finset.univ.map h.wires)

/-- arxiv-2206.13228v4 PDF p.5; arxiv-2206.13228v4 PDF p.9. -/
def preparationDepth {n : ℕ} (C : LayeredPreparationCircuit n) : ℕ := C.layers.length

/-- arxiv-2206.13228v4 PDF p.5; arxiv-2206.13228v4 PDF p.8; arxiv-2206.13228v4 PDF p.9. -/
def preparationOutputDensity {n : ℕ} (C : LayeredPreparationCircuit n) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  traceRight ((pureDensity (act (Circuit.unitary C.layers.flatten) (zeroKet (n+C.ancillas)))).submatrix
    (qubitsAppendEquiv n C.ancillas).symm (qubitsAppendEquiv n C.ancillas).symm)

/-- Sanity check for the source model (arxiv-2206.13228v4 PDF p.5). -/
example (n : ℕ) : preparationDepth (⟨0,[],by simp⟩ : LayeredPreparationCircuit n) = 0 := rfl

end QAlgorithms.NLTS


