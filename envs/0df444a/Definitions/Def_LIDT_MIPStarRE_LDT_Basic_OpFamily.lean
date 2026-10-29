-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
-- name    : LIDT_MIPStarRE_LDT_Basic_OpFamily
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:55:20.431605+00:00
-- url     : https://prove2.me/theorems/171af541-6ab4-4f61-b66b-088840bd4fc2
-- title:
--   LIDT definitions: LDT / Basic / OpFamily
-- statement:
--   This bundle introduces operator families without positivity, projectivity, or boundedness assumptions. These raw families are the ambient objects for state-dependent operator-distance chains, tensor placement, and outcome postprocessing.
--
--   Principal definitions:
--   - `OpFamily`: Stores an operator for each outcome and a separate total operator on a finite Hilbert space.
--   - `IdxOpFamily`: A question-indexed family of raw operator families.
--   - `toOpFamily`: Forgets the submeasurement structure and retains only its outcome operators and total operator.
--   - `toIdxOpFamily`: Applies that forgetful operation pointwise to an indexed submeasurement family.
--   - `leftPlacedOpFamily`: Places every raw operator on the left tensor factor as $A\otimes I$, including the total operator.
--   - `rightPlacedOpFamily`: Places every raw operator on the right tensor factor as $I\otimes B$.
--   - `postprocess`: Relabels outcomes by summing all old outcome operators with the same new label while retaining the original total operator.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/OpFamily.lean#L30-L95

-- Generated from MIPStarRE/LDT/Basic/OpFamily.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

/-!
# Raw operator families for the low individual degree test

This file introduces the notion of an indexed family of operators used in the paper
without positivity or boundedness requirements. These are used for `≈_δ`
chains whose intermediate objects are arbitrary matrix families rather than
honest submeasurements.

## References

- `references/ldt-paper/self_improvement.tex`
- `references/ldt-paper/commutativity-points.tex`
- `references/ldt-paper/commutativity-G.tex`
- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- A raw operator family: outcome operators indexed by `α`, without PSD or bound
requirements. This matches the paper's use of arbitrary matrix families in
`≈_δ` chains. -/
structure OpFamily (α : Type*) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  outcome : α → MIPStarRE.Quantum.Op ι
  total : MIPStarRE.Quantum.Op ι

/-- Indexed raw operator family (question → outcome → operator). -/
def IdxOpFamily (Question Outcome : Type*) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  Question → OpFamily Outcome ι

namespace SubMeas

/-- Forget the PSD and boundedness structure of a submeasurement. -/
def toOpFamily {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : OpFamily α ι where
  outcome := A.outcome
  total := A.total

end SubMeas

instance {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] :
    Coe (SubMeas α ι) (OpFamily α ι) where
  coe := SubMeas.toOpFamily

namespace IdxSubMeas

/-- Forget the PSD and boundedness structure of an indexed submeasurement family. -/
def toIdxOpFamily {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) :
    IdxOpFamily Question Outcome ι :=
  fun q => (A q).toOpFamily

end IdxSubMeas

namespace OpFamily

/-- Place a raw operator family on the left tensor factor of `ιA × ιB`. -/
def leftPlacedOpFamily {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : OpFamily α ιA) :
    OpFamily α (ιA × ιB) where
  outcome := fun a => leftTensor (ι₂ := ιB) (A.outcome a)
  total := leftTensor (ι₂ := ιB) A.total

/-- Place a raw operator family on the right tensor factor of `ιA × ιB`. -/
def rightPlacedOpFamily {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : OpFamily α ιB) :
    OpFamily α (ιA × ιB) where
  outcome := fun a => rightTensor (ι₁ := ιA) (A.outcome a)
  total := rightTensor (ι₁ := ιA) A.total

/-- Post-process the outcomes of a raw operator family. -/
noncomputable def postprocess {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (A : OpFamily α ι) (f : α → β) :
    OpFamily β ι :=
  open Classical in
    { outcome := fun b =>
        ∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a
      total := A.total }

end OpFamily

namespace IdxOpFamily



end IdxOpFamily

end MIPStarRE.LDT

end

end LIDT


