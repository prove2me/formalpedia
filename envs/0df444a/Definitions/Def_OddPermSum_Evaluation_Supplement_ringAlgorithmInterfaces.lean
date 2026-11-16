-- Prove2me | Definitions.Def_OddPermSum_Evaluation_Supplement_ringAlgorithmInterfaces
-- name    : OddPermSum_Evaluation_Supplement_ringAlgorithmInterfaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:39:11.174242+00:00
-- url     : https://prove2.me/theorems/dcfa85c2-c6a1-4320-8d6c-b04b49f65657
-- title:
--   Field-operation execution and truncated-ring input/output interfaces
-- statement:
--   Truncated-ring computation is expressed using the published finite algebraic programs over the coefficient field $F$. Integer control cannot read a field value except through a charged zero test; field operations and tests contribute to the actual interpreter cost. The dimension $s$ and index registers initially containing $L$ and $i$ provide integer parameters. Input/output lists contain only the specified coefficient encodings.
--
--   The four-output interface encodes $A^{-1}$, $\det A$, $\Phi(A)$ and the full transposed gradient. The row-update interface receives $A,B,\Delta,\Phi(A),\rho$ and returns the queried gradient column, updated value and determinant, and the updated inverse when $\eta$ is a unit. This treats the stored quantities as input rather than recomputing them for free.
--
--   Execution, its charged cost and the mathematical output specification are independent definitions.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 14–15, Lemma 5.3; 20–21, Lemma 6.3

import Definitions.Def_OddPermSum_Evaluation_Supplement_truncatedRing
import Definitions.Def_OddPermSum_Evaluation_Supplement_rowUpdate
import Definitions.Def_OddPermSum_Evaluation_gradient
import Definitions.Def_OddPermSum_Evaluation_machineExecution

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

noncomputable def allRingOutputs {F : Type*} [Field F] {s L : ℕ}
    (A : Matrix (Fin s) (Fin s) (Trunc F L)) : List F :=
  truncMatrixEncoding A⁻¹ ++ truncEncoding A.det ++ truncEncoding (phi A) ++
    truncMatrixEncoding (gradient A)

noncomputable def updateInputs {F : Type*} [Field F] {s L : ℕ}
    (A B : Matrix (Fin s) (Fin s) (Trunc F L)) (δ φA : Trunc F L)
    (ρ : Fin s → Trunc F L) : List F :=
  truncMatrixEncoding A ++ truncMatrixEncoding B ++
    truncEncoding δ ++ truncEncoding φA ++ (List.ofFn ρ).flatMap truncEncoding

/-- i, L and s are integer parameters placed in index memory; never converted out of field data. -/
noncomputable def runParameters {F : Type*} [Field F] (p : AlgebraicProgram F)
    (s L i : ℕ) (inputs : List F) (fuel : ℕ) : Option (MachineState F) := by
  classical
  exact execute s inputs fuel p {
    indices := fun a => if a = 0 then L else if a = 1 then i else 0
    registers := fun _ => 0
    outputs := []
    arithmetic := 0
    tests := 0 }

noncomputable def updateOutputs {F : Type*} [Field F] {s L : ℕ}
    (A : Matrix (Fin s) (Fin s) (Trunc F L)) (i : Fin s) (ρ : Fin s → Trunc F L) : List F := by
  classical
  let A' := rowUpdate A i ρ
  exact (List.ofFn (fun j => gradient A j i)).flatMap truncEncoding ++
    truncEncoding (phi A') ++ truncEncoding A'.det ++
    if IsUnit (updateEta A⁻¹ i ρ) then truncMatrixEncoding A'⁻¹ else []

end OddPermSum.Evaluation.Supplement


