-- Prove2me | Definitions.Def_QAlgorithms_Defs_SurgeryLogicalMeasurements
-- name    : QAlgorithms_Defs_SurgeryLogicalMeasurements
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:30:24.733445+00:00
-- url     : https://prove2.me/theorems/674afce0-ee5c-4806-ada3-1f37b05ef540
-- title:
--   SurgeryLogicalMeasurements
-- statement:
--   SurgeryLogicalMeasurements
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SurgeryLogicalMeasurements.lean

import Definitions.Def_QAlgorithms_Defs_SurgeryMappingCones
import Definitions.Def_QAlgorithms_Defs_NLTSCodeGeometry
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Surgery

/-- Image of auxiliary cycles in the memory homology quotient, computed from the
attaching matrix; boundaries are quotiented out (2510.14895 pp.13,27,32,61).
arxiv-2510.14895v1 PDF p.13; arxiv-2510.14895v1 PDF p.27; arxiv-2510.14895v1 PDF p.32; arxiv-2510.14895v1 PDF p.61. -/
def measuredLogicalSubspace {A C : BasedBinaryComplex} (h : BasedChainMap A C) :
    Submodule (ZMod 2) (Homology C 1) :=
  ((LinearMap.range ((component h 1).mulVecLin.comp (cycles A 1).subtype)).comap
    (cycles C 1).subtype).map (boundaries C 1).mkQ

/-- Positive-phase Z representative of a binary vector in a specified qubit basis
(2510.14895 pp.10--13). -/
def zRepresentative {I : Type*} [Fintype I] (u : I → ZMod 2) : Matrix (I → Bool) (I → Bool) ℂ :=
  Matrix.diagonal fun z => (-1 : ℂ) ^ (∑ i, if z i then u i else 0).val

/-- Projective instrument measuring every auxiliary cycle's actual image. Dependent
cycles have dependent outcomes through the product of their commuting projectors;
no independent-logical-request assumption is imposed (2510.14895 pp.13,27,32,61).
The returned matrix is the branch Kraus operator on the retained memory register.
arxiv-2510.14895v1 PDF p.13; arxiv-2510.14895v1 PDF p.27; arxiv-2510.14895v1 PDF p.32; arxiv-2510.14895v1 PDF p.61. -/
def idealLogicalInstrument {A C : BasedBinaryComplex} (h : BasedChainMap A C)
    (outcome : cycles A 1 → Bool) :
    Matrix (Basis C 1 → Bool) (Basis C 1 → Bool) ℂ :=
  (List.ofFn fun i : Fin (Fintype.card (cycles A 1)) =>
    let v := (Fintype.equivFin (cycles A 1)).symm i
    (2⁻¹ : ℂ) • (1+(if outcome v then (-1 : ℂ) else 1) •
      zRepresentative ((component h 1).mulVec v.val))).prod

/-- Sanity check for the source model (arxiv-2510.14895v1 PDF p.13). -/
example {I : Type*} [Fintype I] : zRepresentative (0 : I → ZMod 2) = 1 := by
  ext x y; simp [zRepresentative,Matrix.one_apply]

end QAlgorithms.Surgery


