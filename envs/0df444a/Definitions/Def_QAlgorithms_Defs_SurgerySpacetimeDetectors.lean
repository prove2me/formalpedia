-- Prove2me | Definitions.Def_QAlgorithms_Defs_SurgerySpacetimeDetectors
-- name    : QAlgorithms_Defs_SurgerySpacetimeDetectors
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:36:11.71534+00:00
-- url     : https://prove2.me/theorems/2cc03808-e9fc-4ee5-b6cc-000abdfdf8c5
-- title:
--   SurgerySpacetimeDetectors
-- statement:
--   SurgerySpacetimeDetectors
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SurgerySpacetimeDetectors.lean

import Definitions.Def_QAlgorithms_Defs_SurgerySequentialProtocols
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Surgery

/-- Original-memory stabilizers read ideally at the outgoing temporal boundary.
These certify the residual syndrome, relative to the noiseless reported-record frame;
they are boundary detector data, not additional noisy syndrome rounds
(2510.14895 pp.60--65,69,76). -/
def boundaryChecks {n mx mz : ℕ} (C : PresentedCSS.CheckPresentation n mx mz) :
    List (Fin n → Stabilizer.Pauli) :=
  (List.ofFn fun r : Fin mx => fun j => if C.HX r j = 0 then Stabilizer.Pauli.I else Stabilizer.Pauli.X) ++
    (List.ofFn fun r : Fin mz => fun j => if C.HZ r j = 0 then Stabilizer.Pauli.I else Stabilizer.Pauli.Z)

/-- Binary parity rows on the noisy record together with ideal outgoing syndrome bits
(2510.14895 pp.60--65,69,76). -/
abbrev RecordParity {n mx mz : ℕ} (S : PhenomenologicalSchedule n)
    (_C : PresentedCSS.CheckPresentation n mx mz) :=
  Fin ((S.layers.flatMap MeasurementLayer.checks).length+mx+mz) → ZMod 2

/-- Parity of a recorded measurement string; source locations include the final
ancilla X readout and original-memory boundary checks (2510.14895 pp.60,72,76). -/
def recordParity {n mx mz : ℕ} (S : PhenomenologicalSchedule n)
    (C : PresentedCSS.CheckPresentation n mx mz) (p : RecordParity S C) (r : List Bool) : ZMod 2 :=
  ∑ j, if r.getD j.val false then p j else 0

/-- Exact branch operator for one reported record, aggregated over unreported physical
outcomes, from the schedule interpreter followed by ideal outgoing syndrome readout
(2510.14895 pp.60--65,69,76). -/
def recordOperator {n mx mz : ℕ} (S : PhenomenologicalSchedule n)
    (C : PresentedCSS.CheckPresentation n mx mz) (fault : ScheduleFault n S)
    (record : List Bool) (rho : Matrix (Qubits n) (Qubits n) ℂ) :=
  (((executeSchedule S fault rho).flatMap fun branch =>
    measureChecks (fun _ => false) (boundaryChecks C) 0 branch.1 branch.2).filter
      fun branch => branch.1 = record).map Prod.snd |>.sum

/-- The encoded input projector is computed from every row of the actual CSS
presentation; dependent and zero rows are retained (2510.14895 pp.10--11,60). -/
def codeProjector {n mx mz : ℕ} (C : PresentedCSS.CheckPresentation n mx mz) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  ((List.ofFn fun r : Fin mx => (2⁻¹ : ℂ) • (1+NLTS.rowOperator true (C.HX r))) ++
    (List.ofFn fun r : Fin mz => (2⁻¹ : ℂ) • (1+NLTS.rowOperator false (C.HZ r)))).prod

/-- Detector parities are computed from the noiseless schedule on its specified encoded
input projector. All constant-zero record relations are retained, including consecutive
checks, metachecks, cycles and boundary/frame relations, including the final residual
syndrome from ideal boundary readout; redundant rows are allowed.
No detector matrix is supplied independently (2510.14895 pp.13,23,60,72,76).
arxiv-2510.14895v1 PDF p.13; arxiv-2510.14895v1 PDF p.23; arxiv-2510.14895v1 PDF p.60; arxiv-2510.14895v1 PDF p.72; arxiv-2510.14895v1 PDF p.76. -/
def detectorMap {n mx mz : ℕ} (S : PhenomenologicalSchedule n)
    (C : PresentedCSS.CheckPresentation n mx mz) (record : List Bool) : RecordParity S C → ZMod 2 :=
  fun p => if ∀ r : List Bool, r.length = (S.layers.flatMap MeasurementLayer.checks).length+mx+mz →
    recordParity S C p r ≠ 0 → recordOperator S C (noFault S) r (codeProjector C) = 0
    then recordParity S C p record else 0

/-- Operational spacetime-stabilizer equivalence: faults induce identical reported
record maps on the encoded memory algebra. Pauli/projector/frame relations are evaluated
rather than free equivalence matrices being supplied (2510.14895 pp.13,23,60,72,76).
arxiv-2510.14895v1 PDF p.13; arxiv-2510.14895v1 PDF p.23; arxiv-2510.14895v1 PDF p.60; arxiv-2510.14895v1 PDF p.72; arxiv-2510.14895v1 PDF p.76. -/
def spacetimeStabilizers {n mx mz : ℕ} (S : PhenomenologicalSchedule n)
    (C : PresentedCSS.CheckPresentation n mx mz) : Setoid (ScheduleFault n S) where
  r e f := ∀ record rho,
    recordOperator S C e record (codeProjector C*rho*codeProjector C) =
      recordOperator S C f record (codeProjector C*rho*codeProjector C)
  iseqv := ⟨fun _ _ _ => rfl,fun h r x => (h r x).symm,
    fun h1 h2 r x => (h1 r x).trans (h2 r x)⟩

/-- Sanity check for the source model (arxiv-2510.14895v1 PDF p.13). -/
example {n mx mz : ℕ} (S : PhenomenologicalSchedule n) (C : PresentedCSS.CheckPresentation n mx mz)
    (e : ScheduleFault n S) : (spacetimeStabilizers S C).r e e := fun _ _ => rfl

/-- Every original X and Z row supplies an outgoing boundary syndrome bit, including
redundant rows (2510.14895 pp.64--65). -/
example {n mx mz : ℕ} (C : PresentedCSS.CheckPresentation n mx mz) :
    (boundaryChecks C).length = mx+mz := by
  simp [boundaryChecks]

end QAlgorithms.Surgery


