-- Prove2me | Definitions.Def_QAlgorithms_Defs_SurgerySequentialProtocols
-- name    : QAlgorithms_Defs_SurgerySequentialProtocols
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:33:48.836566+00:00
-- url     : https://prove2.me/theorems/ff91b5af-1975-4823-a6ce-8bdfe22a5490
-- title:
--   SurgerySequentialProtocols
-- statement:
--   SurgerySequentialProtocols
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SurgerySequentialProtocols.lean

import Definitions.Def_QAlgorithms_Defs_SurgeryPhenomenologicalExecution
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Surgery

/-- Public surgery segment on a fixed register, with explicit preparation/readout/check
layers; fresh ancillas may all be prepared initially because unused wires are idle.
The separating physical merge/readout steps retain their non-round markers
(2510.14895 pp.23,32,60,71,82). -/
structure SurgerySegment (q : ℕ) where
  layers : List (MeasurementLayer q)

/-- Embed an X or Z row of the actual deformed presentation on its public wire
placement; unused wires carry identity (2510.14895 pp.12--13,32). -/
def placedCheck {I : Type*} [Fintype I] {q : ℕ} (w : I ↪ Fin q)
    (x : Bool) (row : I → ZMod 2) : Fin q → Stabilizer.Pauli :=
  fun wire => if ∃ i, w i = wire ∧ row i ≠ 0 then
    (if x then Stabilizer.Pauli.X else Stabilizer.Pauli.Z) else Stabilizer.Pauli.I

/-- Construct the actual hypergraph-surgery checks from the mapping cone, repeat them
for the supplied syndrome rounds, and measure every shifted degree-zero auxiliary
wire in X. Merge/preparation and split/readout are explicit non-round physical layers.
The public embedding retains the original memory and fresh auxiliary labels
(2510.14895 pp.12--13,19,23,32,71,82). -/
def hypergraphSegment {A C : BasedBinaryComplex} (h : BasedChainMap A C)
    (q rounds : ℕ) (w : Basis (mappingCone h) 1 ↪ Fin q) : SurgerySegment q := by
  classical
  let D := mappingCone h
  let xchecks := (Finset.univ.toList : List (Basis D 0)).map fun r =>
    placedCheck w true (boundary D 1 r)
  let zchecks := (Finset.univ.toList : List (Basis D 2)).map fun r =>
    placedCheck w false (fun c => boundary D 2 c r)
  let readout := (Finset.univ.toList : List (Basis A 0)).map fun a =>
    let wire := w ⟨Sum.inr a.val,by dsimp [D,mappingCone]; rw [a.property]; norm_num⟩
    (fun k => if k = wire then Stabilizer.Pauli.X else Stabilizer.Pauli.I)
  exact ⟨[⟨[],false,none,Finset.univ.map w⟩] ++ List.replicate rounds ⟨xchecks++zchecks,true,none,Finset.univ.map w⟩ ++ [⟨readout,false,none,Finset.univ.map w⟩]⟩

/-- Sequential concatenation with d original-memory syndrome rounds before and after.
The data include the actual measured Pauli lists and final parity frame, and are chosen
before the hidden encoded input or any faults (2510.14895 pp.23,32,60,71,82).
arxiv-2510.14895v1 PDF p.23; arxiv-2510.14895v1 PDF p.32; arxiv-2510.14895v1 PDF p.60; arxiv-2510.14895v1 PDF p.71; arxiv-2510.14895v1 PDF p.82. -/
def paddedSequentialProtocol (n a d : ℕ) (memoryChecks : List (Fin (n+a) → Stabilizer.Pauli))
    (segments : List (SurgerySegment (n+a)))
    (frame : List Bool → List Bool) : PhenomenologicalSchedule n :=
  ⟨a,List.replicate d ⟨memoryChecks,true,none,
    Finset.univ.map ⟨Fin.castAdd a,Fin.castAdd_injective _ _⟩⟩ ++
    segments.zipIdx.flatMap (fun indexed => indexed.1.layers.map
      (fun layer => {layer with origin := some indexed.2})) ++ List.replicate d ⟨memoryChecks,true,none,
    Finset.univ.map ⟨Fin.castAdd a,Fin.castAdd_injective _ _⟩⟩,frame⟩

/-- Actual number of syndrome-round markers. Preparation and split/readout steps do
not count as syndrome rounds (2510.14895 pp.23,32,60,71,82).
arxiv-2510.14895v1 PDF p.23; arxiv-2510.14895v1 PDF p.32; arxiv-2510.14895v1 PDF p.60; arxiv-2510.14895v1 PDF p.71; arxiv-2510.14895v1 PDF p.82. -/
def syndromeRoundCounts {n : ℕ} (S : PhenomenologicalSchedule n) : ℕ × (ℕ → ℕ) :=
  (S.layers.countP MeasurementLayer.syndrome,fun j =>
    S.layers.countP fun layer => layer.syndrome && decide (layer.origin = some j))

/-- Sanity check for the source model (arxiv-2510.14895v1 PDF p.23). -/
example (n a d : ℕ) (checks : List (Fin (n+a) → Stabilizer.Pauli))
    (frame : List Bool → List Bool) :
    (syndromeRoundCounts (paddedSequentialProtocol n a d checks [] frame)).1 = 2*d := by
  simp [syndromeRoundCounts,paddedSequentialProtocol,List.countP_replicate]
  omega

end QAlgorithms.Surgery


