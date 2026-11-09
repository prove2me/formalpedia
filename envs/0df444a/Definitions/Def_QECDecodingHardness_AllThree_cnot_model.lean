-- Prove2me | Definitions.Def_QECDecodingHardness_AllThree_cnot_model
-- name    : QECDecodingHardness_AllThree_cnot_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:44.884553+00:00
-- url     : https://prove2.me/theorems/b5db4176-d4a5-449e-8b6c-b759a6ad00b0
-- title:
--   tCNOTZ with ideal end measurements and the CNOT detector hyperedges
-- statement:
--   Two identical square patches of size L have measurement rounds j=0,...,2L-1 at time j-1/2. The transversal CNOT acts from patch 1 to patch 2 at t_G=L-1, after the first L rounds. Data Z faults are at integer times 0,...,2L-2, after the gate when t=t_G. Measurement faults occur only at internal rounds 1,...,2L-2; the first and last measurements are ideal.
--
--   Away from the gate, a measurement fault triggers the two same-patch adjacent detectors. The extra incidence at the gate is
--
--   $$ (2,v,t_G-\tfrac12)\longleftrightarrow\{(2,v,t_G-1),(2,v,t_G),(1,v,t_G)\}.$$
--
--   A data fault triggers incident vertex checks on its own patch at its own time. Locations are the disjoint union of data and internal measurement faults, and weight counts them once each. Only one binary fault coordinate is allowed at a location.
--
--   This model preserves the coupled three-ended measurement edge and the full growing time direction. At L=1 there are two ideal measurement rounds, one data layer at the gate, and no internal measurement faults.
-- source:
--   Shouzhen (Bailey) Gu, Lily Wang, Aleksander Kubica, STOC 2027 submission #745 (October 2026), pp.4–5, Section II.3, boxed tCNOTZ problem and detector convention

import Definitions.Def_QECDecodingHardness_AllThree_lattice_coordinates

namespace QECDecodingHardness.AllThree

/-- `false` is patch 1/control; `true` is patch 2/target. A data fault carries
an edge and integer time; a measurement fault a vertex and measurement round j,
whose physical time is j-1/2. Ideal rounds j=0 and j=2L-1 are absent as faults. -/
abbrev CNOTFault := (Bool × SquareEdge × ℕ) ⊕ (Bool × SquareVertex × ℕ)
abbrev CNOTDetector := Bool × SquareVertex × ℕ

def cnotFaults (L : ℕ) : List CNOTFault :=
  ([false, true] : List Bool).flatMap (fun a =>
    ((surfaceQubits L).flatMap (fun e =>
      (List.range (2 * L - 1)).map (fun t => Sum.inl (a, e, t)))) ++
    ((surfaceXChecks L).flatMap (fun v =>
      (List.range (2 * L - 2)).map (fun j => Sum.inr (a, v, j + 1)))))

def cnotDetectors (L : ℕ) : List CNOTDetector :=
  ([false, true] : List Bool).flatMap (fun a =>
    (surfaceXChecks L).flatMap (fun v =>
      (List.range (2 * L - 1)).map (fun t => (a, v, t))))

/-- Section II.3, p.4. Data errors are after the gate. Ordinary measurement
faults trigger two time neighbors. At j=L-1, a target measurement fault also
triggers the control detector at t_G=L-1, giving the required three-ended edge. -/
def cnotIncident (L : ℕ) (d : CNOTDetector) (f : CNOTFault) : Prop :=
  match f with
  | .inl (a, e, t) => d.1 = a ∧ d.2.2 = t ∧ edgeAtVertex d.2.1 e
  | .inr (a, v, j) =>
      (d.1 = a ∧ d.2.1 = v ∧ (d.2.2 + 1 = j ∨ d.2.2 = j)) ∨
      (a = true ∧ d.1 = false ∧ j = L - 1 ∧ d.2.1 = v ∧ d.2.2 = L - 1)

instance (L : ℕ) (d : CNOTDetector) (f : CNOTFault) : Decidable (cnotIncident L d f) := by
  unfold cnotIncident
  split <;> infer_instance

/-- Exactly 2L measurement rounds, gate after the first L, ideal time ends.
The family used below has L≥1. At L=1: t_i=t_G=t_f=0; two ideal rounds,
one data layer, and no internal measurement fault. No periodic time. -/
def transversalCNOTZ (L : ℕ) : CheckSystem :=
  systemOfLists (cnotFaults L) (cnotDetectors L) false (fun _ _ => 0)
    (fun d f => if cnotIncident L d f then 1 else 0)

end QECDecodingHardness.AllThree


