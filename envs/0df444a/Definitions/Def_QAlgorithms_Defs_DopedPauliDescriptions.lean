-- Prove2me | Definitions.Def_QAlgorithms_Defs_DopedPauliDescriptions
-- name    : QAlgorithms_Defs_DopedPauliDescriptions
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T04:11:27.10678+00:00
-- url     : https://prove2.me/theorems/cca06d9b-792f-48a6-b3c6-a99ca196630f
-- title:
--   prove2quantum library: Defs.DopedPauliDescriptions
-- statement:
--   Shared definitions of the prove2quantum Lean library (`QAlgorithms.Defs.DopedPauliDescriptions`), reused by its paper formalizations.
--
--   - `CoefficientCode`: Exact algebraic coefficient codes a+b sqrt(2), with rational a,b (2305.15398 p.3, Eq.(5); pp.11-13, Appendix C.4).
--   - `CoefficientCode.value`: Interpretation of the exact finite coefficient code (2305.15398 p.3, Eq.(5)).
--   - `Description`: A raw finite report, without any true-state correctness fields (2305.15398 p.3, Eq.(3)). Identity bad-generator and coefficient one are implicit.
--   - `reconstruct`: Eq.(3) reconstruction, with true sign flag = +1 and declared list product order. The result is not forcibly projected to density matrices (2305.15398 p.3).
--   - `generatedLabels`: Closure under phase-free multiplication of reported generators (2305.15398 p.4, generator extraction).
--   - `exactDescriptionEvent`: Exact algebraic report success: density, full unsigned group, eigenvalue signs, distinct nonidentity cosets covering support, and exact coefficients (2305.15398 pp.2-4, Eqs.(2)-(3)).
-- source:
--   prove2quantum Lean library, module QAlgorithms.Defs.DopedPauliDescriptions

import Definitions.Def_QAlgorithms_Defs_DopedStabilizerData

noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.DopedTomography

/-- Exact algebraic coefficient codes a+b sqrt(2), with rational a,b
(2305.15398 p.3, Eq.(5); pp.11-13, Appendix C.4). -/
structure CoefficientCode where
  rational : ℚ
  radical : ℚ
  deriving DecidableEq

/-- Interpretation of the exact finite coefficient code (2305.15398 p.3, Eq.(5)). -/
def CoefficientCode.value (a : CoefficientCode) : ℝ := a.rational+a.radical*Real.sqrt 2

/-- A raw finite report, without any true-state correctness fields
(2305.15398 p.3, Eq.(3)). Identity bad-generator and coefficient one are implicit. -/
structure Description (n : ℕ) where
  generators : List ((Fin n → Stabilizer.Pauli) × Bool)
  badGenerators : List ((Fin n → Stabilizer.Pauli) × CoefficientCode)

/-- Eq.(3) reconstruction, with true sign flag = +1 and declared list product order.
The result is not forcibly projected to density matrices (2305.15398 p.3). -/
def reconstruct {n : ℕ} (D : Description n) : Matrix (Qubits n) (Qubits n) ℂ :=
  ((2 : ℂ)^n)⁻¹ •
    ((1+(D.badGenerators.map fun h => (h.2.value : ℂ) • pauliOps h.1).sum)*
      (D.generators.map fun g => 1+(if g.2 then (1 : ℂ) else -1) • pauliOps g.1).prod)

/-- Closure under phase-free multiplication of reported generators
(2305.15398 p.4, generator extraction). -/
def generatedLabels {n : ℕ} (generators : List (Fin n → Stabilizer.Pauli)) :
    Set (Fin n → Stabilizer.Pauli) :=
  {P | ∃ subset : Finset (Fin generators.length),
    P = (List.ofFn fun j : Fin generators.length =>
      if j ∈ subset then generators.get j else fun _ => Stabilizer.Pauli.I).foldl
        Clifford.phaseFreeProduct (fun _ => Stabilizer.Pauli.I)}

/-- Exact algebraic report success: density, full unsigned group, eigenvalue signs,
distinct nonidentity cosets covering support, and exact coefficients
(2305.15398 pp.2-4, Eqs.(2)-(3)). -/
def exactDescriptionEvent {n : ℕ} (psi : EuclideanSpace ℂ (Qubits n)) (state : IsState psi)
    (D : Description n) : Prop :=
  reconstruct D = pureDensity psi ∧
    generatedLabels (D.generators.map Prod.fst) = (unsignedStabilizer psi state : Set _) ∧
    (∀ g ∈ D.generators, act (pauliOps g.1) psi = (if g.2 then (1 : ℂ) else -1) • psi) ∧
    ((D.badGenerators.map fun h => labelCoset (unsignedStabilizer psi state) h.1).Nodup) ∧
    (D.badGenerators.map fun h => labelCoset (unsignedStabilizer psi state) h.1).toFinset =
      badCosets psi state ∧
    ∀ h ∈ D.badGenerators, h.2.value = (pauliOps h.1*pureDensity psi).trace.re

example : CoefficientCode.value ⟨1,0⟩ = 1 := by simp [CoefficientCode.value]

example : reconstruct (⟨[],[]⟩ : Description 0) = 1 := by simp [reconstruct]

example : reconstruct (⟨[⟨fun _ => Stabilizer.Pauli.Z,true⟩],[]⟩ : Description 1) =
    (2⁻¹ : ℂ) • (1+pauliOps (fun _ => Stabilizer.Pauli.Z)) := by
  simp [reconstruct]

end QAlgorithms.DopedTomography


