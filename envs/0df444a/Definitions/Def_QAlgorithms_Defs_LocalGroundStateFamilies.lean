-- Prove2me | Definitions.Def_QAlgorithms_Defs_LocalGroundStateFamilies
-- name    : QAlgorithms_Defs_LocalGroundStateFamilies
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:02:15.882598+00:00
-- url     : https://prove2.me/theorems/99874f61-f9ec-45b0-9d27-5e1ba567d148
-- title:
--   LocalGroundStateFamilies
-- statement:
--   LocalGroundStateFamilies
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\LocalGroundStateFamilies.lean

import Definitions.Def_QAlgorithms_Defs_SpectralFilter
import Definitions.Def_QAlgorithms_Defs_Channel
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix.Norms.L2Operator

namespace QAlgorithms.GroundStateLearning

/-- Parameter domain of the source: the length-two cube, without identifying its faces
(2106.12627 pp.29-30, Eqs.(F1)-(F4)). -/
def parameterCube (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) := {x | ∀ j, |x j| ≤ 1}

/-- Finite-site geometric locality with explicit constants uniform over the system size;
the count bounds are the geometric input, not a dynamical conclusion
(2106.12627 pp.36-37, assumptions (a)-(b), Eq.(F53)). -/
structure SpatialGeometry (n terms spatial : ℕ) where
  spatial_pos : 0 < spatial
  site : Fin n → EuclideanSpace ℝ (Fin spatial)
  support : Fin terms → Finset (Fin n)
  cardinalityBound : ℕ
  radiusBound : ℝ
  radius_nonnegative : 0 ≤ radiusBound
  cardinality : ∀ j, (support j).card ≤ cardinalityBound
  centers : Fin terms → EuclideanSpace ℝ (Fin spatial)
  radiusLocal : ∀ j q, q ∈ support j → dist (site q) (centers j) ≤ radiusBound
  bd : ℝ
  cd : ℝ
  bd_nonnegative : 0 ≤ bd
  cd_nonnegative : 0 ≤ cd
  counts : ∀ q r, 0 ≤ r →
    ((Finset.univ.filter fun j => ∃ v ∈ support j, dist (site q) (site v) ≤ r).card : ℝ) ≤
      bd+cd*r^spatial

/-- Smooth bounded local terms and bounded unit-direction derivatives
(2106.12627 p.36, assumption (b)). No ground-state gradient bound is assumed. -/
structure HamiltonianFamily (n m terms spatial : ℕ) where
  geometry : SpatialGeometry n terms spatial
  term : Fin terms → EuclideanSpace ℝ (Fin m) → Matrix (Qubits n) (Qubits n) ℂ
  hermitian : ∀ j x, x ∈ parameterCube m → (term j x).IsHermitian
  supported : ∀ j x, x ∈ parameterCube m → ActsWithin (geometry.support j) (term j x)
  smooth : ∀ j, ContDiffOn ℝ ⊤ (term j) (parameterCube m)
  bounded : ∀ j x, x ∈ parameterCube m → specNorm (term j x) ≤ 1
  derivativeBound : ∀ j x, x ∈ parameterCube m → ∀ u : EuclideanSpace ℝ (Fin m),
    ‖u‖ = 1 → specNorm (fderivWithin ℝ (term j) (parameterCube m) x u) ≤ 1

/-- The Hamiltonian is computed from its local terms (2106.12627 p.36, assumption (b)). -/
def HamiltonianFamily.hamiltonian {n m terms spatial : ℕ}
    (H : HamiltonianFamily n m terms spatial) (x : EuclideanSpace ℝ (Fin m)) :
    Matrix (Qubits n) (Qubits n) ℂ := ∑ j, H.term j x

/-- A positive gap to a next distinct energy, allowing degeneracy of the ground space
(2106.12627 p.29, Theorem 3 and p.36, assumption (c)). -/
def HasExcitationGap {n : ℕ} (H : Matrix (Qubits n) (Qubits n) ℂ) (gamma : ℝ) : Prop :=
  H.IsHermitian ∧ 0 < gamma ∧
    (∃ k, minEigenvalue H < ascEigenvalues H k) ∧
    ∀ k, minEigenvalue H < ascEigenvalues H k → gamma ≤ ascEigenvalues H k-minEigenvalue H

/-- Uniform density on the minimum eigenspace; on the nonempty qubit space the Hermitian
ground projector has positive trace (2106.12627 p.29, Eq.(F1); p.36, assumption (c)). -/
def groundDensity {n : ℕ} (H : Matrix (Qubits n) (Qubits n) ℂ) (_hermitian : H.IsHermitian) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  let P := spectralProjector H (minEigenvalue H)
  P.trace⁻¹ • P

/-- Few-body observables need bounded support cardinality, not geometric locality
(2106.12627 p.29, Theorem 3; p.36, assumption (d)). -/
structure FewBodyObservable (n q L : ℕ) (B : ℝ) where
  terms : Fin L → Matrix (Qubits n) (Qubits n) ℂ
  support : Fin L → Finset (Fin n)
  cardinality : ∀ j, (support j).card ≤ q
  supported : ∀ j, ActsWithin (support j) (terms j)
  hermitian : ∀ j, (terms j).IsHermitian
  bounded : ∑ j, specNorm (terms j) ≤ B

example (m : ℕ) : (0 : EuclideanSpace ℝ (Fin m)) ∈ parameterCube m := by
  simp [parameterCube]

example {n : ℕ} (H : Matrix (Qubits n) (Qubits n) ℂ) : ¬ HasExcitationGap H 0 := by
  simp [HasExcitationGap]

end QAlgorithms.GroundStateLearning


