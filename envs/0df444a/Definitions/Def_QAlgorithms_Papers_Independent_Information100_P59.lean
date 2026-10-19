-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59
-- name    : QAlgorithms_Papers_Independent_Information100_P59
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T12:24:11.778506+00:00
-- url     : https://prove2.me/theorems/32c52707-da77-4b12-8e6f-bc0c30c2175d
-- title:
--   Definitions for Lie-Wedge Stratification and Pure-State Stabilizability in Single- Channel Qubit Control
-- statement:
--   The objects the formalized statements of *Lie-Wedge Stratification and Pure-State Stabilizability in Single- Channel Qubit Control* (arXiv:2610.00046) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Vec`: PDF p.9: real Bloch-coordinate vectors, in the pinned X,Y,Z order.
--   - `Cvec`: PDF p.9: complex coefficients of a traceless qubit jump.
--   - `Mat`: PDF p.9: real linear maps on Bloch coordinates.
--   - `Block`: PDF pp.9,11: homogeneous-coordinate matrices; generators have zero last row.
--   - `Qmat`: PDF p.9: complex qubit operators, using the accepted Boolean basis.
--   - `jump`: PDF p.9: L=a·sigma in the pinned X,Y,Z order.
--   - `blochState`: PDF p.9: rho(v)=(I+v·sigma)/2; defined also off the Bloch ball.
--   - `dissipator`: PDF pp.9,11: the actual operator dissipator, not its claimed affine formula.
--   - `coherent`: PDF pp.4,9: the Hamiltonian superoperator, with the source's minus-i sign.
--   - `gaugeHamiltonian`: PDF p.11: the Hamiltonian added to the dissipator by L ↦ L+cI. Its negative is the compensating change of the autonomous Hamiltonian.
--   - `amplitudeSq`: PDF p.11: squared coefficient norm |a|², independent of any matrix norm.
--   - `channelMoment`: PDF p.12: M=alpha alpha^T+beta beta^T.
--   - `channelQ`: PDF p.11, (19): candidate linear Bloch coefficient.
--   - `channelB`: PDF p.11, (19): candidate affine translation, in the right-handed convention.
--   - `rotationGenerator`: PDF p.9: J_n v=n×v.
--   - `affineBlock`: PDF p.9: homogeneous affine generator (Q,b;0,0).
--   - `operatorQ`: PDF p.11: actual Bloch-coordinate data extracted from the operator dissipator.
--   - `operatorB`: PDF p.11: actual translation extracted from D_L(I).
--   - `controlBlock`: PDF p.9: a coherent affine generator.
--   - `channelBlock`: PDF p.9: a channel affine generator extracted from the matrix action.
--   - `generatedAlgebra`: PDF pp.9,11: system Lie algebra for a control-axis set and one jump.
--   - `controlAlgebra`: PDF p.9: coherent-control Lie algebra with no dissipator adjoined.
--   - `bracketDirections`: PDF p.11: linear span of brackets of generated directions.
--   - `IsGKLS`: PDF pp.4,9: arbitrary qubit GKLS generators, allowing finitely many channels. The coefficients are extracted from the actual operator action.
--   - `coordinateChange`: PDF p.11: homogeneous coordinate change (T,0;0,1).
--   - `blochConjugate`: PDF p.11: both the matrix part and the translation are conjugated.
--   - `IsRotation`: PDF p.12: a proper spatial rotation.
--   - `Stabilizes`: PDF p.12: stabilizer of the full affine data, including the translation.
--   - `axisRotation`: PDF p.12: Rodrigues rotation about a unit axis. Unit length is required at use sites.
--   - `HasRotationAxis`: PDF p.12: a continuous rotational symmetry axis.
--   - `dampingBlock`: PDF p.11: extremal damping witness D=(diag(-1/2,-1/2,-1),-e_z).
--   - `shiftedDamping`: PDF p.11: the separated, uncompensated shifted damping channel.
--   - `weightOneSymmetric`: PDF pp.15--16: the symmetric weight-one sector. Indices are zero-based here.
--   - `weightOneRotation`: PDF pp.15--16: the rotational weight-one sector span(J_x,J_y).
--   - `weightTwoDeviator`: PDF pp.15--16: weight two plus the deviatoric line; no scalar identity component.
--   - `affineBracket`: PDF p.16: the affine commutator on gl(V) ⋉ V, for arbitrary real V.
--   - `IrreducibleProjection`: PDF p.16: irreducibility for the actual projected action; excludes the zero module.
--   - `Operator`: PDF pp.4--5: operators on a positive-dimensional space (positivity at use sites).
--   - `IsTracelessHermitianBasis`: PDF p.5: a real basis of the traceless Hermitian operators; no orthonormality or positivity of the Kossakowski coordinates is built into this predicate.
--   - `gramMatrix`: PDF p.5: G_jk=Tr(F_k F_j), in exactly the source's index order.
--   - `kossakowskiAction`: PDF pp.4--5: Kossakowski coordinate action; K may be Hermitian of either sign. Positive semidefiniteness is imposed only for physical cone membership.
--   - `superoperatorTrace`: PDF p.5: trace on the full complex operator space, computed in matrix units. This is distinct from Tr(L(rho)), which is zero for a trace-annihilating map.
--   - `IsLKAction`: PDF p.4: complex-linear Hermiticity-preserving trace-annihilating maps.
--   - `dissipationStrength`: PDF p.5: phi(L)=-Re(Tr L)/d; the trace is real on the ambient real algebra.
--   - `IsPhysicalAction`: PDF pp.4--5: the physical cone in coordinates on a specified basis.
--   - `IsHamiltonianAction`: PDF p.5: purely Hamiltonian generators, with the scalar gauge fixed by Tr H=0.
-- source:
--   Lie-Wedge Stratification and Pure-State Stabilizability in Single-Channel Qubit Control, arXiv:2610.00046v1, https://arxiv.org/abs/2610.00046v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QubitBlochMaps

/-! Paper-local interfaces for arXiv:2610.00046v1. All numbered claims are statements only.
Homogeneous affine blocks encode v ↦ Qv+b, with a zero last row for generators.
The quantum dissipator is defined on matrices independently of its Bloch coordinates. -/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P59

/-- PDF p.9: real Bloch-coordinate vectors, in the pinned X,Y,Z order. -/
abbrev Vec := Fin 3 → ℝ
/-- PDF p.9: complex coefficients of a traceless qubit jump. -/
abbrev Cvec := Fin 3 → ℂ
/-- PDF p.9: real linear maps on Bloch coordinates. -/
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ
/-- PDF pp.9,11: homogeneous-coordinate matrices; generators have zero last row. -/
abbrev Block := Matrix (Fin 4) (Fin 4) ℝ
/-- PDF p.9: complex qubit operators, using the accepted Boolean basis. -/
abbrev Qmat := Matrix Bool Bool ℂ

-- Use the associative matrix commutator for every generated Lie algebra below.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.9: L=a·sigma in the pinned X,Y,Z order. -/
def jump (a : Cvec) : Qmat := ∑ j, a j • QubitChannels.sigma j

/-- PDF p.9: rho(v)=(I+v·sigma)/2; defined also off the Bloch ball. -/
def blochState (v : Vec) : Qmat := (2⁻¹ : ℂ) • (1 + jump (fun j => (v j : ℂ)))

/-- PDF pp.9,11: the actual operator dissipator, not its claimed affine formula. -/
def dissipator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L X : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  L * X * Lᴴ - (2⁻¹ : ℂ) • (Lᴴ * L * X + X * Lᴴ * L)

/-- PDF pp.4,9: the Hamiltonian superoperator, with the source's minus-i sign. -/
def coherent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H X : Matrix ι ι ℂ) : Matrix ι ι ℂ := -Complex.I • (H * X - X * H)

/-- PDF p.11: the Hamiltonian added to the dissipator by L ↦ L+cI.
Its negative is the compensating change of the autonomous Hamiltonian. -/
def gaugeHamiltonian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Matrix ι ι ℂ) (c : ℂ) : Matrix ι ι ℂ :=
  (Complex.I / 2) • (star c • L - c • Lᴴ)

/-- PDF p.11: squared coefficient norm |a|², independent of any matrix norm. -/
def amplitudeSq (a : Cvec) : ℝ := ∑ j, Complex.normSq (a j)

/-- PDF p.12: M=alpha alpha^T+beta beta^T. -/
def channelMoment (a : Cvec) : Mat := fun i j =>
  (a i).re * (a j).re + (a i).im * (a j).im

/-- PDF p.11, (19): candidate linear Bloch coefficient. -/
def channelQ (a : Cvec) : Mat := 2 • (channelMoment a - amplitudeSq a • (1 : Mat))

/-- PDF p.11, (19): candidate affine translation, in the right-handed convention. -/
def channelB (a : Cvec) : Vec :=
  4 • crossProduct (fun j => (a j).re) (fun j => (a j).im)

/-- PDF p.9: J_n v=n×v. -/
def rotationGenerator (n : Vec) : Mat :=
  !![0, -n 2, n 1; n 2, 0, -n 0; -n 1, n 0, 0]

/-- PDF p.9: homogeneous affine generator (Q,b;0,0). -/
def affineBlock (Q : Mat) (b : Vec) : Block := fun i j =>
  if hi : i.val < 3 then
    if hj : j.val < 3 then Q ⟨i.val, hi⟩ ⟨j.val, hj⟩ else b ⟨i.val, hi⟩
  else 0

/-- PDF p.11: actual Bloch-coordinate data extracted from the operator dissipator. -/
def operatorQ (a : Cvec) : Mat := fun i j =>
  ((QubitChannels.sigma i * dissipator (jump a) (QubitChannels.sigma j)).trace.re) / 2

/-- PDF p.11: actual translation extracted from D_L(I). -/
def operatorB (a : Cvec) : Vec := fun i =>
  ((QubitChannels.sigma i * dissipator (jump a) 1).trace.re) / 2

/-- PDF p.9: a coherent affine generator. -/
def controlBlock (n : Vec) : Block := affineBlock (rotationGenerator n) 0

/-- PDF p.9: a channel affine generator extracted from the matrix action. -/
def channelBlock (a : Cvec) : Block := affineBlock (operatorQ a) (operatorB a)

/-- PDF pp.9,11: system Lie algebra for a control-axis set and one jump. -/
def generatedAlgebra (axes : Set Vec) (a : Cvec) : LieSubalgebra ℝ Block :=
  LieSubalgebra.lieSpan ℝ Block (controlBlock '' axes ∪ {channelBlock a})

/-- PDF p.9: coherent-control Lie algebra with no dissipator adjoined. -/
def controlAlgebra (axes : Set Vec) : LieSubalgebra ℝ Block :=
  LieSubalgebra.lieSpan ℝ Block (controlBlock '' axes)

/-- PDF p.11: linear span of brackets of generated directions. -/
def bracketDirections (g : LieSubalgebra ℝ Block) : Submodule ℝ Block :=
  Submodule.span ℝ {B | ∃ X ∈ g, ∃ Y ∈ g, B = X * Y - Y * X}

/-- PDF pp.4,9: arbitrary qubit GKLS generators, allowing finitely many channels.
The coefficients are extracted from the actual operator action. -/
def IsGKLS (X : Block) : Prop :=
  ∃ (n : Vec) (k : ℕ) (a : Fin k → Cvec), X = controlBlock n + ∑ j, channelBlock (a j)

/-- PDF p.11: homogeneous coordinate change (T,0;0,1). -/
def coordinateChange (T : Mat) : Block := affineBlock T 0 + Matrix.single 3 3 1

/-- PDF p.11: both the matrix part and the translation are conjugated. -/
def blochConjugate (T : Mat) (X : Block) : Block :=
  coordinateChange T * X * coordinateChange T⁻¹

/-- PDF p.12: a proper spatial rotation. -/
def IsRotation (R : Mat) : Prop := R.transpose * R = 1 ∧ R.det = 1

/-- PDF p.12: stabilizer of the full affine data, including the translation. -/
def Stabilizes (a : Cvec) (R : Mat) : Prop :=
  R * operatorQ a * R.transpose = operatorQ a ∧ R.mulVec (operatorB a) = operatorB a

/-- PDF p.12: Rodrigues rotation about a unit axis. Unit length is required at use sites. -/
def axisRotation (n : Vec) (theta : ℝ) : Mat :=
  Real.cos theta • (1 : Mat) +
    (1 - Real.cos theta : ℝ) • Matrix.of (fun i j => n i * n j) +
    Real.sin theta • rotationGenerator n

/-- PDF p.12: a continuous rotational symmetry axis. -/
def HasRotationAxis (a : Cvec) : Prop :=
  ∃ n : Vec, (∑ j, n j ^ 2) = 1 ∧ ∀ theta : ℝ, Stabilizes a (axisRotation n theta)

/-- PDF p.11: extremal damping witness D=(diag(-1/2,-1/2,-1),-e_z). -/
def dampingBlock : Block :=
  affineBlock (Matrix.diagonal ![-(1/2 : ℝ), -(1/2 : ℝ), -1]) ![0, 0, -1]

/-- PDF p.11: the separated, uncompensated shifted damping channel. -/
def shiftedDamping (c : ℝ) : Block := dampingBlock + c • controlBlock ![0, 1, 0]

/-- PDF pp.15--16: the symmetric weight-one sector. Indices are zero-based here. -/
def weightOneSymmetric : Submodule ℝ Mat :=
  Submodule.span ℝ { (!![0,0,1; 0,0,0; 1,0,0] : Mat), !![0,0,0; 0,0,1; 0,1,0] }

/-- PDF pp.15--16: the rotational weight-one sector span(J_x,J_y). -/
def weightOneRotation : Submodule ℝ Mat :=
  Submodule.span ℝ {rotationGenerator ![1,0,0], rotationGenerator ![0,1,0]}

/-- PDF pp.15--16: weight two plus the deviatoric line; no scalar identity component. -/
def weightTwoDeviator : Submodule ℝ Mat :=
  Submodule.span ℝ { (!![1,0,0; 0,-1,0; 0,0,0] : Mat),
    !![0,1,0; 1,0,0; 0,0,0], !![1,0,0; 0,1,0; 0,0,-2] }

/-- PDF p.16: the affine commutator on gl(V) ⋉ V, for arbitrary real V. -/
def affineBracket {V : Type*} [AddCommGroup V] [Module ℝ V]
    (X Y : Module.End ℝ V × V) : Module.End ℝ V × V :=
  (X.1 * Y.1 - Y.1 * X.1, X.1 Y.2 - Y.1 X.2)

/-- PDF p.16: irreducibility for the actual projected action; excludes the zero module. -/
def IrreducibleProjection {V : Type*} [AddCommGroup V] [Module ℝ V]
    (h : Submodule ℝ (Module.End ℝ V × V)) : Prop :=
  Nontrivial V ∧ ∀ U : Submodule ℝ V,
    (∀ X ∈ h, ∀ v ∈ U, X.1 v ∈ U) → U = ⊥ ∨ U = ⊤

/-- Sanity: zero jump is the zero operator. -/
example : jump 0 = 0 := by simp [jump]

/-- Sanity: the center is I/2; no state normalization is silently dropped. -/
example : blochState 0 = (2⁻¹ : ℂ) • (1 : Qmat) := by simp [blochState, jump]

/-- Sanity: the operator dissipator vanishes on a zero jump. -/
example (X : Qmat) : dissipator 0 X = 0 := by simp [dissipator]

/-- Sanity: the gauge compensation vanishes for c=0. -/
example (L : Qmat) : gaugeHamiltonian L 0 = 0 := by simp [gaugeHamiltonian]

/-- Sanity: J_z has (0,1,0) as its action on the x axis. -/
example : rotationGenerator ![0,0,1] = (!![0,-1,0; 1,0,0; 0,0,0] : Mat) := by
  simp [rotationGenerator]

/-- Sanity: affine generators have zero last row, including the translation entry. -/
example (Q : Mat) (b : Vec) (j : Fin 4) : affineBlock Q b 3 j = 0 := by
  simp [affineBlock]

/-- Sanity: a coordinate change preserves the homogeneous coordinate. -/
example (T : Mat) : coordinateChange T 3 3 = 1 := by
  simp [coordinateChange, affineBlock, Matrix.single]

/-- Sanity: the Rodrigues family contains the identity at zero angle. -/
example (n : Vec) : axisRotation n 0 = 1 := by
  ext i j
  simp [axisRotation]

/-- Sanity: the affine bracket agrees with the infinitesimal action on translations. -/
example {V : Type*} [AddCommGroup V] [Module ℝ V] (A : Module.End ℝ V) (v : V) :
    affineBracket (A, (0 : V)) (0, v) = (0, A v) := by simp [affineBracket]

/-- PDF pp.4--5: operators on a positive-dimensional space (positivity at use sites). -/
abbrev Operator (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- PDF p.5: a real basis of the traceless Hermitian operators; no orthonormality
or positivity of the Kossakowski coordinates is built into this predicate. -/
def IsTracelessHermitianBasis {d : ℕ} (F : Fin (d^2-1) → Operator d) : Prop :=
  (∀ j, (F j).IsHermitian ∧ (F j).trace = 0) ∧ LinearIndependent ℝ F ∧
    ∀ X : Operator d, X.IsHermitian → X.trace = 0 →
      X ∈ Submodule.span ℝ (Set.range F)

/-- PDF p.5: G_jk=Tr(F_k F_j), in exactly the source's index order. -/
def gramMatrix {d : ℕ} (F : Fin (d^2-1) → Operator d) :
    Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ := fun j k => (F k * F j).trace

/-- PDF pp.4--5: Kossakowski coordinate action; K may be Hermitian of either sign.
Positive semidefiniteness is imposed only for physical cone membership. -/
def kossakowskiAction {d : ℕ} (F : Fin (d^2-1) → Operator d) (H : Operator d)
    (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ) (X : Operator d) : Operator d :=
  coherent H X + ∑ j, ∑ k, K j k •
    (F j * X * (F k)ᴴ - (2⁻¹ : ℂ) •
      ((F k)ᴴ * F j * X + X * (F k)ᴴ * F j))

/-- PDF p.5: trace on the full complex operator space, computed in matrix units.
This is distinct from Tr(L(rho)), which is zero for a trace-annihilating map. -/
def superoperatorTrace {d : ℕ} (L : Operator d → Operator d) : ℂ :=
  ∑ i : Fin d, ∑ j : Fin d, L (Matrix.single i j 1) i j

/-- PDF p.4: complex-linear Hermiticity-preserving trace-annihilating maps. -/
def IsLKAction {d : ℕ} (L : Operator d → Operator d) : Prop :=
  (∃ A : Module.End ℂ (Operator d), L = fun X => A X) ∧
    (∀ X, X.IsHermitian → (L X).IsHermitian) ∧ (∀ X, (L X).trace = 0)

/-- PDF p.5: phi(L)=-Re(Tr L)/d; the trace is real on the ambient real algebra. -/
def dissipationStrength {d : ℕ} (L : Operator d → Operator d) : ℝ :=
  -(superoperatorTrace L).re / (d : ℝ)

/-- PDF pp.4--5: the physical cone in coordinates on a specified basis. -/
def IsPhysicalAction {d : ℕ} (F : Fin (d^2-1) → Operator d)
    (L : Operator d → Operator d) : Prop :=
  ∃ (H : Operator d) (K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ),
    H.IsHermitian ∧ K.PosSemidef ∧ L = kossakowskiAction F H K

/-- PDF p.5: purely Hamiltonian generators, with the scalar gauge fixed by Tr H=0. -/
def IsHamiltonianAction {d : ℕ} (L : Operator d → Operator d) : Prop :=
  ∃ H : Operator d, H.IsHermitian ∧ H.trace = 0 ∧ L = coherent H

/-- Sanity: the zero superoperator has zero superoperator trace in every dimension. -/
example (d : ℕ) : superoperatorTrace (fun _ : Operator d => (0 : Operator d)) = 0 := by
  simp [superoperatorTrace]

/-- Sanity: zero Hamiltonian and zero Kossakowski data give zero action. -/
example {d : ℕ} (F : Fin (d^2-1) → Operator d) (X : Operator d) :
    kossakowskiAction F 0 0 X = 0 := by
  simp [kossakowskiAction, coherent]

/-- Sanity: zero data have no dissipation strength, independently of d. -/
example (d : ℕ) : dissipationStrength (fun _ : Operator d => (0 : Operator d)) = 0 := by
  simp [dissipationStrength, superoperatorTrace]

end QAlgorithms.Papers.Independent.Information100.P59


