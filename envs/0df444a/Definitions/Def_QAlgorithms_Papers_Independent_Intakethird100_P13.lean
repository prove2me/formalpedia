-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P13
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T04:51:45.419788+00:00
-- url     : https://prove2.me/theorems/18019906-71fe-4443-9c87-6be2541dd9a8
-- title:
--   Definitions for Simulation of non-Pauli Channels
-- statement:
--   The objects the formalized statements of *Simulation of non-Pauli Channels* (arXiv:1706.05384) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `QubitOp`: PDF p.3: qubit operators in the fixed Bool computational basis.
--   - `ResourceOp`: PDF pp.3,5: two-qubit operators, Alice/reference first and Bob/output second.
--   - `QubitMap`: PDF p.5: the imported all-operator superoperator type specialized to qubits.
--   - `BlochCoordinates`: PDF p.3, Eqs.(14),(23): three real Bloch/correlation coordinates, not algebraic points.
--   - `teleportationPauli`: PDF pp.2--3: the ordered basis (I,X,Y,Z), with the library's computational basis.
--   - `FourOutcomeLaw`: PDF pp.3,5, Eqs.(9),(36): a normalized four-letter probability law.
--   - `ClassicalTeleportationLaw`: PDF p.5, Eq.(36): p(l|k), output index FIRST; no row-sum condition is imposed.
--   - `teleportationBellAmplitude`: PDF p.3, Eqs.(10)--(13): Bell vectors Phi+,Psi+,Psi-,Phi-. The Y-generated third vector differs from Psi- by an irrelevant phase.
--   - `teleportationBellProjector`: PDF p.3, Eqs.(10)--(13): normalized Bell projectors, phase independent.
--   - `teleportationBellMixture`: PDF p.3, Eq.(24): the actual Bell-diagonal resource with weights w.
--   - `qubitBellBranch`: PDF pp.2,5: unnormalized Bob state after Bell outcome k on C,A. Every branch is retained; there is no division by an outcome probability.
--   - `noisyTeleport`: PDF p.5: the physical noisy Bell/Pauli protocol, averaged over both classical labels. The resource tau and the conditional law p are fixed before rho.
--   - `Simulable`: PDF p.5: simulability by exactly this protocol on every operator, hence with references.
--   - `augmentedMoment`: PDF p.3, Eq.(8): augmented t_(j,i); j=0 is Bob's local Bloch vector.
--   - `bobVector`: PDF p.3, Eq.(8): Bob's local Bloch vector, not Alice's.
--   - `resourcePauliCorrelation`: PDF p.3, Eq.(8): correlations in Alice-row, Bob-column order.
--   - `labelKroneckerDelta`: PDF p.5, Eq.(38): Kronecker delta in the exponent.
--   - `sCoordinate`: PDF p.5, Eq.(38): the six deltas and common 1/4 are essential. Appendix B's summation instruction omits that factor and is not used.
--   - `fCoordinate`: PDF p.5, Eqs.(37)--(39): f_ij = tprime_(j,i) S_ij.
--   - `bellVertex`: PDF p.3, Eq.(23): source correlation vertices; actual Y multipliers have opposite sign.
--   - `pauliTetrahedron`: PDF p.3, Eq.(23): the closed Bell-correlation tetrahedron, not the multiplier tetrahedron.
--   - `pauliMixture`: PDF p.3, Eq.(9): an actual probability mixture of Pauli conjugations.
--   - `IsPauli`: PDF p.3, Eq.(9): Pauli channels always carry a normalized probability law.
--   - `pauliPointChannel`: PDF pp.3,6, Eqs.(15),(52): q is a correlation point, so the Y multiplier is -q2.
--   - `blochAmplitudeDamping`: PDF pp.6--7, Eqs.(47),(51): amplitude damping on all operators. Its physical parameter range is supplied by each theorem.
--   - `normalizedQubitChoi`: PDF pp.3,6, Eqs.(26),(48): normalized Choi resource, reference first.
--   - `pauliDamping`: PDF p.7, Eq.(53): Bool false/true encodes u=0/1; this asserts no uniqueness.
--   - `attainableVertices`: PDF p.7, Eq.(59): eight vertices with paired signs, regular regime only.
--   - `attainableRegion`: PDF pp.7--8, Eq.(59): complete convex attainable q region for 0<gamma<1.
--   - `axialReplacement`: PDF p.8: axial replacement, used to state gamma=1 without 0/0.
--   - `channelTraceDistance`: PDF p.9, Eq.(68): full trace norm supremum over normalized qubit states. For the channel arguments in the statements the domain is nonempty and the image bounded.
--   - `channelDiamondDistance`: PDF p.9, Eq.(72): full norm with a qubit reference, on normalized density inputs.
--   - `closestPoint`: PDF pp.9,14: explicit closest Pauli correlation point, translation deleted.
--   - `closestPauli`: PDF pp.9,14: concrete minimizing channel, with the source's Y-coordinate convention.
--   - `discardClassical`: PDF p.10: forgetting Alice's outcome and always applying I retains all branches.
--   - `rescaling`: PDF p.12, Lemma 20: regular quotient, used only with a strictly positive denominator.
--   - `contractPoint`: PDF p.12, Lemma 22: roots apply to alpha, never to coordinates.
--   - `regularPauliPoint`: PDF pp.12--13, Eq.(C3): q is constructed from S, rather than freely supplied.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, https://arxiv.org/abs/1706.05384v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QubitBlochMaps
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

/-! Statements from Cope--Hetzel--Banchi--Pirandola, arXiv:1706.05384v2.
All local constructions use the fixed computational basis false=0, true=1.
Source ambiguities and the operational-capacity interface gap are recorded in HARD.md.
Compilation is pending the mechanical batch handoff. -/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3: qubit operators in the fixed Bool computational basis. -/
abbrev QubitOp := Matrix Bool Bool ℂ

/-- PDF pp.3,5: two-qubit operators, Alice/reference first and Bob/output second. -/
abbrev ResourceOp := Matrix (Bool × Bool) (Bool × Bool) ℂ

/-- PDF p.5: the imported all-operator superoperator type specialized to qubits. -/
abbrev QubitMap := QAlgorithms.Superop Bool Bool

/-- PDF p.3, Eqs.(14),(23): three real Bloch/correlation coordinates, not algebraic points. -/
abbrev BlochCoordinates := Fin 3 → ℝ

/-- PDF pp.2--3: the ordered basis (I,X,Y,Z), with the library's computational basis. -/
def teleportationPauli : Fin 4 → QubitOp := ![1, QAlgorithms.QubitChannels.sigma 0,
  QAlgorithms.QubitChannels.sigma 1, QAlgorithms.QubitChannels.sigma 2]

/-- PDF pp.3,5, Eqs.(9),(36): a normalized four-letter probability law. -/
def FourOutcomeLaw (w : Fin 4 → ℝ) : Prop :=
  (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1

/-- PDF p.5, Eq.(36): p(l|k), output index FIRST; no row-sum condition is imposed. -/
def ClassicalTeleportationLaw (p : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ k, FourOutcomeLaw (fun l => p l k)

/-- PDF p.3, Eqs.(10)--(13): Bell vectors Phi+,Psi+,Psi-,Phi-.
The Y-generated third vector differs from Psi- by an irrelevant phase. -/
def teleportationBellAmplitude (k : Fin 4) (c a : Bool) : ℂ :=
  (Real.sqrt 2 : ℂ)⁻¹ * teleportationPauli k a c

/-- PDF p.3, Eqs.(10)--(13): normalized Bell projectors, phase independent. -/
def teleportationBellProjector (k : Fin 4) : ResourceOp :=
  fun x y => teleportationBellAmplitude k x.1 x.2 * conj (teleportationBellAmplitude k y.1 y.2)

/-- PDF p.3, Eq.(24): the actual Bell-diagonal resource with weights w. -/
def teleportationBellMixture (w : Fin 4 → ℝ) : ResourceOp :=
  ∑ k, (w k : ℂ) • teleportationBellProjector k

/-- PDF pp.2,5: unnormalized Bob state after Bell outcome k on C,A.
Every branch is retained; there is no division by an outcome probability. -/
def qubitBellBranch (tau : ResourceOp) (k : Fin 4) (rho : QubitOp) : QubitOp :=
  fun b b2 => ∑ c : Bool, ∑ a : Bool, ∑ d : Bool, ∑ a2 : Bool,
    conj (teleportationBellAmplitude k c a) * rho c d * tau (a,b) (a2,b2) * teleportationBellAmplitude k d a2

/-- PDF p.5: the physical noisy Bell/Pauli protocol, averaged over both classical labels.
The resource tau and the conditional law p are fixed before rho. -/
def noisyTeleport (tau : ResourceOp) (p : Fin 4 → Fin 4 → ℝ) : QubitMap :=
  fun rho => ∑ k, ∑ l, (p l k : ℂ) •
    (teleportationPauli l * qubitBellBranch tau k rho * (teleportationPauli l)ᴴ)

/-- PDF p.5: simulability by exactly this protocol on every operator, hence with references. -/
def Simulable (tau : ResourceOp) (E : QubitMap) : Prop :=
  ∃ p, ClassicalTeleportationLaw p ∧ noisyTeleport tau p = E

/-- PDF p.3, Eq.(8): augmented t_(j,i); j=0 is Bob's local Bloch vector. -/
def augmentedMoment (tau : ResourceOp) (j : Fin 4) (i : Fin 3) : ℝ :=
  ((Matrix.kronecker (teleportationPauli j) (teleportationPauli i.succ) * tau).trace).re

/-- PDF p.3, Eq.(8): Bob's local Bloch vector, not Alice's. -/
def bobVector (tau : ResourceOp) : BlochCoordinates := fun i => augmentedMoment tau 0 i

/-- PDF p.3, Eq.(8): correlations in Alice-row, Bob-column order. -/
def resourcePauliCorrelation (tau : ResourceOp) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun j i => augmentedMoment tau j.succ i

/-- PDF p.5, Eq.(38): Kronecker delta in the exponent. -/
def labelKroneckerDelta (a b : Fin 4) : ℕ := if a = b then 1 else 0

/-- PDF p.5, Eq.(38): the six deltas and common 1/4 are essential.
Appendix B's summation instruction omits that factor and is not used. -/
def sCoordinate (p : Fin 4 → Fin 4 → ℝ) (i : Fin 3) (j : Fin 4) : ℝ :=
  (1 / 4 : ℝ) * ∑ k, ∑ l,
    (-1 : ℝ) ^ (labelKroneckerDelta k 0 + labelKroneckerDelta j 2 + labelKroneckerDelta j 0 + labelKroneckerDelta k j +
      labelKroneckerDelta i.succ l + labelKroneckerDelta 0 l) * p l k

/-- PDF p.5, Eqs.(37)--(39): f_ij = tprime_(j,i) S_ij. -/
def fCoordinate (tau : ResourceOp) (p : Fin 4 → Fin 4 → ℝ)
    (i : Fin 3) (j : Fin 4) : ℝ :=
  augmentedMoment tau j i * sCoordinate p i j

/-- PDF p.3, Eq.(23): source correlation vertices; actual Y multipliers have opposite sign. -/
def bellVertex : Fin 4 → BlochCoordinates :=
  ![![1,-1,1], ![1,1,-1], ![-1,-1,-1], ![-1,1,1]]

/-- PDF p.3, Eq.(23): the closed Bell-correlation tetrahedron, not the multiplier tetrahedron. -/
def pauliTetrahedron : Set BlochCoordinates := convexHull ℝ (Set.range bellVertex)

/-- PDF p.3, Eq.(9): an actual probability mixture of Pauli conjugations. -/
def pauliMixture (w : Fin 4 → ℝ) : QubitMap :=
  fun rho => ∑ k, (w k : ℂ) • (teleportationPauli k * rho * (teleportationPauli k)ᴴ)

/-- PDF p.3, Eq.(9): Pauli channels always carry a normalized probability law. -/
def IsPauli (E : QubitMap) : Prop :=
  ∃ w, FourOutcomeLaw w ∧ E = pauliMixture w

/-- PDF pp.3,6, Eqs.(15),(52): q is a correlation point, so the Y multiplier is -q2. -/
def pauliPointChannel (q : BlochCoordinates) : QubitMap :=
  QAlgorithms.QubitChannels.blochAffineMap 0 (Matrix.diagonal ![q 0, -q 1, q 2])

/-- PDF pp.6--7, Eqs.(47),(51): amplitude damping on all operators.
Its physical parameter range is supplied by each theorem. -/
def blochAmplitudeDamping (gamma : ℝ) : QubitMap :=
  QAlgorithms.QubitChannels.blochAffineMap ![0,0,gamma]
    (Matrix.diagonal ![Real.sqrt (1-gamma), Real.sqrt (1-gamma), 1-gamma])

/-- PDF pp.3,6, Eqs.(26),(48): normalized Choi resource, reference first. -/
def normalizedQubitChoi (E : QubitMap) : ResourceOp :=
  idTensorSuperop (R := Bool) E (teleportationBellProjector 0)

/-- PDF p.7, Eq.(53): Bool false/true encodes u=0/1; this asserts no uniqueness. -/
def pauliDamping (u : Bool) (eta : ℝ) (q : BlochCoordinates) : QubitMap :=
  fun rho => let Y := blochAmplitudeDamping eta (pauliPointChannel q rho)
    if u then pauliX * Y * pauliXᴴ else Y

/-- PDF p.7, Eq.(59): eight vertices with paired signs, regular regime only. -/
def attainableVertices (gamma eta : ℝ) : Fin 8 → BlochCoordinates :=
  let a := Real.sqrt ((1-gamma)/(1-eta))
  let b := 1-eta/gamma
  ![![a,a*b,-a^2*b], ![a,-a*b,a^2*b],
    ![a*b,a,-a^2*b], ![-a*b,a,a^2*b],
    ![-a,a*b,a^2*b], ![-a,-a*b,-a^2*b],
    ![a*b,-a,a^2*b], ![-a*b,-a,-a^2*b]]

/-- PDF pp.7--8, Eq.(59): complete convex attainable q region for 0<gamma<1. -/
def attainableRegion (gamma eta : ℝ) : Set BlochCoordinates :=
  convexHull ℝ (Set.range (attainableVertices gamma eta))

/-- PDF p.8: axial replacement, used to state gamma=1 without 0/0. -/
def axialReplacement (z : ℝ) : QubitMap :=
  QAlgorithms.QubitChannels.blochAffineMap ![0,0,z] 0

/-- PDF p.9, Eq.(68): full trace norm supremum over normalized qubit states.
For the channel arguments in the statements the domain is nonempty and the image bounded. -/
def channelTraceDistance (E F : QubitMap) : ℝ :=
  sSup {v | ∃ rho : QubitOp, IsDensityMatrix rho ∧ v = traceNorm (E rho - F rho)}

/-- PDF p.9, Eq.(72): full norm with a qubit reference, on normalized density inputs. -/
def channelDiamondDistance (E F : QubitMap) : ℝ :=
  sSup {v | ∃ rho : ResourceOp, IsDensityMatrix rho ∧
    v = traceNorm (idTensorSuperop (R := Bool) E rho -
      idTensorSuperop (R := Bool) F rho)}

/-- PDF pp.9,14: explicit closest Pauli correlation point, translation deleted. -/
def closestPoint (u : Bool) (eta : ℝ) (q : BlochCoordinates) : BlochCoordinates :=
  let a := Real.sqrt (1-eta)
  if u then ![a*q 0, -a*q 1, -(1-eta)*q 2]
  else ![a*q 0, a*q 1, (1-eta)*q 2]

/-- PDF pp.9,14: concrete minimizing channel, with the source's Y-coordinate convention. -/
def closestPauli (u : Bool) (eta : ℝ) (q : BlochCoordinates) : QubitMap :=
  pauliPointChannel (closestPoint u eta q)

/-- PDF p.10: forgetting Alice's outcome and always applying I retains all branches. -/
def discardClassical : Fin 4 → Fin 4 → ℝ := fun l _ => if l = 0 then 1 else 0

/-- PDF p.12, Lemma 20: regular quotient, used only with a strictly positive denominator. -/
def rescaling (gamma s30 : ℝ) : ℝ := (1-gamma)/(1-gamma*s30)

/-- PDF p.12, Lemma 22: roots apply to alpha, never to coordinates. -/
def contractPoint (alpha : ℝ) (q : BlochCoordinates) : BlochCoordinates :=
  ![Real.sqrt alpha*q 0, Real.sqrt alpha*q 1, alpha*q 2]

/-- PDF pp.12--13, Eq.(C3): q is constructed from S, rather than freely supplied. -/
def regularPauliPoint (gamma s30 : ℝ) (s : BlochCoordinates) : BlochCoordinates :=
  contractPoint (rescaling gamma s30) s

/-- Definition sanity: source's first resourcePauliCorrelation vertex. -/
example : bellVertex 0 = ![1,-1,1] := rfl

/-- Definition sanity: normalized classical reset, including all four input columns. -/
example : ClassicalTeleportationLaw discardClassical := by
  intro k
  constructor
  · intro l; by_cases h : l = 0 <;> simp [discardClassical, h]
  · simp [discardClassical]

/-- Definition sanity: at alpha=0 the contraction is the origin. -/
example (q : BlochCoordinates) : contractPoint 0 q = 0 := by
  funext i
  fin_cases i <;> simp [contractPoint]

/-- Definition sanity: no singular quotient is needed at zero damping. -/
example (s : ℝ) : rescaling 0 s = 1 := by simp [rescaling]

/-- Definition sanity: the first coordinate of the regular vertex is computed directly. -/
example (gamma : ℝ) :
    attainableVertices gamma gamma 0 0 = Real.sqrt ((1-gamma)/(1-gamma)) := rfl

/-- Definition sanity: eta=gamma makes b=0 in both remaining coordinates. -/
example (gamma : ℝ) (h : gamma ≠ 0) :
    attainableVertices gamma gamma 0 1 = 0 ∧
    attainableVertices gamma gamma 0 2 = 0 := by
  simp [attainableVertices, h]

/-- Definition sanity: the first Bell vector has positive normalized 00 amplitude. -/
example : teleportationBellAmplitude 0 false false = (Real.sqrt 2 : ℂ)⁻¹ := by
  simp [teleportationBellAmplitude, teleportationPauli, QAlgorithms.QubitChannels.sigma]

/-- Definition sanity: the third Bell vector has the allowed global Y phase. -/
example : teleportationBellAmplitude 2 false true = (Real.sqrt 2 : ℂ)⁻¹ * Complex.I := by
  simp [teleportationBellAmplitude, teleportationPauli, QAlgorithms.QubitChannels.sigma, pauliY]

/-- Definition sanity: Bell-branch averaging is performed before choosing an input. -/
example (tau : ResourceOp) (p : Fin 4 → Fin 4 → ℝ) (rho : QubitOp) :
    noisyTeleport tau p rho = ∑ k, ∑ l, (p l k : ℂ) •
      (teleportationPauli l * qubitBellBranch tau k rho * (teleportationPauli l)ᴴ) := rfl

end QAlgorithms.Papers.Independent.Intakethird100.P13


