-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30
-- name    : QAlgorithms_Papers_Independent_Extend50_P30
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T15:54:00.532487+00:00
-- url     : https://prove2.me/theorems/39876b3a-952d-4ee8-9d7b-1dc1dca008d8
-- title:
--   Definitions for Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations
-- statement:
--   The objects the formalized statements of *Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations* (arXiv:1712.08628) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ResidueRegister`: PDF p.14: n qudits in the specified cyclic-residue computational basis.
--   - `DiscretePhaseSpace`: PDF p.15: momentum and position labels over ZMod d, also for composite d.
--   - `QuditOperator`: PDF p.14: operators indexed by the cyclic computational register.
--   - `QuditCopies`: Specialize the accepted copy register to the source cyclic-qudit basis.
--   - `phaseModulus`: PDF p.14: the order of weylPhase.
--   - `weylRoot`: PDF p.14: omega, with the stray q removed as fixed by the action of Z.
--   - `weylPhase`: PDF p.14: weylPhase includes the parity-dependent sign.
--   - `cyclicWeyl`: PDF pp.14--15, (2.1): canonical lifts and output-row convention for Z^p X^q.
--   - `symplecticBracket`: PDF p.15, (2.3), with the source sign.
--   - `cyclicPauliGroup`: PDF pp.14--17: the finite Pauli group, including all powers of weylPhase.
--   - `IsCyclicStabilizerGroup`: PDF p.16: finite Pauli subgroup with no nonidentity scalar.
--   - `pauliAverageProjector`: PDF p.16, (2.14): code projection before trace normalization.
--   - `mixedStabilizers`: PDF p.58 footnote 8: maximally mixed code states, not their convex hull.
--   - `stabilizers`: PDF p.17: phase-free pure stabilizer density matrices.
--   - `IsStabilizer`: Pure stabilizer predicate; vector phases are immaterial.
--   - `stabilizerOverlap`: Fidelity with a pure state specified by its density matrix.
--   - `FarFromStabilizers`: Source maximum upper bound, pointwise on exactly the finite stabilizer set.
--   - `IsClifford`: PDF p.14: full unitary normalizer, retaining scalar representatives.
--   - `characteristicDistribution`: PDF p.18, (3.2): characteristic distribution.
--   - `weylBellVector`: PDF p.19: normalized Bell vector (W_x tensor I)|Phi+>.
--   - `bellDifference`: PDF p.19: two Bell measurements and XOR of the labels, on four copies.
--   - `qubitTest`: PDF p.22, (3.11): Algorithm 1, four sampling copies and two verification copies.
--   - `realQubitTest`: PDF p.22, Remark 3.5: two Bell-sampling and two verification copies.
--   - `quditInvolution`: PDF p.23, (3.15): alternating W and W dagger, with normalization d^{-n}.
--   - `quditTest`: PDF p.24: accepting effect on exactly 2s copies.
--   - `soundnessConstant`: PDF p.25: exact soundness coefficient.
--   - `CopyTest`: Binary POVM on k physical copies, fixed independently of the input.
--   - `CopyTest.prob`: Born probability from the carried effect and copy count.
--   - `residueQuadratic`: PDF p.27: q, with canonical lifts, including reduction modulo 4 at d=2.
--   - `IsStochasticLagrangian`: PDF p.27: at prime d, cardinality d^t is exactly dimension t.
--   - `Lagrangian`
--   - `relationOperator`: PDF p.27: incidence matrix of the actual subspace.
--   - `tensorRelation`: PDF p.27: r(T) tensor n, regrouped into t blocks of n qudits.
--   - `cliffordCommutant`: Concrete commutant of all Clifford tensor powers.
--   - `commutantCount`: The t-1 factors give an empty product at t=1.
--   - `IsStochasticOrthogonal`: PDF p.34, Definition 4.11.
--   - `StochasticOrthogonal`
--   - `graphRelation`: Graph of a computed linear map.
--   - `perpendicular`: PDF p.36: dot-product annihilator.
--   - `IsDefect`: PDF p.36: isotropy and co-stochasticity are both required.
--   - `leftDefect`: PDF p.37: left kernel.
--   - `rightDefect`: PDF p.37: right kernel.
--   - `defectQuotient`: PDF p.36: N-perp/N as a submodule of the ambient quotient.
--   - `defectClass`: Quotient class of an admissible representative.
--   - `defectRepresentative`: Canonical representative for the phase-independent coset vector.
--   - `DefectIsomorphism`: PDF p.36: invertible linear quotient map preserving q on all representatives and the ones class.
--   - `defectRelationSet`: PDF p.36, (4.17): the actual relation, with quotient direction right to left.
--   - `defectRelation`: Linear span construction, accompanied by exact relation-set equality in the theorem.
--   - `cosetState`: PDF p.39: uniform normalized coset ket.
--   - `cssRelation`: PDF p.39, (4.21): CSS relation with equal defects and identity quotient map.
--   - `cssProjector`: PDF p.39, (4.22): independent Pauli definition of the CSS projector.
--   - `composeRelation`: PDF pp.40--41: relational composition with an existential intermediate vector.
--   - `actedRelation`: PDF p.36: left/right action; the right coordinate uses transpose.
--   - `SameDoubleOrbit`: PDF p.38: concrete double orbit predicate.
--   - `antiPermutation`: PDF p.44: binary anti-permutation matrix.
--   - `phasePointOperator`: PDF p.16, (2.11): phase-space point operator.
--   - `discreteWigner`: PDF p.16, (2.10), real for odd d on pure-state inputs.
--   - `sumNegativity`: PDF p.58: negative mass, not the full l1 norm.
--   - `threeCopyInvolution`: PDF p.61, (8.3): the concrete three-copy involution.
--   - `threeCopyTest`: PDF p.62: accepting effect on three copies.
--   - `stabilizerMoment`: PDF p.45: uniform moment without counting state phases repeatedly.
--   - `momentNormalization`: PDF p.46: Z_{n,d,t}.
--   - `minimalTest`: PDF p.48, (5.11): group-average test independent of the stabilizer span.
--   - `IsOrthogonalProjectionOnto`: Orthogonal projection onto a specified concrete vector subspace.
--   - `stabilizerSpan`: PDF p.48: actual span of stabilizer tensor powers.
--   - `repeatEffect`: Tensor product of r copies of a k-copy effect, flattened to k*r physical copies.
--   - `embeddedLocal`: A constant-size block acting on the k corresponding qudits at physical site j.
--   - `copyPrefixReduction`: Copy-prefix partial trace, reusing the accepted construction with reordered arguments. Its n=0 and s=0 values are scalar traces, not junk defaults.
--   - `compressZero`: Zero-ancilla compression in the physical-qudit coordinates.
--   - `permutationOperator`: Computational permutation of the t blocks.
--   - `IsPermutationSymmetric`: The symmetric-subspace condition is vector invariance.
--   - `embeddedAntiIdentity`: Anti-identity on a specified set of six distinct blocks.
--   - `IsDistributionOn`: Finite probability weights on precisely a named finite set.
--   - `stabilizerMixture`: Convex mixture of s-copy density tensors.
--   - `stabilizerVector`: A representative vector for each phase-free pure stabilizer, with a harmless default off the set.
--   - `stabilizerGram`: PDF p.53: source Gram matrix, built from the canonical state representatives.
--   - `stabilizerFrame`: PDF p.53: the frame operator Q, constructed independently of a Gram bound.
--   - `positivePseudoInverse`: Moore--Penrose inverse of a PSD matrix, with zero inverse defined as zero by cfc.
--   - `rowVectorize`: Source row-stacking vectorization; unlike Matrix.vec it indexes the row first.
--   - `unitaryChoiVector`: Normalized Choi ket, ordered as the output register then the reference register.
--   - `haarMoment`: Finite normalized Haar moment, using the exact permutation formula (5.7), PDF p.47. This is a formula for the Haar integral, not a new distributional hypothesis.
--   - `PauliAction`: One scalar-free Clifford is specified by its conjugation action on the finite Pauli group.
--   - `RealizesAction`: The faithful finite image of the Clifford group modulo scalar phases.
--   - `cliffordActions`: The actual finite normalizer quotient; only realized actions are counted.
--   - `cliffordRepresentative`: Choice of scalar representative has no effect on any density-matrix twirl.
--   - `cliffordMoment`: PDF pp.49--50: uniform Clifford-orbit moment, counted once modulo phases.
--   - `residuePermutation`: PDF p.50: permutation matrix over the residue field.
--   - `transposeRelation`: Transposed relation.
--   - `SameDesignClass`: Definition 6.1: permutation double action plus transposition, not O-double-orbits.
--   - `designClasses`: Distinct equivalence classes are represented as finite subsets, avoiding a chosen enumeration.
--   - `designClassOf`: PDF pp.51--52: actual class containing a specified subspace.
--   - `qutritDefect`: All-ones defect of the qutrit example.
--   - `qutritFourThird`: Third representative printed on PDF p.52, with eight coordinates grouped as left/right.
--   - `qutritFourAnti`: Qutrit anti-identity of (4.35) for t=4; entries 1 on diagonal and 2 elsewhere.
--   - `canonicalDefectMap`: PDF p.37: canonical right-to-left quotient function obtained from the relation itself.
--   - `doubleClasses`: Finite collection of actual double orbits.
--   - `unitaryDistance`: Source average-case distance for unitary testing.
--   - `choiMonomial`: Degree-six Choi tensor monomial, without an irrelevant common normalization.
--   - `cliffordPolynomial`: PDF p.8: actual degree-six anti-identity invariance equations in the entries of U.
--   - `qubitVerificationUnitary`: PDF p.22, (3.11): the source six-copy verification unitary, not the anti-identity surrogate.
--   - `designClassSum`: Class sums R_i from Definition 6.1, independent of a state or its twirl.
--   - `designCoefficients`: The coefficients of the concrete Clifford moment, set to zero off the actual class set. The source stable-range theorem guarantees the expansion; no such guarantee is a hypothesis.
--   - `qutritSymmetricProjector`: Physical symmetric projector on three qutrit blocks.
--   - `qutritAlternatingProjector`: Physical alternating projector on three qutrit blocks.
--   - `qutritCSSProjector`: PDF p.42, (4.29): independent CSS Pauli projector, tensorized over physical sites.
--   - `qutritPieceProjector`: PDF pp.42--43: the four compressed pieces, and one physical standard-S3 multiplicity slice. P_minus is defined by alternating compression, which fixes the printed plus-sign error.
--   - `qutritPiece`: Source physical irreducible carriers, constructed from the five projections.
--   - `IsCliffordInvariant`: Invariance under the actual Clifford tensor-power action.
--   - `IsCliffordIrreducible`: Nonzero irreducible physical Clifford module.
--   - `CliffordModulesEquivalent`: Equivalence means an actual linear bijection intertwining the physical action on the two carriers.
--   - `pieceIndex`: Four one-fold constituents and two copies of the (2,1) constituent.
--   - `QutritDecomposition`
--   - `standardS3`: The standard S3 representation in the basis e0-e2,e1-e2 of the zero-sum plane.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, https://arxiv.org/abs/1712.08628v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P06

/-! Concrete models for arXiv:1712.08628v3. Computational indices are copy-first.
Accepted tensor powers, copy carriers and prefix partial trace are imported.
Cyclic-residue phases and finite quadratic geometry use paper-specific names;
the similarly named frozen continuous-variable objects have different domains. -/

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)
open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF p.14: n qudits in the specified cyclic-residue computational basis. -/
abbrev ResidueRegister (d n : ℕ) := Fin n → ZMod d

/-- PDF p.15: momentum and position labels over ZMod d, also for composite d. -/
abbrev DiscretePhaseSpace (d n : ℕ) := ResidueRegister d n × ResidueRegister d n

/-- PDF p.14: operators indexed by the cyclic computational register. -/
abbrev QuditOperator (d n : ℕ) := Matrix (ResidueRegister d n) (ResidueRegister d n) ℂ

/-- Specialize the accepted copy register to the source cyclic-qudit basis. -/
abbrev QuditCopies (d n t : ℕ) :=
  QAlgorithms.Papers.Independent.Gap48.P20.Copies (ResidueRegister d n) t

/-- PDF p.14: the order of weylPhase. -/
def phaseModulus (d : ℕ) : ℕ := if Even d then 2 * d else d

/-- PDF p.14: omega, with the stray q removed as fixed by the action of Z. -/
def weylRoot (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / (d : ℂ))

/-- PDF p.14: weylPhase includes the parity-dependent sign. -/
def weylPhase (d : ℕ) : ℂ := (-1 : ℂ) ^ d * Complex.exp (Real.pi * Complex.I / (d : ℂ))

/-- PDF pp.14--15, (2.1): canonical lifts and output-row convention for Z^p X^q. -/
def cyclicWeyl (d n : ℕ) [NeZero d] (x : DiscretePhaseSpace d n) : QuditOperator d n :=
  fun a b => if a = b + x.2 then
    (weylPhase d) ^ (-((∑ j, (x.1 j).val * (x.2 j).val : ℕ) : ℤ)) *
      (weylRoot d) ^ (∑ j, (x.1 j).val * (a j).val) else 0

/-- PDF p.15, (2.3), with the source sign. -/
def symplecticBracket {d n : ℕ} (x y : DiscretePhaseSpace d n) : ZMod d :=
  ∑ j, (x.1 j * y.2 j - x.2 j * y.1 j)

/-- PDF pp.14--17: the finite Pauli group, including all powers of weylPhase. -/
def cyclicPauliGroup (d n : ℕ) [NeZero d] : Finset (QuditOperator d n) :=
  ((Finset.range (phaseModulus d)).product (Finset.univ : Finset (DiscretePhaseSpace d n))).image
    (fun a => (weylPhase d) ^ a.1 • cyclicWeyl d n a.2)

/-- PDF p.16: finite Pauli subgroup with no nonidentity scalar. -/
def IsCyclicStabilizerGroup {d n : ℕ} [NeZero d] (G : Finset (QuditOperator d n)) : Prop :=
  G ⊆ cyclicPauliGroup d n ∧ 1 ∈ G ∧
  (∀ A ∈ G, ∀ B ∈ G, A * B ∈ G) ∧ (∀ A ∈ G, Aᴴ ∈ G) ∧
  (∀ A ∈ G, ∀ c : ℂ, A = c • (1 : QuditOperator d n) → c = 1)

/-- PDF p.16, (2.14): code projection before trace normalization. -/
def pauliAverageProjector {d n : ℕ} [NeZero d] (G : Finset (QuditOperator d n)) : QuditOperator d n :=
  (G.card : ℂ)⁻¹ • ∑ P ∈ G, P

/-- PDF p.58 footnote 8: maximally mixed code states, not their convex hull. -/
def mixedStabilizers (d n : ℕ) [NeZero d] : Finset (QuditOperator d n) :=
  (((cyclicPauliGroup d n).powerset.filter IsCyclicStabilizerGroup).image fun G =>
    ((pauliAverageProjector G).trace)⁻¹ • pauliAverageProjector G)

/-- PDF p.17: phase-free pure stabilizer density matrices. -/
def stabilizers (d n : ℕ) [NeZero d] : Finset (QuditOperator d n) :=
  (mixedStabilizers d n).filter fun A => ∃ v : EuclideanSpace ℂ (ResidueRegister d n),
    ‖v‖ = 1 ∧ A = QAlgorithms.pureDensity v

/-- Pure stabilizer predicate; vector phases are immaterial. -/
def IsStabilizer {d n : ℕ} [NeZero d] (v : EuclideanSpace ℂ (ResidueRegister d n)) : Prop :=
  ‖v‖ = 1 ∧ QAlgorithms.pureDensity v ∈ stabilizers d n

/-- Fidelity with a pure state specified by its density matrix. -/
def stabilizerOverlap {d n : ℕ} [NeZero d] (S : QuditOperator d n)
    (v : EuclideanSpace ℂ (ResidueRegister d n)) : ℝ := QAlgorithms.effectProb S (QAlgorithms.pureDensity v)

/-- Source maximum upper bound, pointwise on exactly the finite stabilizer set. -/
def FarFromStabilizers {d n : ℕ} [NeZero d]
    (v : EuclideanSpace ℂ (ResidueRegister d n)) (epsilon : ℝ) : Prop :=
  ∀ S ∈ stabilizers d n, stabilizerOverlap S v ≤ 1 - epsilon ^ 2

/-- PDF p.14: full unitary normalizer, retaining scalar representatives. -/
def IsClifford {d n : ℕ} [NeZero d] (U : QuditOperator d n) : Prop :=
  U ∈ Matrix.unitaryGroup (ResidueRegister d n) ℂ ∧
  (cyclicPauliGroup d n).image (fun P => U * P * Uᴴ) = cyclicPauliGroup d n

/-- PDF p.18, (3.2): characteristic distribution. -/
def characteristicDistribution {d n : ℕ} [NeZero d]
    (v : EuclideanSpace ℂ (ResidueRegister d n)) (x : DiscretePhaseSpace d n) : ℝ :=
  ((d : ℝ) ^ n)⁻¹ * Complex.normSq (inner ℂ v (QAlgorithms.act (cyclicWeyl d n x) v))

/-- PDF p.19: normalized Bell vector (W_x tensor I)|Phi+>. -/
def weylBellVector (n : ℕ) (x : DiscretePhaseSpace 2 n) :
    EuclideanSpace ℂ (ResidueRegister 2 n × ResidueRegister 2 n) :=
  WithLp.toLp 2 (fun a => ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) * cyclicWeyl 2 n x a.1 a.2)

/-- PDF p.19: two Bell measurements and XOR of the labels, on four copies. -/
def bellDifference (n : ℕ) (a : DiscretePhaseSpace 2 n) :
    Matrix (QuditCopies 2 n 4) (QuditCopies 2 n 4) ℂ :=
  fun u v => ∑ x : DiscretePhaseSpace 2 n,
    QAlgorithms.pureDensity (weylBellVector n x) (u 0, u 1) (v 0, v 1) *
    QAlgorithms.pureDensity (weylBellVector n (x + a)) (u 2, u 3) (v 2, v 3)

/-- PDF p.22, (3.11): Algorithm 1, four sampling copies and two verification copies. -/
def qubitTest (n : ℕ) : Matrix (QuditCopies 2 n 6) (QuditCopies 2 n 6) ℂ :=
  fun u v => ∑ a : DiscretePhaseSpace 2 n,
    bellDifference n a (fun i => u ⟨i.val, by omega⟩) (fun i => v ⟨i.val, by omega⟩) *
    (2⁻¹ : ℂ) * ((if (u 4, u 5) = (v 4, v 5) then 1 else 0) +
      cyclicWeyl 2 n a (u 4) (v 4) * (cyclicWeyl 2 n a)ᴴ (u 5) (v 5))

/-- PDF p.22, Remark 3.5: two Bell-sampling and two verification copies. -/
def realQubitTest (n : ℕ) : Matrix (QuditCopies 2 n 4) (QuditCopies 2 n 4) ℂ :=
  fun u v => ∑ a : DiscretePhaseSpace 2 n,
    QAlgorithms.pureDensity (weylBellVector n a) (u 0, u 1) (v 0, v 1) * (2⁻¹ : ℂ) *
    ((if (u 2, u 3) = (v 2, v 3) then 1 else 0) +
      cyclicWeyl 2 n a (u 2) (v 2) * (cyclicWeyl 2 n a)ᴴ (u 3) (v 3))

/-- PDF p.23, (3.15): alternating W and W dagger, with normalization d^{-n}. -/
def quditInvolution (d n s : ℕ) [NeZero d] :
    Matrix (QuditCopies d n (2 * s)) (QuditCopies d n (2 * s)) ℂ :=
  fun u v => ((d : ℂ) ^ n)⁻¹ * ∑ x : DiscretePhaseSpace d n,
    ∏ j : Fin (2 * s), if Even j.val then cyclicWeyl d n x (u j) (v j)
      else (cyclicWeyl d n x)ᴴ (u j) (v j)

/-- PDF p.24: accepting effect on exactly 2s copies. -/
def quditTest (d n s : ℕ) [NeZero d] :
    Matrix (QuditCopies d n (2 * s)) (QuditCopies d n (2 * s)) ℂ :=
  (2⁻¹ : ℂ) • (1 + quditInvolution d n s)

/-- PDF p.25: exact soundness coefficient. -/
def soundnessConstant (d s : ℕ) : ℝ :=
  (1 - (1 - 1 / (4 * (d : ℝ) ^ 2)) ^ (s - 1)) / 2

/-- Binary POVM on k physical copies, fixed independently of the input. -/
structure CopyTest (d n : ℕ) [NeZero d] where
  copies : ℕ
  accept : Matrix (QuditCopies d n copies) (QuditCopies d n copies) ℂ
  effect : QAlgorithms.IsEffect accept

/-- Born probability from the carried effect and copy count. -/
def CopyTest.prob {d n : ℕ} [NeZero d] (A : CopyTest d n)
    (v : EuclideanSpace ℂ (ResidueRegister d n)) : ℝ :=
  QAlgorithms.effectProb A.accept (tensorPower A.copies (QAlgorithms.pureDensity v))

/-- PDF p.27: q, with canonical lifts, including reduction modulo 4 at d=2. -/
def residueQuadratic {d t : ℕ} [NeZero d] (x : ResidueRegister d t) : ZMod (phaseModulus d) :=
  ∑ j, ((x j).val : ZMod (phaseModulus d)) ^ 2

/-- PDF p.27: at prime d, cardinality d^t is exactly dimension t. -/
def IsStochasticLagrangian {d t : ℕ} [NeZero d]
    (T : Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t)) : Prop :=
  (∀ z ∈ T, residueQuadratic z.1 = residueQuadratic z.2) ∧ Nat.card T = d ^ t ∧
    ((fun _ => 1), (fun _ => 1)) ∈ T

abbrev Lagrangian (d t : ℕ) [NeZero d] :=
  {T : Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t) // IsStochasticLagrangian T}

/-- Finite enumeration of source Sigma; no mathematical assumptions added. -/
instance instFintypeLagrangian (d t : ℕ) [NeZero d] : Fintype (Lagrangian d t) := Fintype.ofFinite _

/-- PDF p.27: incidence matrix of the actual subspace. -/
def relationOperator {d t : ℕ} [NeZero d]
    (T : Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t)) : QuditOperator d t :=
  fun x y => if (x, y) ∈ T then 1 else 0

/-- PDF p.27: r(T) tensor n, regrouped into t blocks of n qudits. -/
def tensorRelation {d t : ℕ} [NeZero d] (n : ℕ)
    (T : Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t)) :
    Matrix (QuditCopies d n t) (QuditCopies d n t) ℂ :=
  fun x y => ∏ j : Fin n, relationOperator T (fun i => x i j) (fun i => y i j)

/-- Concrete commutant of all Clifford tensor powers. -/
def cliffordCommutant (d n t : ℕ) [NeZero d] :
    Submodule ℂ (Matrix (QuditCopies d n t) (QuditCopies d n t) ℂ) where
  carrier := {A | ∀ U : QuditOperator d n, IsClifford U →
    A * tensorPower t U = tensorPower t U * A}
  zero_mem' := by simp
  add_mem' := by intro A B hA hB U hU; simp [Matrix.add_mul, Matrix.mul_add, hA U hU, hB U hU]
  smul_mem' := by intro c A hA U hU; simp [Matrix.smul_mul, Matrix.mul_smul, hA U hU]

/-- The t-1 factors give an empty product at t=1. -/
def commutantCount (d t : ℕ) : ℕ := ∏ k ∈ Finset.range (t - 1), (d ^ k + 1)

/-- PDF p.34, Definition 4.11. -/
def IsStochasticOrthogonal {d t : ℕ} [NeZero d]
    (O : Matrix (Fin t) (Fin t) (ZMod d)) : Prop :=
  (∀ x, residueQuadratic (O.mulVec x) = residueQuadratic x) ∧ O.mulVec (fun _ => 1) = (fun _ => 1)

abbrev StochasticOrthogonal (d t : ℕ) [NeZero d] :=
  {O : Matrix (Fin t) (Fin t) (ZMod d) // IsStochasticOrthogonal O}

/-- Finite enumeration of source stochastic isometries. -/
instance instFintypeStochasticOrthogonal (d t : ℕ) [NeZero d] : Fintype (StochasticOrthogonal d t) := Fintype.ofFinite _

/-- Graph of a computed linear map. -/
def graphRelation {d t : ℕ} [NeZero d] (O : Matrix (Fin t) (Fin t) (ZMod d)) :
    Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t) where
  carrier := {z | z.1 = O.mulVec z.2}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change a.1 = O.mulVec a.2 at ha
    change b.1 = O.mulVec b.2 at hb
    change a.1 + b.1 = O.mulVec (a.2 + b.2)
    rw [Matrix.mulVec_add, ha, hb]
  smul_mem' := by
    intro c b hb
    change b.1 = O.mulVec b.2 at hb
    change c • b.1 = O.mulVec (c • b.2)
    rw [Matrix.mulVec_smul, hb]

/-- PDF p.36: dot-product annihilator. -/
def perpendicular {d t : ℕ} (N : Submodule (ZMod d) (ResidueRegister d t)) :
    Submodule (ZMod d) (ResidueRegister d t) where
  carrier := {x | ∀ y ∈ N, dotProduct x y = 0}
  zero_mem' := by simp [dotProduct]
  add_mem' := by
    intro a b ha hb y hy
    change (∑ i, (a i + b i) * y i) = 0
    simp only [add_mul, Finset.sum_add_distrib]
    change dotProduct a y + dotProduct b y = 0
    rw [ha y hy, hb y hy, add_zero]
  smul_mem' := by
    intro c x hx y hy
    change (∑ i, (c * x i) * y i) = 0
    simp only [mul_assoc, ← Finset.mul_sum]
    change c * dotProduct x y = 0
    rw [hx y hy, mul_zero]

/-- PDF p.36: isotropy and co-stochasticity are both required. -/
def IsDefect {d t : ℕ} [NeZero d] (N : Submodule (ZMod d) (ResidueRegister d t)) : Prop :=
  (∀ x ∈ N, residueQuadratic x = 0) ∧ (fun _ => 1) ∈ perpendicular N

/-- PDF p.37: left kernel. -/
def leftDefect {d t : ℕ} (T : Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t)) :
    Submodule (ZMod d) (ResidueRegister d t) := T.comap (LinearMap.inl (ZMod d) _ _)

/-- PDF p.37: right kernel. -/
def rightDefect {d t : ℕ} (T : Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t)) :
    Submodule (ZMod d) (ResidueRegister d t) := T.comap (LinearMap.inr (ZMod d) _ _)

/-- PDF p.36: N-perp/N as a submodule of the ambient quotient. -/
def defectQuotient {d t : ℕ} (N : Submodule (ZMod d) (ResidueRegister d t)) :=
  (perpendicular N).map N.mkQ

/-- Quotient class of an admissible representative. -/
def defectClass {d t : ℕ} (N : Submodule (ZMod d) (ResidueRegister d t))
    (x : ResidueRegister d t) (hx : x ∈ perpendicular N) : defectQuotient N :=
  ⟨N.mkQ x, ⟨x, hx, rfl⟩⟩

/-- Canonical representative for the phase-independent coset vector. -/
def defectRepresentative {d t : ℕ} (N : Submodule (ZMod d) (ResidueRegister d t))
    (x : defectQuotient N) : ResidueRegister d t := Classical.choose x.property

/-- PDF p.36: invertible linear quotient map preserving q on all representatives and the ones class. -/
structure DefectIsomorphism {d t : ℕ} [NeZero d]
    (N M : Submodule (ZMod d) (ResidueRegister d t)) where
  linearEquiv : defectQuotient N ≃ₗ[ZMod d] defectQuotient M
  residueQuadratic : ∀ x hx y hy, linearEquiv (defectClass N x hx) = defectClass M y hy →
    P30.residueQuadratic x = P30.residueQuadratic y
  stochastic : ∀ hx hy,
    linearEquiv (defectClass N (fun _ => 1) hx) = defectClass M (fun _ => 1) hy

/-- PDF p.36, (4.17): the actual relation, with quotient direction right to left. -/
def defectRelationSet {d t : ℕ} [NeZero d] (N M : Submodule (ZMod d) (ResidueRegister d t))
    (J : DefectIsomorphism M N) : Set (ResidueRegister d t × ResidueRegister d t) :=
  {z | ∃ hx : z.1 ∈ perpendicular N, ∃ hy : z.2 ∈ perpendicular M,
    J.linearEquiv (defectClass M z.2 hy) = defectClass N z.1 hx}

/-- Linear span construction, accompanied by exact relation-set equality in the theorem. -/
def defectRelation {d t : ℕ} [NeZero d] (N M : Submodule (ZMod d) (ResidueRegister d t))
    (J : DefectIsomorphism M N) : Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t) :=
  Submodule.span (ZMod d) (defectRelationSet N M J)

/-- PDF p.39: uniform normalized coset ket. -/
def cosetState {d t : ℕ} [NeZero d] (N : Submodule (ZMod d) (ResidueRegister d t))
    (q : defectQuotient N) : EuclideanSpace ℂ (ResidueRegister d t) :=
  WithLp.toLp 2 (fun x => if x - defectRepresentative N q ∈ N then
    ((Real.sqrt (Nat.card N : ℝ))⁻¹ : ℂ) else 0)

/-- PDF p.39, (4.21): CSS relation with equal defects and identity quotient map. -/
def cssRelation {d t : ℕ} (N : Submodule (ZMod d) (ResidueRegister d t)) :
    Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t) where
  carrier := {z | z.1 ∈ perpendicular N ∧ z.2 ∈ perpendicular N ∧ z.1 - z.2 ∈ N}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha, hb, hc⟩ ⟨hd, he, hf⟩
    exact ⟨(perpendicular N).add_mem ha hd, (perpendicular N).add_mem hb he,
      by simpa [add_sub_add_comm] using N.add_mem hc hf⟩
  smul_mem' := by
    rintro c a ⟨ha, hb, hc⟩
    exact ⟨(perpendicular N).smul_mem c ha, (perpendicular N).smul_mem c hb,
      by simpa [smul_sub] using N.smul_mem c hc⟩

/-- PDF p.39, (4.22): independent Pauli definition of the CSS projector. -/
def cssProjector {d t : ℕ} [NeZero d] (N : Submodule (ZMod d) (ResidueRegister d t)) : QuditOperator d t :=
  ((Nat.card N : ℂ) ^ 2)⁻¹ • ∑ p : N, ∑ q : N,
    cyclicWeyl d t (p.val, 0) * cyclicWeyl d t (0, q.val)

/-- PDF pp.40--41: relational composition with an existential intermediate vector. -/
def composeRelation {d t : ℕ}
    (A B : Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t)) :
    Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t) :=
  Submodule.span (ZMod d) {z | ∃ y, (z.1, y) ∈ A ∧ (y, z.2) ∈ B}

/-- PDF p.36: left/right action; the right coordinate uses transpose. -/
def actedRelation {d t : ℕ} (O P : Matrix (Fin t) (Fin t) (ZMod d))
    (T : Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t)) :
    Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t) :=
  Submodule.span (ZMod d) {z | ∃ w ∈ T, z = (O.mulVec w.1, P.transpose.mulVec w.2)}

/-- PDF p.38: concrete double orbit predicate. -/
def SameDoubleOrbit {d t : ℕ} [NeZero d] (T S : Lagrangian d t) : Prop :=
  ∃ O P : StochasticOrthogonal d t, S.val = actedRelation O.val P.val T.val

/-- PDF p.44: binary anti-permutation matrix. -/
def antiPermutation {t : ℕ} (p : Equiv.Perm (Fin t)) : Matrix (Fin t) (Fin t) (ZMod 2) :=
  fun i j => 1 - if i = p j then 1 else 0

/-- PDF p.16, (2.11): phase-space point operator. -/
def phasePointOperator (d n : ℕ) [NeZero d] (x : DiscretePhaseSpace d n) : QuditOperator d n :=
  ((d : ℂ) ^ n)⁻¹ • ∑ y : DiscretePhaseSpace d n,
    (weylRoot d) ^ (-((symplecticBracket x y).val : ℤ)) • (cyclicWeyl d n y)ᴴ

/-- PDF p.16, (2.10), real for odd d on pure-state inputs. -/
def discreteWigner {d n : ℕ} [NeZero d] (v : EuclideanSpace ℂ (ResidueRegister d n))
    (x : DiscretePhaseSpace d n) : ℝ :=
  ((d : ℝ) ^ n)⁻¹ * QAlgorithms.effectProb (phasePointOperator d n x) (QAlgorithms.pureDensity v)

/-- PDF p.58: negative mass, not the full l1 norm. -/
def sumNegativity {d n : ℕ} [NeZero d] (v : EuclideanSpace ℂ (ResidueRegister d n)) : ℝ :=
  ∑ x : DiscretePhaseSpace d n, max 0 (-discreteWigner v x)

/-- PDF p.61, (8.3): the concrete three-copy involution. -/
def threeCopyInvolution (d n : ℕ) [NeZero d] : Matrix (QuditCopies d n 3) (QuditCopies d n 3) ℂ :=
  ((d : ℂ) ^ n)⁻¹ • ∑ x : DiscretePhaseSpace d n, tensorPower 3 (phasePointOperator d n x)

/-- PDF p.62: accepting effect on three copies. -/
def threeCopyTest (d n : ℕ) [NeZero d] : Matrix (QuditCopies d n 3) (QuditCopies d n 3) ℂ :=
  (2⁻¹ : ℂ) • (1 + threeCopyInvolution d n)

/-- PDF p.45: uniform moment without counting state phases repeatedly. -/
def stabilizerMoment (d n t : ℕ) [NeZero d] : Matrix (QuditCopies d n t) (QuditCopies d n t) ℂ :=
  ((stabilizers d n).card : ℂ)⁻¹ • ∑ S ∈ stabilizers d n, tensorPower t S

/-- PDF p.46: Z_{n,d,t}. -/
def momentNormalization (d n t : ℕ) : ℕ :=
  d ^ n * ∏ k ∈ Finset.range (t - 1), (d ^ k + d ^ n)

/-- PDF p.48, (5.11): group-average test independent of the stabilizer span. -/
def minimalTest (d n t : ℕ) [NeZero d] : Matrix (QuditCopies d n t) (QuditCopies d n t) ℂ :=
  (Nat.card (StochasticOrthogonal d t) : ℂ)⁻¹ •
    ∑ O : StochasticOrthogonal d t, tensorRelation n (graphRelation O.val)

/-- Orthogonal projection onto a specified concrete vector subspace. -/
def IsOrthogonalProjectionOnto {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (V : Submodule ℂ (I → ℂ)) : Prop :=
  Pᴴ = P ∧ P * P = P ∧ LinearMap.range (Matrix.toLin' P) = V

/-- PDF p.48: actual span of stabilizer tensor powers. -/
def stabilizerSpan (d n t : ℕ) [NeZero d] : Submodule ℂ (QuditCopies d n t → ℂ) :=
  Submodule.span ℂ {w | ∃ v : EuclideanSpace ℂ (ResidueRegister d n), IsStabilizer v ∧
    w = fun x => QAlgorithms.tensorPow t v x}

/-- Empty tensors are scalars, including the zero-qudit corner. -/
example {I : Type*} (A : Matrix I I ℂ) (x y : Fin 0 → I) : tensorPower 0 A x y = 1 := by
  simp [tensorPower]

/-- Graph incidence agrees with the computational permutation matrix. -/
example {d t : ℕ} [NeZero d] (O : Matrix (Fin t) (Fin t) (ZMod d)) (x y : ResidueRegister d t) :
    relationOperator (graphRelation O) x y = (if x = O.mulVec y then 1 else 0) := by
  simp [relationOperator, graphRelation]

/-- The t=1 product is empty. -/
example (d : ℕ) : commutantCount d 1 = 1 := by simp [commutantCount]

/-- Qubit q takes values modulo four. -/
example : phaseModulus 2 = 4 := by norm_num [phaseModulus]

/-- Tensor product of r copies of a k-copy effect, flattened to k*r physical copies. -/
def repeatEffect {d n k : ℕ} [NeZero d] (r : ℕ)
    (A : Matrix (QuditCopies d n k) (QuditCopies d n k) ℂ) :
    Matrix (QuditCopies d n (k * r)) (QuditCopies d n (k * r)) ℂ :=
  fun x y => ∏ j : Fin r, A
    (fun i => x ⟨j.val * k + i.val, by nlinarith [j.isLt, i.isLt, Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt)]⟩)
    (fun i => y ⟨j.val * k + i.val, by nlinarith [j.isLt, i.isLt, Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.isLt)]⟩)

/-- A constant-size block acting on the k corresponding qudits at physical site j. -/
def embeddedLocal {d n k : ℕ} [NeZero d] (j : Fin n)
    (L : Matrix (QuditCopies d 1 k) (QuditCopies d 1 k) ℂ) :
    Matrix (QuditCopies d n k) (QuditCopies d n k) ℂ :=
  fun x y => if ∀ i l, l ≠ j → x i l = y i l then
    L (fun i _ => x i j) (fun i _ => y i j) else 0

/-- Copy-prefix partial trace, reusing the accepted construction with reordered arguments.
Its n=0 and s=0 values are scalar traces, not junk defaults. -/
def copyPrefixReduction {d n t : ℕ} [NeZero d] (s : ℕ) (hs : s ≤ t)
    (A : Matrix (QuditCopies d n t) (QuditCopies d n t) ℂ) :
    Matrix (QuditCopies d n s) (QuditCopies d n s) ℂ :=
  QAlgorithms.Papers.Independent.Advance50.P30.reduceCopies A s hs

/-- Zero-ancilla compression in the physical-qudit coordinates. -/
def compressZero {d N n t : ℕ} [NeZero d] (hn : n ≤ N)
    (A : Matrix (QuditCopies d N t) (QuditCopies d N t) ℂ) :
    Matrix (QuditCopies d n t) (QuditCopies d n t) ℂ :=
  fun x y => A
    (fun i j => if h : j.val < n then x i ⟨j.val, h⟩ else 0)
    (fun i j => if h : j.val < n then y i ⟨j.val, h⟩ else 0)

/-- Computational permutation of the t blocks. -/
def permutationOperator (d n t : ℕ) [NeZero d] (p : Equiv.Perm (Fin t)) :
    Matrix (QuditCopies d n t) (QuditCopies d n t) ℂ :=
  fun x y => if x = fun i => y (p.symm i) then 1 else 0

/-- The symmetric-subspace condition is vector invariance. -/
def IsPermutationSymmetric {d n t : ℕ} [NeZero d] (v : EuclideanSpace ℂ (QuditCopies d n t)) : Prop :=
  ∀ p : Equiv.Perm (Fin t), QAlgorithms.act (permutationOperator d n t p) v = v

/-- Anti-identity on a specified set of six distinct blocks. -/
def embeddedAntiIdentity {n t : ℕ} (e : Fin 6 ↪ Fin t) :
    Matrix (QuditCopies 2 n t) (QuditCopies 2 n t) ℂ :=
  fun x y => if ∀ i, i ∉ Set.range e → x i = y i then
    quditInvolution 2 n 3 (fun i => x (e i)) (fun i => y (e i)) else 0

/-- Finite probability weights on precisely a named finite set. -/
def IsDistributionOn {I : Type*} (F : Finset I) (p : I → ℝ) : Prop :=
  (∀ i ∈ F, 0 ≤ p i) ∧ ∑ i ∈ F, p i = 1

/-- Convex mixture of s-copy density tensors. -/
def stabilizerMixture {d n : ℕ} [NeZero d] (s : ℕ) (F : Finset (QuditOperator d n))
    (p : QuditOperator d n → ℝ) : Matrix (QuditCopies d n s) (QuditCopies d n s) ℂ :=
  ∑ S ∈ F, (p S : ℂ) • tensorPower s S

/-- A representative vector for each phase-free pure stabilizer, with a harmless default off the set. -/
def stabilizerVector {d n : ℕ} [NeZero d] (S : QuditOperator d n) :
    EuclideanSpace ℂ (ResidueRegister d n) :=
  if h : ∃ v : EuclideanSpace ℂ (ResidueRegister d n), ‖v‖ = 1 ∧ S = QAlgorithms.pureDensity v
  then Classical.choose h else 0

/-- PDF p.53: source Gram matrix, built from the canonical state representatives. -/
def stabilizerGram (d n t : ℕ) [NeZero d] :
    Matrix {S // S ∈ stabilizers d n} {S // S ∈ stabilizers d n} ℂ :=
  fun S T => (inner ℂ (stabilizerVector S.val) (stabilizerVector T.val)) ^ t

/-- PDF p.53: the frame operator Q, constructed independently of a Gram bound. -/
def stabilizerFrame (d n t : ℕ) [NeZero d] : Matrix (QuditCopies d n t) (QuditCopies d n t) ℂ :=
  ∑ S ∈ stabilizers d n, tensorPower t S

/-- Moore--Penrose inverse of a PSD matrix, with zero inverse defined as zero by cfc. -/
def positivePseudoInverse {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) : Matrix I I ℂ := cfc (fun x : ℝ => x⁻¹) A

/-- Source row-stacking vectorization; unlike Matrix.vec it indexes the row first. -/
def rowVectorize {I : Type*} (A : Matrix I I ℂ) : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 (fun x => A x.1 x.2)

/-- Normalized Choi ket, ordered as the output register then the reference register. -/
def unitaryChoiVector (n : ℕ) (U : QuditOperator 2 n) : EuclideanSpace ℂ (ResidueRegister 2 (n + n)) :=
  WithLp.toLp 2 (fun x => ((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℂ) *
    U (fun i => x (Fin.castAdd n i)) (fun i => x (Fin.natAdd n i)))

/-- Finite normalized Haar moment, using the exact permutation formula (5.7), PDF p.47.
This is a formula for the Haar integral, not a new distributional hypothesis. -/
def haarMoment (d n t : ℕ) [NeZero d] : Matrix (QuditCopies d n t) (QuditCopies d n t) ℂ :=
  (∏ k ∈ Finset.range t, ((d : ℂ) ^ n + k))⁻¹ •
    ∑ p : Equiv.Perm (Fin t), permutationOperator d n t p

/-- One scalar-free Clifford is specified by its conjugation action on the finite Pauli group. -/
abbrev PauliAction (d n : ℕ) [NeZero d] :=
  {P // P ∈ cyclicPauliGroup d n} → {P // P ∈ cyclicPauliGroup d n}

/-- The faithful finite image of the Clifford group modulo scalar phases. -/
def RealizesAction {d n : ℕ} [NeZero d] (a : PauliAction d n) (U : QuditOperator d n) : Prop :=
  IsClifford U ∧ ∀ P, U * P.val * Uᴴ = (a P).val

/-- The actual finite normalizer quotient; only realized actions are counted. -/
def cliffordActions (d n : ℕ) [NeZero d] : Finset (PauliAction d n) :=
  Finset.univ.filter fun a => ∃ U, RealizesAction a U

/-- Choice of scalar representative has no effect on any density-matrix twirl. -/
def cliffordRepresentative {d n : ℕ} [NeZero d] (a : PauliAction d n) : QuditOperator d n :=
  if h : ∃ U, RealizesAction a U then Classical.choose h else 1

/-- PDF pp.49--50: uniform Clifford-orbit moment, counted once modulo phases. -/
def cliffordMoment {d n : ℕ} [NeZero d] (t : ℕ)
    (v : EuclideanSpace ℂ (ResidueRegister d n)) : Matrix (QuditCopies d n t) (QuditCopies d n t) ℂ :=
  ((cliffordActions d n).card : ℂ)⁻¹ • ∑ a ∈ cliffordActions d n,
    tensorPower t (QAlgorithms.pureDensity (QAlgorithms.act (cliffordRepresentative a) v))

/-- PDF p.50: permutation matrix over the residue field. -/
def residuePermutation {d t : ℕ} (p : Equiv.Perm (Fin t)) : Matrix (Fin t) (Fin t) (ZMod d) :=
  fun i j => if i = p j then 1 else 0

/-- Transposed relation. -/
def transposeRelation {d t : ℕ} (T : Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t)) :
    Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t) :=
  T.comap (LinearEquiv.prodComm (ZMod d) (ResidueRegister d t) (ResidueRegister d t)).toLinearMap

/-- Definition 6.1: permutation double action plus transposition, not O-double-orbits. -/
def SameDesignClass {d t : ℕ} [NeZero d] (T S : Lagrangian d t) : Prop :=
  ∃ p q : Equiv.Perm (Fin t),
    S.val = actedRelation (residuePermutation p) (residuePermutation q) T.val ∨
    S.val = actedRelation (residuePermutation p) (residuePermutation q) (transposeRelation T.val)

/-- Distinct equivalence classes are represented as finite subsets, avoiding a chosen enumeration. -/
def designClasses (d t : ℕ) [NeZero d] : Finset (Finset (Lagrangian d t)) :=
  Finset.univ.image fun T => Finset.univ.filter (SameDesignClass T)

/-- PDF pp.51--52: actual class containing a specified subspace. -/
def designClassOf {d t : ℕ} [NeZero d]
    (T : Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t)) : Finset (Lagrangian d t) :=
  Finset.univ.filter fun S => ∃ p q : Equiv.Perm (Fin t),
    S.val = actedRelation (residuePermutation p) (residuePermutation q) T ∨
    S.val = actedRelation (residuePermutation p) (residuePermutation q) (transposeRelation T)

/-- All-ones defect of the qutrit example. -/
def qutritDefect : Submodule (ZMod 3) (ResidueRegister 3 3) :=
  Submodule.span (ZMod 3) {(fun _ => 1)}

/-- Third representative printed on PDF p.52, with eight coordinates grouped as left/right. -/
def qutritFourThird : Submodule (ZMod 3) (ResidueRegister 3 4 × ResidueRegister 3 4) :=
  Submodule.span (ZMod 3) (Set.range (fun i : Fin 4 =>
    let A : Matrix (Fin 4) (Fin 8) (ZMod 3) :=
      ![![1,1,1,1,1,1,1,1], ![0,1,2,0,0,2,1,0],
        ![0,0,0,0,1,1,1,0], ![1,1,1,0,0,0,0,0]]
    ((fun j => A i (Fin.castAdd 4 j)), (fun j => A i (Fin.natAdd 4 j)))))

/-- Qutrit anti-identity of (4.35) for t=4; entries 1 on diagonal and 2 elsewhere. -/
def qutritFourAnti : Matrix (Fin 4) (Fin 4) (ZMod 3) :=
  fun i j => if i = j then 1 else 2

/-- Sanity: a zero vector has zero characteristic mass, hence normalization cannot be omitted. -/
example {d n : ℕ} [NeZero d] (x : DiscretePhaseSpace d n) :
    characteristicDistribution (0 : EuclideanSpace ℂ (ResidueRegister d n)) x = 0 := by
  simp [characteristicDistribution, QAlgorithms.act]

/-- Sanity: zero independent repetitions accept as the scalar identity. -/
example {d n k : ℕ} [NeZero d] (A : Matrix (QuditCopies d n k) (QuditCopies d n k) ℂ)
    (x y : QuditCopies d n (k * 0)) : repeatEffect 0 A x y = 1 := by simp [repeatEffect]

/-- Finite enumeration of the concrete defect quotient. -/
instance instFintypeDefectQuotient {d t : ℕ} [NeZero d] (N : Submodule (ZMod d) (ResidueRegister d t)) :
    Fintype (defectQuotient N) := Fintype.ofFinite _

/-- PDF p.37: canonical right-to-left quotient function obtained from the relation itself. -/
def canonicalDefectMap {d t : ℕ} [NeZero d]
    (T : Submodule (ZMod d) (ResidueRegister d t × ResidueRegister d t))
    (q : defectQuotient (rightDefect T)) : defectQuotient (leftDefect T) :=
  let y := defectRepresentative (rightDefect T) q
  if h : ∃ x : ResidueRegister d t, x ∈ perpendicular (leftDefect T) ∧ (x, y) ∈ T then
    defectClass (leftDefect T) (Classical.choose h) (Classical.choose_spec h).1
  else 0

/-- Finite collection of actual double orbits. -/
def doubleClasses (d t : ℕ) [NeZero d] : Finset (Finset (Lagrangian d t)) :=
  Finset.univ.image fun T => Finset.univ.filter (SameDoubleOrbit T)

/-- Source average-case distance for unitary testing. -/
def unitaryDistance {n : ℕ} (U V : QuditOperator 2 n) : ℝ :=
  Real.sqrt (1 - Complex.normSq ((Uᴴ * V).trace / (2 : ℂ) ^ n))

/-- Degree-six Choi tensor monomial, without an irrelevant common normalization. -/
def choiMonomial (n : ℕ) (x : QuditCopies 2 (n + n) 6) :
    MvPolynomial (ResidueRegister 2 n × ResidueRegister 2 n) ℂ :=
  ∏ i : Fin 6, MvPolynomial.X
    ((fun j => x i (Fin.castAdd n j)), (fun j => x i (Fin.natAdd n j)))

/-- PDF p.8: actual degree-six anti-identity invariance equations in the entries of U. -/
def cliffordPolynomial (n : ℕ) (x : QuditCopies 2 (n + n) 6) :
    MvPolynomial (ResidueRegister 2 n × ResidueRegister 2 n) ℂ :=
  (∑ y : QuditCopies 2 (n + n) 6,
    MvPolynomial.C (quditInvolution 2 (n + n) 3 x y) * choiMonomial n y) - choiMonomial n x

/-- PDF p.22, (3.11): the source six-copy verification unitary, not the anti-identity surrogate. -/
def qubitVerificationUnitary (n : ℕ) : Matrix (QuditCopies 2 n 6) (QuditCopies 2 n 6) ℂ :=
  (2 : ℂ) • qubitTest n - 1

/-- Class sums R_i from Definition 6.1, independent of a state or its twirl. -/
def designClassSum {d t : ℕ} [NeZero d] (n : ℕ) (F : Finset (Lagrangian d t)) :
    Matrix (QuditCopies d n t) (QuditCopies d n t) ℂ := ∑ T ∈ F, tensorRelation n T.val

/-- The coefficients of the concrete Clifford moment, set to zero off the actual class set.
The source stable-range theorem guarantees the expansion; no such guarantee is a hypothesis. -/
def designCoefficients {d n t : ℕ} [NeZero d]
    (v : EuclideanSpace ℂ (ResidueRegister d n)) : Finset (Lagrangian d t) → ℝ :=
  if h : ∃ a : Finset (Lagrangian d t) → ℝ,
    (∀ F, F ∉ designClasses d t → a F = 0) ∧
    cliffordMoment t v = ∑ F ∈ designClasses d t, (a F : ℂ) • designClassSum n F
  then Classical.choose h else fun _ => 0

/-- Physical symmetric projector on three qutrit blocks. -/
def qutritSymmetricProjector (n : ℕ) : Matrix (QuditCopies 3 n 3) (QuditCopies 3 n 3) ℂ :=
  (6⁻¹ : ℂ) • ∑ p : Equiv.Perm (Fin 3), permutationOperator 3 n 3 p

/-- Physical alternating projector on three qutrit blocks. -/
def qutritAlternatingProjector (n : ℕ) : Matrix (QuditCopies 3 n 3) (QuditCopies 3 n 3) ℂ :=
  (6⁻¹ : ℂ) • ∑ p : Equiv.Perm (Fin 3),
    (if Equiv.Perm.sign p = 1 then (1 : ℂ) else -1) • permutationOperator 3 n 3 p

/-- PDF p.42, (4.29): independent CSS Pauli projector, tensorized over physical sites. -/
def qutritCSSProjector (n : ℕ) : Matrix (QuditCopies 3 n 3) (QuditCopies 3 n 3) ℂ :=
  fun x y => ∏ j : Fin n, cssProjector qutritDefect (fun i => x i j) (fun i => y i j)

/-- PDF pp.42--43: the four compressed pieces, and one physical standard-S3 multiplicity slice.
P_minus is defined by alternating compression, which fixes the printed plus-sign error. -/
def qutritPieceProjector (n : ℕ) : Fin 5 → Matrix (QuditCopies 3 n 3) (QuditCopies 3 n 3) ℂ :=
  let S := qutritSymmetricProjector n
  let A := qutritAlternatingProjector n
  let P := qutritCSSProjector n
  let plus := S * P * S
  let minus := A * P * A
  ![plus, S - plus, minus, A - minus,
    (2⁻¹ : ℂ) • (1 + permutationOperator 3 n 3 (Equiv.swap 0 1)) - S]

/-- Source physical irreducible carriers, constructed from the five projections. -/
def qutritPiece (n : ℕ) (i : Fin 5) : Submodule ℂ (QuditCopies 3 n 3 → ℂ) :=
  LinearMap.range (Matrix.toLin' (qutritPieceProjector n i))

/-- Invariance under the actual Clifford tensor-power action. -/
def IsCliffordInvariant {d n t : ℕ} [NeZero d] (V : Submodule ℂ (QuditCopies d n t → ℂ)) : Prop :=
  ∀ U : QuditOperator d n, IsClifford U → ∀ v ∈ V, (tensorPower t U).mulVec v ∈ V

/-- Nonzero irreducible physical Clifford module. -/
def IsCliffordIrreducible {d n t : ℕ} [NeZero d] (V : Submodule ℂ (QuditCopies d n t → ℂ)) : Prop :=
  V ≠ ⊥ ∧ IsCliffordInvariant V ∧ ∀ W : Submodule ℂ (QuditCopies d n t → ℂ),
    W ≤ V → IsCliffordInvariant W → W = ⊥ ∨ W = V

/-- Equivalence means an actual linear bijection intertwining the physical action on the two carriers. -/
def CliffordModulesEquivalent {d n t : ℕ} [NeZero d]
    (V W : Submodule ℂ (QuditCopies d n t → ℂ)) : Prop :=
  ∃ L : (QuditCopies d n t → ℂ) →ₗ[ℂ] (QuditCopies d n t → ℂ),
    Set.BijOn L (V : Set _) (W : Set _) ∧
    ∀ U : QuditOperator d n, IsClifford U → ∀ v ∈ V,
      L ((tensorPower t U).mulVec v) = (tensorPower t U).mulVec (L v)

/-- Four one-fold constituents and two copies of the (2,1) constituent. -/
def pieceIndex (i : Fin 6) : Fin 5 := ⟨if i.val < 4 then i.val else 4, by split_ifs <;> omega⟩

abbrev QutritDecomposition (n : ℕ) := (i : Fin 6) → qutritPiece n (pieceIndex i)

/-- The standard S3 representation in the basis e0-e2,e1-e2 of the zero-sum plane. -/
def standardS3 (p : Equiv.Perm (Fin 3)) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if p.symm ⟨i.val, by omega⟩ = ⟨j.val, by omega⟩ then 1
    else if p.symm ⟨i.val, by omega⟩ = 2 then -1 else 0

end QAlgorithms.Papers.Independent.Extend50.P30


