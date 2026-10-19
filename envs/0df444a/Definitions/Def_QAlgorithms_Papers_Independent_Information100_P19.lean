-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19
-- name    : QAlgorithms_Papers_Independent_Information100_P19
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:38:50.539155+00:00
-- url     : https://prove2.me/theorems/c922de9d-40a4-46e9-a0b4-712f77fc2ab6
-- title:
--   Definitions for Optimal entanglement criteria from trace invariants
-- statement:
--   The objects the formalized statements of *Optimal entanglement criteria from trace invariants* (arXiv:2609.29471) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Part`: Partitions with positive parts in decreasing order; PDF p.9.
--   - `Coeff`
--   - `bracket`: A formal partition basis vector, without fixed-dimensional identifications; PDF p.9.
--   - `b1`
--   - `b2`
--   - `b11`
--   - `b3`
--   - `b21`
--   - `b111`
--   - `b31`
--   - `b22`
--   - `b51`
--   - `b33`
--   - `spectralMoments`: Products of ordinary, unnormalized spectral power sums; PDF p.9.
--   - `pairing`: Coefficient pairing, with the nonnegative polar convention; PDF p.10.
--   - `allCone`: Dimension-free all-Hermitian cone in its equivalent spectral formulation; PDF p.9.
--   - `psdCone`: Dimension-free PSD cone, permitting zero eigenvalues; PDF p.12.
--   - `finiteCone`: Finite conic combinations, including the empty combination.
--   - `closedCone`: Closed conic hull: the closure in the ambient finite-coordinate topology; pp.10,20.
--   - `allMom`: Closed all-Hermitian moment cone; PDF pp.9–10.
--   - `psdMom`: Closed PSD moment cone, including dimension-free limits; PDF p.12.
--   - `spectralPolar`: Nonnegative coefficient polar, rather than Mathlib's nonpositive convention; p.10.
--   - `Extreme`: A nonzero generator of an extreme ray of a cone.
--   - `ray`: Nonnegative ray through a vector, including its vertex.
--   - `extremeRays`: The set of extreme rays; pp.10,13.
--   - `IsPolyhedral`: Finite intersections of linear half-spaces.
--   - `cubicRay`: Cubic rank-transition generator; PDF p.13.
--   - `Bip`
--   - `Perms`
--   - `TensorCoeff`
--   - `powerTrace`: Ordinary unnormalized power trace, real on Hermitian inputs; pp.9,28.
--   - `tensorTrace`: Explicit index contraction, with the source's permutation orientation; PDF p.19.
--   - `tensorEval`: Real group-algebra evaluation; PDF p.20.
--   - `sepCone`: Dimension-free separability-valid cone; PDF p.20.
--   - `sepMom`: Closed conic hull of all separable tensor-trace moment vectors; PDF p.20.
--   - `tensorPolar`: Nonnegative polar under the finite tensor coefficient pairing; PDF p.20.
--   - `transposeB`: Partial transpose on B, explicitly fixing the tensor factor; PDF p.21.
--   - `marginalA`: Partial trace over B; PDF p.28.
--   - `marginalB`: Partial trace over A; PDF p.28.
--   - `mass`: Real trace and the two marginal purities; PDF p.28.
--   - `purityA`
--   - `purityB`
--   - `centered`: Homogeneous centered operator; Eq.(14), PDF p.28.
--   - `G`: Squared enhanced-real-ignment threshold; Eq.(15), PDF p.28.
--   - `realign`: Rectangular realignment with A indices as rows and B indices as columns; p.27.
--   - `realignmentSquare`: Square zero extension of rectangular realignment, for the frozen square trace norm. Its singular values are those of realignment together with zeros; PDF pp.27–28.
--   - `rMoment`: Even realignment moment, including zero singular values; PDF p.29.
--   - `eigenSpectrum`: Full Hermitian spectrum as a multiset, retaining multiplicities.
--   - `singularSpectrum`: Singular values from the Gram spectrum; padded with row-space zeros if rectangular.
--   - `canonicalPerm`: Canonical contiguous cycles in decreasing block order; PDF p.21.
--   - `embed`: Diagonal or partial-transpose embedding; coefficients chosen before any input; p.21.
--   - `orbitRel`: Simultaneous conjugation and simultaneous inversion, with no factor exchange; p.22.
--   - `Orbit`
--   - `reduce`: Summation of formal coefficients over each orbit; universal evaluation quotient; p.22.
--   - `orbitEval`: Evaluation of an orbit using a chosen representative; p.22.
--   - `reducedSepCone`: Reduced separability cone in orbit coordinates; pp.22–23.
--   - `IrredChar`: Distinct irreducible characters, independent of a chosen representation basis; p.23.
--   - `quadEval`: The four degree-two quotient coordinates: t², π, πA, πB; PDF p.26.
--   - `quadCone`: Degree-two cone after removing the evaluation kernel; PDF pp.26–27.
--   - `quadGenerators`: The four quotient ray generators in coefficient order (t²,π,πA,πB); p.26.
--   - `K2`: Normalized separable purity triples, before convexification; PDF p.24.
--   - `discreteFeasible`: Actual unit-atom feasibility in Eq.(17), allowing an empty vector for zero data; p.31.
--   - `alpha`: Extended nonnegative optimum: infeasibility has value infinity; Eq.(17), p.31.
--   - `continuousFeasible`: Finite, unnormalized measures supported on [0,1], with explicit integrability; pp.32–33.
--   - `alphaC`: Continuous relaxation, with free finite total mass and infinity on infeasibility; p.32.
--   - `sdpFeasible`: Truncated Hausdorff SDP: matrix sizes m+1 and m, y0 free; PDF p.33.
--   - `sdpValue`: The Hausdorff SDP objective, with extended nonnegative empty-set convention; p.33.
--   - `binomial`: Binomial minorants of sqrt(x), Eq.(21), PDF p.35.
--   - `minorantFeasible`: Weighted feasible polynomials, including the zero constant coefficient; Eq.(23), p.35.
--   - `weightedError`: The actual weighted integral, used only in its integrable beta range; PDF p.51.
--   - `WeightedOptimizer`: Argmin predicate; does not select an unspecified sequence of optimizers; pp.35,51.
--   - `SOS`: A polynomial sum of squares with a finite, unweighted list of square summands.
--   - `sosFeasible`: The Markov–Lukacs certificate with the degree bounds stated in Appendix A; p.51.
--   - `weightedScore`: Linear part of the weighted objective; Eq.(47), p.51.
--   - `outer`: Rank-one outer product.
--   - `rhoC`: Exact two-qubit family of Example 5.2, PDF p.29.
--   - `phi3`: Maximally entangled qutrit vector, normalized in the source; PDF p.42.
--   - `isotropic3`: Noisy qutrit isotropic state in the strictness witness; PDF p.42.
--   - `starVectors`: The four exact vectors of Eq.(45), preserving every sign and basis index; p.46.
--   - `starTransposeVectors`: The four vectors in the partial transpose decomposition; Proposition 6.6, p.46.
--   - `rhoStar`: The exact PPT state rhoStar, not an arbitrary PPT projection; Eq.(45), p.46.
--   - `noisyStar`: White-noise family associated with rhoStar; PDF p.47.
--   - `RankFourProjection`: Hermitian orthogonal projection of rank four, expressed through its linear-map range.
--   - `betaPerm`: Fixed-point-free involutions alpha_m and beta_m, using zero-based indices; p.29.
--   - `alphaPerm`
--   - `tensorBasis`: A single group-algebra coefficient basis element.
--   - `s12`: Degree-four transpositions, with zero-based indices.
--   - `s23`
--   - `s34`
--   - `cycle4`
--   - `wM`: The exact degree-four binomial and pair-sum coefficient vectors; pp.42,44.
--   - `wS`
--   - `wRemainder`
--   - `defect`: Four homogeneous defects P,E,M,S; negative, never zero, means detection; pp.42–43.
--   - `StateUniverse`: States of every positive finite pair of dimensions, as one disjoint union; p.42.
--   - `detection`: Detection sets over the full dimension union; no fixed-dimension non-inclusion claim; p.42.
--   - `interpolationRatio`: Correct fractional exponent version of the interpolation ratio in Proposition 5.11.
--   - `polynomialEval`: Scalar coefficient evaluation without a constant term; Eq.(28), p.37.
-- source:
--   Optimal entanglement criteria from trace invariants, arXiv:2609.29471v1, https://arxiv.org/abs/2609.29471v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

noncomputable section

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder
open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P19

/-- Partitions with positive parts in decreasing order; PDF p.9. -/
def Part (n : ℕ) := {l : List ℕ // l.Pairwise (· ≥ ·) ∧ (∀ k ∈ l, 0 < k) ∧ l.sum = n}

abbrev Coeff (n : ℕ) := Part n →₀ ℝ

/-- A formal partition basis vector, without fixed-dimensional identifications; PDF p.9. -/
def bracket (l : List ℕ) (h : l.Pairwise (· ≥ ·) ∧ ∀ k ∈ l, 0 < k) : Coeff l.sum :=
  Finsupp.single ⟨l, h.1, h.2, rfl⟩ 1

abbrev b1 : Coeff 1 := bracket [1] (by decide)
abbrev b2 : Coeff 2 := bracket [2] (by decide)
abbrev b11 : Coeff 2 := bracket [1,1] (by decide)
abbrev b3 : Coeff 3 := bracket [3] (by decide)
abbrev b21 : Coeff 3 := bracket [2,1] (by decide)
abbrev b111 : Coeff 3 := bracket [1,1,1] (by decide)
abbrev b31 : Coeff 4 := bracket [3,1] (by decide)
abbrev b22 : Coeff 4 := bracket [2,2] (by decide)
abbrev b51 : Coeff 6 := bracket [5,1] (by decide)
abbrev b33 : Coeff 6 := bracket [3,3] (by decide)

/-- Products of ordinary, unnormalized spectral power sums; PDF p.9. -/
def spectralMoments {n d : ℕ} (x : Fin d → ℝ) : Part n → ℝ :=
  fun l => (l.val.map (fun k => ∑ i, x i ^ k)).prod

/-- Coefficient pairing, with the nonnegative polar convention; PDF p.10. -/
def pairing {n : ℕ} (f : Coeff n) (y : Part n → ℝ) : ℝ :=
  f.sum fun l c => c * y l

/-- Dimension-free all-Hermitian cone in its equivalent spectral formulation; PDF p.9. -/
def allCone (n : ℕ) : Set (Coeff n) :=
  {f | ∀ d, 0 < d → ∀ x : Fin d → ℝ, 0 ≤ pairing f (spectralMoments x)}

/-- Dimension-free PSD cone, permitting zero eigenvalues; PDF p.12. -/
def psdCone (n : ℕ) : Set (Coeff n) :=
  {f | ∀ d, 0 < d → ∀ x : Fin d → ℝ, (∀ i, 0 ≤ x i) →
    0 ≤ pairing f (spectralMoments x)}

/-- Finite conic combinations, including the empty combination. -/
def finiteCone {V : Type*} [AddCommMonoid V] [Module ℝ V] (S : Set V) : Set V :=
  {v | ∃ N : ℕ, ∃ c : Fin N → ℝ, ∃ u : Fin N → V,
    (∀ i, 0 ≤ c i ∧ u i ∈ S) ∧ v = ∑ i, c i • u i}

/-- Closed conic hull: the closure in the ambient finite-coordinate topology; pp.10,20. -/
def closedCone {V : Type*} [AddCommMonoid V] [Module ℝ V] [TopologicalSpace V]
    (S : Set V) : Set V := closure (finiteCone S)

/-- Closed all-Hermitian moment cone; PDF pp.9–10. -/
def allMom (n : ℕ) : Set (Part n → ℝ) :=
  closedCone {y | ∃ d, 0 < d ∧ ∃ x : Fin d → ℝ, y = spectralMoments x}

/-- Closed PSD moment cone, including dimension-free limits; PDF p.12. -/
def psdMom (n : ℕ) : Set (Part n → ℝ) :=
  closedCone {y | ∃ d, 0 < d ∧ ∃ x : Fin d → ℝ,
    (∀ i, 0 ≤ x i) ∧ y = spectralMoments x}

/-- Nonnegative coefficient polar, rather than Mathlib's nonpositive convention; p.10. -/
def spectralPolar {n : ℕ} (S : Set (Part n → ℝ)) : Set (Coeff n) :=
  {f | ∀ y ∈ S, 0 ≤ pairing f y}

/-- A nonzero generator of an extreme ray of a cone. -/
def Extreme {V : Type*} [AddCommMonoid V] [Module ℝ V] (C : Set V) (v : V) : Prop :=
  v ≠ 0 ∧ v ∈ C ∧ ∀ u ∈ C, ∀ w ∈ C, u + w = v →
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ u = a • v ∧ w = b • v

/-- Nonnegative ray through a vector, including its vertex. -/
def ray {V : Type*} [AddCommMonoid V] [Module ℝ V] (v : V) : Set V :=
  {w | ∃ c : ℝ, 0 ≤ c ∧ w = c • v}

/-- The set of extreme rays; pp.10,13. -/
def extremeRays {V : Type*} [AddCommMonoid V] [Module ℝ V] (C : Set V) : Set (Set V) :=
  {R | ∃ v, Extreme C v ∧ R = ray v}

/-- Finite intersections of linear half-spaces. -/
def IsPolyhedral {V : Type*} [AddCommGroup V] [Module ℝ V] (C : Set V) : Prop :=
  ∃ N : ℕ, ∃ L : Fin N → V →ₗ[ℝ] ℝ, C = {v | ∀ i, 0 ≤ L i v}

/-- Cubic rank-transition generator; PDF p.13. -/
def cubicRay (k : ℕ) : Coeff 3 :=
  b111 - (2 * (k : ℝ) + 1) • b21 + ((k : ℝ) * (k + 1)) • b3

abbrev Bip (a b : ℕ) := Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ
abbrev Perms (n : ℕ) := Equiv.Perm (Fin n) × Equiv.Perm (Fin n)
abbrev TensorCoeff (n : ℕ) := Perms n → ℝ

/-- Ordinary unnormalized power trace, real on Hermitian inputs; pp.9,28. -/
def powerTrace {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) (k : ℕ) : ℝ :=
  (Matrix.trace (X ^ k)).re

/-- Explicit index contraction, with the source's permutation orientation; PDF p.19. -/
def tensorTrace {n a b : ℕ} (p : Perms n) (X : Bip a b) : ℂ :=
  ∑ i : Fin n → Fin a, ∑ j : Fin n → Fin b,
    ∏ r, X (i r, j r) (i (p.1 r), j (p.2 r))

/-- Real group-algebra evaluation; PDF p.20. -/
def tensorEval {n a b : ℕ} (f : TensorCoeff n) (X : Bip a b) : ℝ :=
  ∑ p, f p * (tensorTrace p X).re

/-- Dimension-free separability-valid cone; PDF p.20. -/
def sepCone (n : ℕ) : Set (TensorCoeff n) :=
  {f | ∀ a b, 0 < a → 0 < b → ∀ X : Bip a b,
    QAlgorithms.Entanglement.IsSeparablePositive X → 0 ≤ tensorEval f X}

/-- Closed conic hull of all separable tensor-trace moment vectors; PDF p.20. -/
def sepMom (n : ℕ) : Set (Perms n → ℝ) :=
  closedCone {y | ∃ a b, 0 < a ∧ 0 < b ∧ ∃ X : Bip a b,
    QAlgorithms.Entanglement.IsSeparablePositive X ∧ y = fun p => (tensorTrace p X).re}

/-- Nonnegative polar under the finite tensor coefficient pairing; PDF p.20. -/
def tensorPolar {n : ℕ} (S : Set (Perms n → ℝ)) : Set (TensorCoeff n) :=
  {f | ∀ y ∈ S, 0 ≤ ∑ p, f p * y p}

/-- Partial transpose on B, explicitly fixing the tensor factor; PDF p.21. -/
def transposeB {a b : ℕ} (X : Bip a b) : Bip a b :=
  fun p q => X (p.1, q.2) (q.1, p.2)

/-- Partial trace over B; PDF p.28. -/
def marginalA {a b : ℕ} (X : Bip a b) : Matrix (Fin a) (Fin a) ℂ :=
  fun i j => ∑ k, X (i,k) (j,k)

/-- Partial trace over A; PDF p.28. -/
def marginalB {a b : ℕ} (X : Bip a b) : Matrix (Fin b) (Fin b) ℂ :=
  fun i j => ∑ k, X (k,i) (k,j)

/-- Real trace and the two marginal purities; PDF p.28. -/
def mass {a b : ℕ} (X : Bip a b) : ℝ := powerTrace X 1

def purityA {a b : ℕ} (X : Bip a b) : ℝ := powerTrace (marginalA X) 2

def purityB {a b : ℕ} (X : Bip a b) : ℝ := powerTrace (marginalB X) 2

/-- Homogeneous centered operator; Eq.(14), PDF p.28. -/
def centered {a b : ℕ} (X : Bip a b) : Bip a b :=
  (mass X : ℂ) • X - Matrix.kronecker (marginalA X) (marginalB X)

/-- Squared enhanced-real-ignment threshold; Eq.(15), PDF p.28. -/
def G {a b : ℕ} (X : Bip a b) : ℝ :=
  (mass X ^ 2 - purityA X) * (mass X ^ 2 - purityB X)

/-- Rectangular realignment with A indices as rows and B indices as columns; p.27. -/
def realign {a b : ℕ} (X : Bip a b) : Matrix (Fin a × Fin a) (Fin b × Fin b) ℂ :=
  fun i j => X (i.1,j.1) (i.2,j.2)

/-- Square zero extension of rectangular realignment, for the frozen square trace norm.
Its singular values are those of realignment together with zeros; PDF pp.27–28. -/
def realignmentSquare {a b : ℕ} (X : Bip a b) :
    Matrix ((Fin a × Fin a) ⊕ (Fin b × Fin b))
      ((Fin a × Fin a) ⊕ (Fin b × Fin b)) ℂ :=
  Matrix.fromBlocks 0 (realign X) 0 0

example {a b : ℕ} (X : Bip a b) (i : Fin a × Fin a) (j : Fin b × Fin b) :
    realignmentSquare X (Sum.inl i) (Sum.inr j) = realign X i j := rfl

/-- Even realignment moment, including zero singular values; PDF p.29. -/
def rMoment {a b : ℕ} (X : Bip a b) (k : ℕ) : ℝ :=
  powerTrace (realign X * (realign X).conjTranspose) k

/-- Full Hermitian spectrum as a multiset, retaining multiplicities. -/
def eigenSpectrum {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) : Multiset ℝ :=
  X.charpoly.roots.map Complex.re

/-- Singular values from the Gram spectrum; padded with row-space zeros if rectangular. -/
def singularSpectrum {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (X : Matrix I J ℂ) : Multiset ℝ :=
  (eigenSpectrum (X * X.conjTranspose)).map Real.sqrt

/-- Canonical contiguous cycles in decreasing block order; PDF p.21. -/
def canonicalPerm {n : ℕ} (l : Part n) : Equiv.Perm (Fin n) :=
  ((l.val.zipIdx).map fun z =>
    ((List.finRange n).filter fun i =>
      (l.val.take z.2).sum ≤ i.val ∧ i.val < (l.val.take z.2).sum + z.1).formPerm).prod

/-- Diagonal or partial-transpose embedding; coefficients chosen before any input; p.21. -/
def embed {n : ℕ} (ppt : Bool) (f : Coeff n) : TensorCoeff n :=
  fun p => f.sum fun l c =>
    if p = (canonicalPerm l, if ppt then (canonicalPerm l)⁻¹ else canonicalPerm l) then c else 0

/-- Simultaneous conjugation and simultaneous inversion, with no factor exchange; p.22. -/
def orbitRel {n : ℕ} (p q : Perms n) : Prop :=
  ∃ g : Equiv.Perm (Fin n),
    q = (g * p.1 * g⁻¹, g * p.2 * g⁻¹) ∨
    q = (g * p.1⁻¹ * g⁻¹, g * p.2⁻¹ * g⁻¹)

abbrev Orbit (n : ℕ) := Quot (@orbitRel n)

/-- Summation of formal coefficients over each orbit; universal evaluation quotient; p.22. -/
def reduce {n : ℕ} (f : TensorCoeff n) : Orbit n →₀ ℝ :=
  open Classical in
  ∑ p, Finsupp.single (Quot.mk orbitRel p) (f p)

/-- Evaluation of an orbit using a chosen representative; p.22. -/
def orbitEval {n a b : ℕ} (q : Orbit n) (X : Bip a b) : ℝ :=
  (tensorTrace q.out X).re

/-- Reduced separability cone in orbit coordinates; pp.22–23. -/
def reducedSepCone (n : ℕ) : Set (Orbit n →₀ ℝ) :=
  {c | ∀ a b, 0 < a → 0 < b → ∀ X : Bip a b,
    QAlgorithms.Entanglement.IsSeparablePositive X →
      0 ≤ c.sum (fun q t => t * orbitEval q X)}

/-- Distinct irreducible characters, independent of a chosen representation basis; p.23. -/
def IrredChar (n : ℕ) := {χ : Equiv.Perm (Fin n) → ℂ //
  ∃ d : ℕ, 0 < d ∧ ∃ ρ : Representation ℂ (Equiv.Perm (Fin n)) (Fin d → ℂ),
    Representation.IsIrreducible ρ ∧ χ = ρ.character}

/-- The four degree-two quotient coordinates: t², π, πA, πB; PDF p.26. -/
def quadEval {a b : ℕ} (c : Fin 4 → ℝ) (X : Bip a b) : ℝ :=
  c 0 * mass X ^ 2 + c 1 * powerTrace X 2 + c 2 * purityA X + c 3 * purityB X

/-- Degree-two cone after removing the evaluation kernel; PDF pp.26–27. -/
def quadCone : Set (Fin 4 → ℝ) :=
  {c | ∀ a b, 0 < a → 0 < b → ∀ X : Bip a b,
    QAlgorithms.Entanglement.IsSeparablePositive X → 0 ≤ quadEval c X}

/-- The four quotient ray generators in coefficient order (t²,π,πA,πB); p.26. -/
def quadGenerators : Fin 4 → Fin 4 → ℝ :=
  ![![0,1,0,0], ![0,-1,1,0], ![0,-1,0,1], ![1,1,-1,-1]]

/-- Normalized separable purity triples, before convexification; PDF p.24. -/
def K2 : Set (Fin 3 → ℝ) :=
  {v | ∃ a b, 0 < a ∧ 0 < b ∧ ∃ X : Bip a b,
    QAlgorithms.Entanglement.IsSeparablePositive X ∧ mass X = 1 ∧
      v = ![powerTrace X 2, purityA X, purityB X]}

/-- Actual unit-atom feasibility in Eq.(17), allowing an empty vector for zero data; p.31. -/
def discreteFeasible {m N : ℕ} (r : Fin m → ℝ) (s : Fin N → ℝ) : Prop :=
  (∀ i, s i ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ k, ∑ i, s i ^ (2 * (k.val + 1)) = r k

/-- Extended nonnegative optimum: infeasibility has value infinity; Eq.(17), p.31. -/
def alpha {m : ℕ} (r : Fin m → ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ N : ℕ, ∃ s : Fin N → ℝ,
    discreteFeasible r s ∧ v = ENNReal.ofReal (∑ i, s i)}

/-- Finite, unnormalized measures supported on [0,1], with explicit integrability; pp.32–33. -/
def continuousFeasible {m : ℕ} (r : Fin m → ℝ) (μ : Measure ℝ) : Prop :=
  μ Set.univ < ∞ ∧ μ (Set.Icc (0 : ℝ) 1)ᶜ = 0 ∧ Integrable (fun x : ℝ => x) μ ∧
  ∀ k, Integrable (fun x : ℝ => x ^ (2 * (k.val + 1))) μ ∧
    (∫ x, x ^ (2 * (k.val + 1)) ∂μ) = r k

/-- Continuous relaxation, with free finite total mass and infinity on infeasibility; p.32. -/
def alphaC {m : ℕ} (r : Fin m → ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ μ : Measure ℝ, continuousFeasible r μ ∧ v = ENNReal.ofReal (∫ x, x ∂μ)}

/-- Truncated Hausdorff SDP: matrix sizes m+1 and m, y0 free; PDF p.33. -/
def sdpFeasible {m : ℕ} (r : Fin m → ℝ) (y : ℕ → ℝ) : Prop :=
  (∀ j ≤ 2*m, 0 ≤ y j) ∧
  (Matrix.of (fun i j : Fin (m+1) => y (i.val+j.val))).PosSemidef ∧
  (Matrix.of (fun i j : Fin m => y (i.val+j.val+1) - y (i.val+j.val+2))).PosSemidef ∧
  ∀ k, y (2*(k.val+1)) = r k

/-- The Hausdorff SDP objective, with extended nonnegative empty-set convention; p.33. -/
def sdpValue {m : ℕ} (r : Fin m → ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ y : ℕ → ℝ, sdpFeasible r y ∧ v = ENNReal.ofReal (y 1)}

/-- Binomial minorants of sqrt(x), Eq.(21), PDF p.35. -/
def binomial (m : ℕ) (x : ℝ) : ℝ :=
  x * ∑ a ∈ Finset.range m,
    ((Nat.factorial (2*a) : ℝ) / (4^a * (Nat.factorial a : ℝ)^2)) * (1-x)^a

/-- Weighted feasible polynomials, including the zero constant coefficient; Eq.(23), p.35. -/
def minorantFeasible (k : ℕ) (h : Polynomial ℝ) : Prop :=
  h.natDegree ≤ k ∧ h.coeff 0 = 0 ∧ h.eval 1 = 1 ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, h.eval x ≤ Real.sqrt x

/-- The actual weighted integral, used only in its integrable beta range; PDF p.51. -/
def weightedError (beta : ℝ) (_h0 : 0 ≤ beta) (_h1 : beta < 3/2)
    (h : Polynomial ℝ) : ℝ :=
  ∫ x in Set.Ioc (0 : ℝ) 1, Real.rpow x (-beta) * (Real.sqrt x - h.eval x)

/-- Argmin predicate; does not select an unspecified sequence of optimizers; pp.35,51. -/
def WeightedOptimizer (k : ℕ) (beta : ℝ) (h : Polynomial ℝ) : Prop :=
  ∃ h0 : 0 ≤ beta, ∃ h1 : beta < 3/2,
    minorantFeasible k h ∧ ∀ g, minorantFeasible k g →
      weightedError beta h0 h1 h ≤ weightedError beta h0 h1 g

/-- A polynomial sum of squares with a finite, unweighted list of square summands. -/
def SOS (q : Polynomial ℝ) : Prop :=
  ∃ N : ℕ, ∃ u : Fin N → Polynomial ℝ, q = ∑ i, u i ^ 2

/-- The Markov–Lukacs certificate with the degree bounds stated in Appendix A; p.51. -/
def sosFeasible (k : ℕ) (h : Polynomial ℝ) : Prop :=
  h.natDegree ≤ k ∧ h.coeff 0 = 0 ∧ h.eval 1 = 1 ∧
  ∃ Q S : Polynomial ℝ, SOS Q ∧ SOS S ∧ Q.natDegree ≤ 2*k ∧ S.natDegree ≤ 2*k-2 ∧
    Polynomial.X - h.comp (Polynomial.X^2) = Q + Polynomial.X * (1-Polynomial.X) * S

/-- Linear part of the weighted objective; Eq.(47), p.51. -/
def weightedScore (k : ℕ) (beta : ℝ) (h : Polynomial ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, h.coeff (j+1) / ((j : ℝ)+2-beta)

/-- Rank-one outer product. -/
def outer {I : Type*} (v : I → ℂ) : Matrix I I ℂ := fun i j => v i * conj (v j)

/-- Exact two-qubit family of Example 5.2, PDF p.29. -/
def rhoC (c : ℝ) : Bip 2 2 :=
  let vp := (Real.sqrt 2 : ℂ)⁻¹ • ((WithLp.ofLp (QAlgorithms.ket (ι := Fin 2 × Fin 2) (0, 1))) + (WithLp.ofLp (QAlgorithms.ket (ι := Fin 2 × Fin 2) (1, 0))))
  let vm := (Real.sqrt 2 : ℂ)⁻¹ • ((WithLp.ofLp (QAlgorithms.ket (ι := Fin 2 × Fin 2) (0, 1))) - (WithLp.ofLp (QAlgorithms.ket (ι := Fin 2 × Fin 2) (1, 0))))
  (1/2 : ℂ) • outer ((WithLp.ofLp (QAlgorithms.ket (ι := Fin 2 × Fin 2) (0, 0)))) + ((1+2*c)/4 : ℂ) • outer vp +
    ((1-2*c)/4 : ℂ) • outer vm

/-- Maximally entangled qutrit vector, normalized in the source; PDF p.42. -/
def phi3 : Fin 3 × Fin 3 → ℂ :=
  fun p => if p.1 = p.2 then (Real.sqrt 3 : ℂ)⁻¹ else 0

/-- Noisy qutrit isotropic state in the strictness witness; PDF p.42. -/
def isotropic3 (p : ℝ) : Bip 3 3 :=
  (p : ℂ) • outer phi3 + (((1-p)/9 : ℝ) : ℂ) • 1

/-- The four exact vectors of Eq.(45), preserving every sign and basis index; p.46. -/
def starVectors : Fin 4 → (Fin 3 × Fin 3 → ℂ) :=
  let s := (Real.sqrt 2 : ℂ)
  let t := (Real.sqrt 3 : ℂ)⁻¹
  ![t • ((WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (0, 0))) + s • (WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (2, 1)))), t • ((WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (0, 1))) + s • (WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (1, 2)))),
    t • (s • (WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (0, 2))) - (WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (1, 0)))), t • ((WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (1, 1))) - s • (WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (2, 0))))]

/-- The four vectors in the partial transpose decomposition; Proposition 6.6, p.46. -/
def starTransposeVectors : Fin 4 → (Fin 3 × Fin 3 → ℂ) :=
  let s := (Real.sqrt 2 : ℂ)
  let t := (Real.sqrt 3 : ℂ)⁻¹
  ![t • ((WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (0, 1))) + s • (WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (2, 0)))), t • (s • (WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (0, 2))) + (WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (1, 1)))),
    t • ((WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (0, 0))) - s • (WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (1, 2)))), t • ((WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (1, 0))) - s • (WithLp.ofLp (QAlgorithms.ket (ι := Fin 3 × Fin 3) (2, 1))))]

/-- The exact PPT state rhoStar, not an arbitrary PPT projection; Eq.(45), p.46. -/
def rhoStar : Bip 3 3 := (1/4 : ℂ) • ∑ k, outer (starVectors k)

/-- White-noise family associated with rhoStar; PDF p.47. -/
def noisyStar (p : ℝ) : Bip 3 3 :=
  (p : ℂ) • rhoStar + (((1-p)/9 : ℝ) : ℂ) • 1

/-- Hermitian orthogonal projection of rank four, expressed through its linear-map range. -/
def RankFourProjection {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℂ) : Prop :=
  P.IsHermitian ∧ P*P = P ∧ Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) = 4

/-- Fixed-point-free involutions alpha_m and beta_m, using zero-based indices; p.29. -/
def betaPerm (m : ℕ) : Equiv.Perm (Fin (2*m)) :=
  ((List.range m).map fun j =>
    ((List.finRange (2*m)).filter fun i => i.val = 2*j ∨ i.val = 2*j+1).formPerm).prod

def alphaPerm (m : ℕ) : Equiv.Perm (Fin (2*m)) :=
  (((List.finRange (2*m)).filter fun i => i.val = 0 ∨ i.val+1 = 2*m).formPerm) *
    ((List.range (m-1)).map fun j =>
      ((List.finRange (2*m)).filter fun i => i.val = 2*j+1 ∨ i.val = 2*j+2).formPerm).prod

/-- A single group-algebra coefficient basis element. -/
def tensorBasis {n : ℕ} (p : Perms n) : TensorCoeff n := fun q => if q=p then 1 else 0

/-- Degree-four transpositions, with zero-based indices. -/
def s12 : Equiv.Perm (Fin 4) := Equiv.swap 0 1

def s23 : Equiv.Perm (Fin 4) := Equiv.swap 1 2

def s34 : Equiv.Perm (Fin 4) := Equiv.swap 2 3

def cycle4 : Equiv.Perm (Fin 4) := ([0,1,2,3] : List (Fin 4)).formPerm

/-- The exact degree-four binomial and pair-sum coefficient vectors; pp.42,44. -/
def wM : TensorCoeff 4 := tensorBasis (1,1) - (3/2 : ℝ) • tensorBasis (s12,s12) +
  (1/2 : ℝ) • tensorBasis (alphaPerm 2,betaPerm 2)

def wS : TensorCoeff 4 := tensorBasis (1,1) - (2 : ℝ) • tensorBasis (s12,s12) -
  tensorBasis (s12*s34,s12*s34) + (2 : ℝ) • tensorBasis (alphaPerm 2,betaPerm 2)

def wRemainder : TensorCoeff 4 := (3 : ℝ) • tensorBasis (1,1) -
  (4 : ℝ) • tensorBasis (s12,s12) + tensorBasis (s12*s34,s12*s34)

/-- Four homogeneous defects P,E,M,S; negative, never zero, means detection; pp.42–43. -/
def defect {a b : ℕ} (j : Fin 4) (X : Bip a b) : ℝ :=
  (![mass X * powerTrace (transposeB X) 3 - powerTrace (transposeB X) 2 ^ 2,
    G X - rMoment (centered X) 1,
    mass X ^ 4 - (3/2 : ℝ)*mass X^2*rMoment X 1 + (1/2 : ℝ)*rMoment X 2,
    (mass X^2-rMoment X 1)^2 - 2*(rMoment X 1^2-rMoment X 2)] : Fin 4 → ℝ) j

/-- States of every positive finite pair of dimensions, as one disjoint union; p.42. -/
def StateUniverse := Σ a : ℕ, Σ b : ℕ,
  {X : Bip a b // 0 < a ∧ 0 < b ∧ X.PosSemidef ∧ mass X = 1}

/-- Detection sets over the full dimension union; no fixed-dimension non-inclusion claim; p.42. -/
def detection (j : Fin 4) : Set StateUniverse :=
  {s | defect j s.2.2.val < 0}

/-- Correct fractional exponent version of the interpolation ratio in Proposition 5.11. -/
def interpolationRatio {N : ℕ} (s : Fin N → ℝ) (a b : ℕ) : ℝ :=
  Real.rpow (∑ i, |s i|^(2*a)) ((((2*b : ℕ) : ℝ)-1)/((b:ℝ)-a)) /
    Real.rpow (∑ i, |s i|^(2*b)) ((((2*a : ℕ) : ℝ)-1)/((b:ℝ)-a))

/-- Scalar coefficient evaluation without a constant term; Eq.(28), p.37. -/
def polynomialEval {m : ℕ} (p : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ k, p k * x^(k.val+1)

example {a b : ℕ} (X : Bip a b) : transposeB (transposeB X) = X := rfl

example : finiteCone (∅ : Set ℝ) = {0} := by
  ext v
  constructor
  · rintro ⟨N,c,u,h,rfl⟩
    have hz : N = 0 := by
      by_contra hn
      exact (h ⟨0, Nat.pos_of_ne_zero hn⟩).2
    subst N
    simp
  · rintro rfl
    exact ⟨0, Fin.elim0, Fin.elim0, by simp, by simp⟩

example {a b : ℕ} (X : Bip a b) (i j : Fin a) :
    realign X (i,j) = fun k => X (i,k.1) (j,k.2) := rfl

example : binomial 1 (0 : ℝ) = 0 := by simp [binomial]

example : binomial 1 (1 : ℝ) = 1 := by simp [binomial]

end QAlgorithms.Papers.Independent.Information100.P19


