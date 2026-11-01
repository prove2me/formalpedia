-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P60
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P60
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T06:50:32.816994+00:00
-- url     : https://prove2.me/theorems/b2673d1b-2df3-4e60-bda6-5802833b3e81
-- title:
--   Definitions for Remarks on additivity of the Holevo channel capacity and of the entanglement of formation
-- statement:
--   The objects the formalized statements of *Remarks on additivity of the Holevo channel capacity and of the entanglement of formation* (arXiv:quant-ph/0206148) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `pureEntropyBits`: PDF p.3: entropy in bits of the first-party marginal of a pure vector. Physical vector arguments are normalized in the theorem or imported ensemble.
--   - `finiteBasisState`: PDF p.3: change only the local basis labels to the accepted finite-dimensional operational cost interface. The same bijection is used in both matrix indices.
--   - `formationCostBits`: PDF p.3: operational entanglement cost in singlets per copy, with half trace norm error. Reuse the accepted actual finite adaptive two-way LOCC definition; local basis relabelling accommodates all finite registers, including direct sums.
--   - `HasRangeIn`: PDF p.4: support means every matrix column belongs to the stated linear subspace.
--   - `dilationSpace`: PDF pp.4,9--13: range of the actual displayed embedding, as the span of its columns.
--   - `SignalEnsemble`: PDF pp.2,5--6: a finite ensemble on an arbitrary input Hilbert space.
--   - `FiniteOutputDualChannel`: PDF pp.2,5--6: unital completely positive dual channel, with no finite input assumption. Complete positivity uses all positive block matrices and all test vectors.
--   - `pureOutput`: PDF p.6: actual pure output; Tr(rho E_ji)=rho_ij fixes the transposition.
--   - `signalBarycenter`: PDF pp.2,6: output barycenter of an input ensemble.
--   - `signalHolevo`: PDF p.2, (1): Holevo objective, in bits. Only normalized physical signals are used.
--   - `signalCapacity`: PDF p.2, (1): the actual finite-ensemble supremum. With positive finite output and an attaining ensemble it is nonempty and bounded between zero and log2(output dim).
--   - `completedOperator`: Canonical bounded-operator extension to the Hilbert completion; its embedding is isometric and dense, so ContinuousLinearMap.extend never takes its junk branch.
--   - `tensorDualOutput`: PDF p.6, (9): tensor channel on the completed Hilbert tensor product. This formula uses the actual tensor product of each pair of dual matrix units, and includes arbitrary infinite-Schmidt-rank inputs through completion, not merely algebraic simple tensors.
--   - `PauliAdmissible`: PDF p.9, (13): the closed weight simplex and both axis-order inequalities.
--   - `pauliDilation`: PDF p.9: columns are exactly psi_T and psi_T_perp, output:environment order. The y-column phases are +i and -i, and the second z coefficient is negative.
--   - `pauliMixture`: PDF p.9, (14): mixtures of the two specified projectors; endpoints are allowed.
--   - `pauliDilationWord`: PDF p.9: a named tensor word, regrouped across the party cut.
--   - `pauliWordMixture`: PDF p.9: an arbitrary convex mixture of the named tensor-word projectors.
--   - `gapPolynomial`: PDF p.14: the exact quartic, with no total negative-root selector.
--   - `GapCriterion`: PDF p.14, (20): the entire numerator 2^h-1 is negated before division by two.
--   - `DepolarizingData`: PDF p.10: physical parameter and the source's orthogonal unitary error basis.
--   - `depolarizingWeight`: PDF p.10: p0=lambda+(1-lambda)/d^2, all other weights equal.
--   - `depolarizingDilation`: PDF p.10: the actual Kraus-block embedding, in output:environment order.
--   - `depolarizingEntropyBits`: PDF p.10: entropy of the printed spectrum (a,b,...,b), including zero eigenvalues.
--   - `productMatrices`: Grouped tensor product of a list of local density matrices.
--   - `productMixture`: PDF p.10: finite convex mixtures of supported product states, not arbitrary entangled states in the tensor-power subspace.
--   - `jointDepolarizing`: PDF p.8: tensor of the specified dilation maps, allowing different local dimensions.
--   - `pairMarginal`: PDF p.8: the actual ith pair marginal, summing the remaining coordinates once. The update changes only coordinate i in the column; all other registers are traced.
--   - `IrreducibleMatrix`: PDF p.11: irreducibility on exactly the represented space.
--   - `CovariantData`: PDF p.11, (15): compact continuous unitary actions on K and H2, both irreducible. W is the actual isometry into environment:output. Covariance is imposed on all input operators; no twirling identity, optimum, or product-case action is a hypothesis.
--   - `projectorState`: PDF p.11: P/Tr(P), constructed from W, whose rank and trace are k>0.
--   - `embedded`: PDF p.11: embed a source vector using the actual isometry.
--   - `minimumEntanglement`: PDF p.11, (17): minimum-entropy value over unit vectors, not all vectors of K. The result below also asserts attainment, so the printed minimum is retained.
--   - `dilationHolevo`: PDF p.11: finite-input Holevo objective for the channel defined by W and traceLeft.
--   - `dilationCapacity`: PDF p.11, (16): actual channel capacity (1), with unit normalized inputs.
--   - `minimizingProjectorHull`: PDF pp.11--12: convex hull of the orbit of the minimizing pure projector. This is a convex hull of density matrices, not their linear support span.
--   - `PureTransitive`: PDF p.12: transitivity on pure projectors, thus insensitive to global phase.
--   - `exampleSevenDilation`: PDF p.13, Example 7: the three displayed orthonormal columns. j+3 is an ordinary environment coordinate (3,4,5), not a residue modulo three.
--   - `exampleSevenMixtureDilation`: PDF p.13: coherent superposition in C3 tensor (C6 direct-sum (C3 tensor C3)). The right branch is |Phi_3> tensor |j>; no incoherent flag replaces the direct sum.
--   - `exampleSevenMixtureEntropy`: PDF p.13: explicit constant from the spectrum of the printed channel. a=(1-|c|^2)/3+|c|^2/2, b=(1-|c|^2)/3+|c|^2/4, spectrum (a,b,b).
--   - `antisymmetricDilation`: PDF p.13, Example 8: the specified normalized antisymmetric basis wedges.
-- source:
--   Remarks on additivity of the Holevo channel capacity and of the entanglement of formation, arXiv:quant-ph/0206148v4, https://arxiv.org/abs/quant-ph/0206148v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P42
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32

/-!
Matsumoto--Shimono--Winter, arXiv:quant-ph/0206148v4.
Accepted interfaces are imported; paper-specific adapters have complete bodies.
Only result statements have sorry.
Entropy and operational rates are in bits. Compilation is pending batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P60

open scoped Matrix ComplexConjugate ComplexOrder TensorProduct

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix, normalized ensemble, convex roof, grouped copies and LOCC.
open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)
open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble pureAverage formation)
open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)
open QAlgorithms.Papers.Independent.Gap48.P32 (twoWayDistillable)

/-- PDF p.3: entropy in bits of the first-party marginal of a pure vector.
Physical vector arguments are normalized in the theorem or imported ensemble. -/
def pureEntropyBits {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (v : EuclideanSpace ℂ (A × B)) : ℝ := vnEntropy (traceRight (pureDensity v))

/-- PDF p.3: change only the local basis labels to the accepted finite-dimensional
operational cost interface. The same bijection is used in both matrix indices. -/
def finiteBasisState {A B : Type*} [Fintype A] [Fintype B]
    (rho : Op (A × B)) : Op (Fin (Fintype.card A) × Fin (Fintype.card B)) :=
  fun p q => rho ((Fintype.equivFin A).symm p.1, (Fintype.equivFin B).symm p.2)
    ((Fintype.equivFin A).symm q.1, (Fintype.equivFin B).symm q.2)

/-- PDF p.3: operational entanglement cost in singlets per copy, with half trace
norm error. Reuse the accepted actual finite adaptive two-way LOCC definition;
local basis relabelling accommodates all finite registers, including direct sums. -/
def formationCostBits {A B : Type*} [Fintype A] [Fintype B]
    (rho : Op (A × B)) : ℝ :=
  QAlgorithms.Papers.Independent.Dependency50.P42.entanglementCost
    QAlgorithms.Papers.Independent.Dependency50.P42.halfTraceDistance (finiteBasisState rho)

/-- The cost adapter changes basis labels without changing any matrix entry. -/
example {A B : Type*} [Fintype A] [Fintype B] (rho : Op (A × B))
    (p q : Fin (Fintype.card A) × Fin (Fintype.card B)) :
    finiteBasisState rho p q =
      rho ((Fintype.equivFin A).symm p.1, (Fintype.equivFin B).symm p.2)
        ((Fintype.equivFin A).symm q.1, (Fintype.equivFin B).symm q.2) := rfl

/-- PDF p.4: support means every matrix column belongs to the stated linear subspace. -/
def HasRangeIn {I : Type*} (K : Submodule ℂ (I → ℂ)) (rho : Op I) : Prop :=
  ∀ j, (fun i => rho i j) ∈ K

/-- PDF pp.4,9--13: range of the actual displayed embedding, as the span of its columns. -/
def dilationSpace {I J : Type*} (W : Matrix I J ℂ) : Submodule ℂ (I → ℂ) :=
  Submodule.span ℂ (Set.range fun j => fun i => W i j)

/-- Normalization sanity for the finite roof, not a proof of a source theorem. -/
example {I : Type} [Fintype I] (v : EuclideanSpace ℂ I) (hv : ‖v‖ = 1) :
    ∃ e : PureEnsemble I, pureAverage e = pureDensity v := by
  refine ⟨⟨1, fun _ => 1, fun _ => v, fun _ => by norm_num, by simp,
    fun _ => hv⟩, ?_⟩
  simp [pureAverage]

/-- Zero copies are the scalar trace-one operator, without a division by zero. -/
example {A B : Type*} (rho : Op (A × B))
    (x y : (Fin 0 → A) × (Fin 0 → B)) : groupedPower rho 0 x y = 1 := by
  simp [groupedPower]

/-- The protocol class includes the identity without spending entanglement. -/
example (a b : ℕ) : FiniteLOCC (fun X : Op (Fin a × Fin b) => X) :=
  FiniteLOCC.identity a b

/-! General Hilbert input, finite output: Heisenberg-picture normal channels.
The domain algebra is finite dimensional, so positivity at all matrix levels and
unitality specify precisely the adjoint of a trace-preserving completely positive
Schrodinger channel on all trace-class input states. No input dimension restriction. -/

/-- PDF pp.2,5--6: a finite ensemble on an arbitrary input Hilbert space. -/
structure SignalEnsemble (H : Type*) [NormedAddCommGroup H] where
  size : ℕ
  prob : Fin size → ℝ
  vector : Fin size → H
  nonneg : ∀ j, 0 ≤ prob j
  total : ∑ j, prob j = 1
  unit : ∀ j, ‖vector j‖ = 1

/-- PDF pp.2,5--6: unital completely positive dual channel, with no finite input
assumption. Complete positivity uses all positive block matrices and all test vectors. -/
structure FiniteOutputDualChannel (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (d : ℕ) where
  dual : Op (Fin d) →ₗ[ℂ] (H →L[ℂ] H)
  unital : dual 1 = ContinuousLinearMap.id ℂ H
  completely_positive : ∀ k : ℕ, ∀ X : Op (Fin k × Fin d), X.PosSemidef →
    ∀ v : Fin k → H,
      0 ≤ ∑ r, ∑ s, inner ℂ (v r)
        (dual (fun i j => X (r, i) (s, j)) (v s))

/-- PDF p.6: actual pure output; Tr(rho E_ji)=rho_ij fixes the transposition. -/
def pureOutput {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {d : ℕ} (T : FiniteOutputDualChannel H d) (v : H) : Op (Fin d) :=
  fun i j => inner ℂ v (T.dual (Matrix.single j i 1) v)

/-- PDF pp.2,6: output barycenter of an input ensemble. -/
def signalBarycenter {H I : Type*} [NormedAddCommGroup H]
    (signal : H → Op I) (e : SignalEnsemble H) : Op I :=
  ∑ j, (e.prob j : ℂ) • signal (e.vector j)

/-- PDF p.2, (1): Holevo objective, in bits. Only normalized physical signals are used. -/
def signalHolevo {H I : Type*} [NormedAddCommGroup H] [Fintype I] [DecidableEq I]
    (signal : H → Op I) (e : SignalEnsemble H) : ℝ :=
  vnEntropy (signalBarycenter signal e) - ∑ j, e.prob j * vnEntropy (signal (e.vector j))

/-- PDF p.2, (1): the actual finite-ensemble supremum. With positive finite output and
an attaining ensemble it is nonempty and bounded between zero and log2(output dim). -/
def signalCapacity {H I : Type*} [NormedAddCommGroup H] [Fintype I] [DecidableEq I]
    (signal : H → Op I) : ℝ := sSup (Set.range (signalHolevo signal))

/-- Canonical bounded-operator extension to the Hilbert completion; its embedding
is isometric and dense, so ContinuousLinearMap.extend never takes its junk branch. -/
def completedOperator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : E →L[ℂ] E) : UniformSpace.Completion E →L[ℂ] UniformSpace.Completion E :=
  ((UniformSpace.Completion.toComplL : E →L[ℂ] UniformSpace.Completion E).comp f).extend
    (UniformSpace.Completion.toComplL : E →L[ℂ] UniformSpace.Completion E)

/-- PDF p.6, (9): tensor channel on the completed Hilbert tensor product. This formula
uses the actual tensor product of each pair of dual matrix units, and includes arbitrary
infinite-Schmidt-rank inputs through completion, not merely algebraic simple tensors. -/
def tensorDualOutput {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] {d e : ℕ}
    (T : FiniteOutputDualChannel H d) (S : FiniteOutputDualChannel K e)
    (v : UniformSpace.Completion (H ⊗[ℂ] K)) : Op (Fin d × Fin e) :=
  fun i j => inner ℂ v (completedOperator
    (TensorProduct.mapL (T.dual (Matrix.single j.1 i.1 1))
      (S.dual (Matrix.single j.2 i.2 1))) v)

/-- PDF p.9, (13): the closed weight simplex and both axis-order inequalities. -/
def PauliAdmissible (p : Fin 4 → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
    |p 0 + p 2 - p 1 - p 3| ≤ p 0 + p 3 - p 1 - p 2 ∧
    |p 0 + p 1 - p 2 - p 3| ≤ p 0 + p 3 - p 1 - p 2

/-- PDF p.9: columns are exactly psi_T and psi_T_perp, output:environment order.
The y-column phases are +i and -i, and the second z coefficient is negative. -/
def pauliDilation (p : Fin 4 → ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2) ℂ :=
  fun q j =>
    if q.2 = 0 then if q.1 = j then (Real.sqrt (p 0) : ℂ) else 0
    else if q.2 = 1 then if q.1 ≠ j then (Real.sqrt (p 1) : ℂ) else 0
    else if q.2 = 2 then if q.1 ≠ j then
      (if j = 0 then Complex.I else -Complex.I) * (Real.sqrt (p 2) : ℂ) else 0
    else if q.1 = j then
      (if j = 0 then (1 : ℂ) else -1) * (Real.sqrt (p 3) : ℂ) else 0

/-- PDF p.9, (14): mixtures of the two specified projectors; endpoints are allowed. -/
def pauliMixture (p : Fin 4 → ℝ) (s : ℝ) : Op (Fin 2 × Fin 4) :=
  (s : ℂ) • pureDensity (WithLp.toLp 2 fun q => pauliDilation p q 0) +
    ((1 - s : ℝ) : ℂ) • pureDensity (WithLp.toLp 2 fun q => pauliDilation p q 1)

/-- PDF p.9: a named tensor word, regrouped across the party cut. -/
def pauliDilationWord (p : Fin 4 → ℝ) (n : ℕ) (w : Fin n → Fin 2) :
    EuclideanSpace ℂ ((Fin n → Fin 2) × (Fin n → Fin 4)) :=
  WithLp.toLp 2 fun q => ∏ i, pauliDilation p (q.1 i, q.2 i) (w i)

/-- PDF p.9: an arbitrary convex mixture of the named tensor-word projectors. -/
def pauliWordMixture (p : Fin 4 → ℝ) (n : ℕ) (mu : (Fin n → Fin 2) → ℝ) :
    Op ((Fin n → Fin 2) × (Fin n → Fin 4)) :=
  ∑ w, (mu w : ℂ) • pureDensity (pauliDilationWord p n w)

/-- PDF p.14: the exact quartic, with no total negative-root selector. -/
def gapPolynomial (p : Fin 4 → ℝ) (z : ℝ) : ℝ :=
  z ^ 4 - z ^ 3 + 4 * (p 0 * p 1 * p 2 + p 0 * p 1 * p 3 +
    p 0 * p 2 * p 3 + p 1 * p 2 * p 3) * z - 16 * p 0 * p 1 * p 2 * p 3

/-- PDF p.14, (20): the entire numerator 2^h-1 is negated before division by two. -/
def GapCriterion (p : Fin 4 → ℝ) : Prop :=
  0 < gapPolynomial p (-(((2 : ℝ) ^ binEntropy2 (p 0 + p 3) - 1) / 2))

/-- The y-phase and perpendicular z-sign are pinned directly at matrix entries. -/
example (p : Fin 4 → ℝ) :
    pauliDilation p (1, 2) 0 = Complex.I * (Real.sqrt (p 2) : ℂ) ∧
    pauliDilation p (0, 2) 1 = -Complex.I * (Real.sqrt (p 2) : ℂ) ∧
    pauliDilation p (1, 3) 1 = -(Real.sqrt (p 3) : ℂ) := by
  norm_num [pauliDilation, Fin.ext_iff]

/-- Quartic boundary check: the allowed identity channel has no negative root. -/
example (z : ℝ) : gapPolynomial ![1, 0, 0, 0] z = z ^ 4 - z ^ 3 := by
  change z ^ 4 - z ^ 3 +
    4 * (1 * 0 * 0 + 1 * 0 * 0 + 1 * 0 * 0 + 0 * 0 * 0) * z -
    16 * 1 * 0 * 0 * 0 = z ^ 4 - z ^ 3
  ring

/-! General depolarizing subspaces. -/

/-- PDF p.10: physical parameter and the source's orthogonal unitary error basis. -/
structure DepolarizingData (d : ℕ) where
  dimension : 2 ≤ d
  parameter : ℝ
  lower : -1 / ((d : ℝ) ^ 2 - 1) ≤ parameter
  upper : parameter ≤ 1
  sigma : Fin (d ^ 2) → Op (Fin d)
  identity : ∀ i, i.val = 0 → sigma i = 1
  unitary : ∀ i, (sigma i)ᴴ * sigma i = 1
  orthogonal : ∀ i j, ((sigma i)ᴴ * sigma j).trace = if i = j then (d : ℂ) else 0

/-- PDF p.10: p0=lambda+(1-lambda)/d^2, all other weights equal. -/
def depolarizingWeight {d : ℕ} (D : DepolarizingData d) (i : Fin (d ^ 2)) : ℝ :=
  let p0 := D.parameter + (1 - D.parameter) / (d : ℝ) ^ 2
  if i.val = 0 then p0 else (1 - p0) / ((d : ℝ) ^ 2 - 1)

/-- PDF p.10: the actual Kraus-block embedding, in output:environment order. -/
def depolarizingDilation {d : ℕ} (D : DepolarizingData d) :
    Matrix (Fin d × Fin (d ^ 2)) (Fin d) ℂ :=
  fun q j => (Real.sqrt (depolarizingWeight D q.2) : ℂ) * D.sigma q.2 q.1 j

/-- PDF p.10: entropy of the printed spectrum (a,b,...,b), including zero eigenvalues. -/
def depolarizingEntropyBits {d : ℕ} (D : DepolarizingData d) : ℝ :=
  let b := (1 - D.parameter) / (d : ℝ)
  let a := D.parameter + b;
  -(a * Real.logb 2 a + (d - 1 : ℕ) * b * Real.logb 2 b)

/-- Grouped tensor product of a list of local density matrices. -/
def productMatrices {A B : Type*} (n : ℕ) (rho : Fin n → Op (A × B)) :
    Op ((Fin n → A) × (Fin n → B)) :=
  fun p q => ∏ i, rho i (p.1 i, p.2 i) (q.1 i, q.2 i)

/-- PDF p.10: finite convex mixtures of supported product states, not arbitrary
entangled states in the tensor-power subspace. -/
def productMixture {A B : Type*} (n m : ℕ) (mu : Fin m → ℝ)
    (rho : Fin m → Fin n → Op (A × B)) : Op ((Fin n → A) × (Fin n → B)) :=
  ∑ j, (mu j : ℂ) • productMatrices n (rho j)

/-- PDF p.8: tensor of the specified dilation maps, allowing different local dimensions. -/
def jointDepolarizing {n : ℕ} {d : Fin n → ℕ} (D : ∀ i, DepolarizingData (d i)) :
    Matrix ((∀ i, Fin (d i)) × (∀ i, Fin (d i ^ 2))) (∀ i, Fin (d i)) ℂ :=
  fun q j => ∏ i, depolarizingDilation (D i) (q.1 i, q.2 i) (j i)

/-- PDF p.8: the actual ith pair marginal, summing the remaining coordinates once.
The update changes only coordinate i in the column; all other registers are traced. -/
def pairMarginal {n : ℕ} {a b : Fin n → ℕ}
    (rho : Op ((∀ i, Fin (a i)) × (∀ i, Fin (b i)))) (i : Fin n) :
    Op (Fin (a i) × Fin (b i)) :=
  fun p q => ∑ x : {x : ∀ j, Fin (a j) // x i = p.1},
    ∑ y : {y : ∀ j, Fin (b j) // y i = p.2},
      rho (x.val, y.val) (Function.update x.val i q.1, Function.update y.val i q.2)

/-- At the identity endpoint the nonidentity Kraus weights vanish, without 0/0. -/
example {d : ℕ} (D : DepolarizingData d) (h : D.parameter = 1)
    (i : Fin (d ^ 2)) (hi : i.val ≠ 0) : depolarizingWeight D i = 0 := by
  simp [depolarizingWeight, h, hi]

/-! Compact symmetry, on a nonzero finite-dimensional effective dilation.
An arbitrary ambient environment can be compressed to the component span of the finite
range, preserving every supported matrix, its marginal spectrum, and operational rates. -/

/-- PDF p.11: irreducibility on exactly the represented space. -/
def IrreducibleMatrix {G : Type*} {k : ℕ} (V : G → Op (Fin k)) : Prop :=
  ∀ L : Submodule ℂ (Fin k → ℂ),
    (∀ g x, x ∈ L → (V g).mulVec x ∈ L) → L = ⊥ ∨ L = ⊤

/-- PDF p.11, (15): compact continuous unitary actions on K and H2, both irreducible.
W is the actual isometry into environment:output. Covariance is imposed on all input
operators; no twirling identity, optimum, or product-case action is a hypothesis. -/
structure CovariantData (G : Type*) [Group G] [TopologicalSpace G]
    (a b k : ℕ) where
  environment_positive : 0 < a
  output_positive : 0 < b
  input_positive : 0 < k
  W : Matrix (Fin a × Fin b) (Fin k) ℂ
  isometry : Wᴴ * W = 1
  V : G → Op (Fin k)
  U : G → Op (Fin b)
  V_one : V 1 = 1
  U_one : U 1 = 1
  V_mul : ∀ g h, V (g * h) = V g * V h
  U_mul : ∀ g h, U (g * h) = U g * U h
  V_unitary : ∀ g, (V g)ᴴ * V g = 1
  U_unitary : ∀ g, (U g)ᴴ * U g = 1
  V_continuous : ∀ i j, Continuous (fun g => V g i j)
  U_continuous : ∀ i j, Continuous (fun g => U g i j)
  V_irreducible : IrreducibleMatrix V
  U_irreducible : IrreducibleMatrix U
  covariance : ∀ g X, traceLeft (W * (V g * X * (V g)ᴴ) * Wᴴ) =
    U g * traceLeft (W * X * Wᴴ) * (U g)ᴴ

/-- PDF p.11: P/Tr(P), constructed from W, whose rank and trace are k>0. -/
def projectorState {G : Type*} [Group G] [TopologicalSpace G] {a b k : ℕ}
    (D : CovariantData G a b k) : Op (Fin a × Fin b) :=
  (k : ℂ)⁻¹ • (D.W * D.Wᴴ)

/-- PDF p.11: embed a source vector using the actual isometry. -/
def embedded {a b k : ℕ} (W : Matrix (Fin a × Fin b) (Fin k) ℂ)
    (v : EuclideanSpace ℂ (Fin k)) : EuclideanSpace ℂ (Fin a × Fin b) :=
  WithLp.toLp 2 (W.mulVec (WithLp.ofLp v))

/-- PDF p.11, (17): minimum-entropy value over unit vectors, not all vectors of K.
The result below also asserts attainment, so the printed minimum is retained. -/
def minimumEntanglement {G : Type*} [Group G] [TopologicalSpace G] {a b k : ℕ}
    (D : CovariantData G a b k) : ℝ :=
  sInf {r | ∃ v : EuclideanSpace ℂ (Fin k), ‖v‖ = 1 ∧
    r = pureEntropyBits (embedded D.W v)}

/-- PDF p.11: finite-input Holevo objective for the channel defined by W and traceLeft. -/
def dilationHolevo {a b k : ℕ} (W : Matrix (Fin a × Fin b) (Fin k) ℂ)
    (e : PureEnsemble (Fin k)) : ℝ :=
  vnEntropy (traceLeft (W * pureAverage e * Wᴴ)) -
    ∑ j, e.prob j * vnEntropy (traceLeft (pureDensity (embedded W (e.vector j))))

/-- PDF p.11, (16): actual channel capacity (1), with unit normalized inputs. -/
def dilationCapacity {a b k : ℕ} (W : Matrix (Fin a × Fin b) (Fin k) ℂ) : ℝ :=
  sSup (Set.range (dilationHolevo W))

/-- PDF pp.11--12: convex hull of the orbit of the minimizing pure projector.
This is a convex hull of density matrices, not their linear support span. -/
def minimizingProjectorHull {G : Type*} [Group G] [TopologicalSpace G] {a b k : ℕ}
    (D : CovariantData G a b k) (v : EuclideanSpace ℂ (Fin k)) : Set (Op (Fin a × Fin b)) :=
  convexHull ℝ {rho | ∃ g : G, rho = pureDensity (embedded D.W (act (D.V g) v))}

/-- PDF p.12: transitivity on pure projectors, thus insensitive to global phase. -/
def PureTransitive {G : Type*} [Group G] [TopologicalSpace G] {a b k : ℕ}
    (D : CovariantData G a b k) : Prop :=
  ∀ v w : EuclideanSpace ℂ (Fin k), ‖v‖ = 1 → ‖w‖ = 1 →
    ∃ g : G, pureDensity (act (D.V g) v) = pureDensity w

/-- PDF p.13, Example 7: the three displayed orthonormal columns. j+3 is an
ordinary environment coordinate (3,4,5), not a residue modulo three. -/
def exampleSevenDilation : Matrix (Fin 3 × Fin 6) (Fin 3) ℂ :=
  fun q j =>
    if q.1 = j ∧ q.2.val = j.val + 3 then (Real.sqrt 2 / 2 : ℝ)
    else if (q.1.val = (j.val + 1) % 3 ∧ q.2.val = (j.val + 2) % 3) ∨
      (q.1.val = (j.val + 2) % 3 ∧ q.2.val = (j.val + 1) % 3) then (1 / 2 : ℂ) else 0

/-- PDF p.13: coherent superposition in C3 tensor (C6 direct-sum (C3 tensor C3)).
The right branch is |Phi_3> tensor |j>; no incoherent flag replaces the direct sum. -/
def exampleSevenMixtureDilation (c s : ℂ) :
    Matrix (Fin 3 × (Fin 6 ⊕ (Fin 3 × Fin 3))) (Fin 3) ℂ :=
  fun q j => match q.2 with
    | Sum.inl e => c * exampleSevenDilation (q.1, e) j
    | Sum.inr e => if q.1 = e.1 ∧ e.2 = j then s * ((Real.sqrt 3)⁻¹ : ℂ) else 0

/-- PDF p.13: explicit constant from the spectrum of the printed channel.
a=(1-|c|^2)/3+|c|^2/2, b=(1-|c|^2)/3+|c|^2/4, spectrum (a,b,b). -/
def exampleSevenMixtureEntropy (c : ℂ) : ℝ :=
  let t := Complex.normSq c
  let a := (1 - t) / 3 + t / 2
  let b := (1 - t) / 3 + t / 4;
  -(a * Real.logb 2 a + 2 * b * Real.logb 2 b)

/-- PDF p.13, Example 8: the specified normalized antisymmetric basis wedges. -/
def antisymmetricDilation : Matrix (Fin 3 × Fin 3) (Fin 3) ℂ :=
  fun q j =>
    if q.1.val = (j.val + 1) % 3 ∧ q.2.val = (j.val + 2) % 3 then ((Real.sqrt 2)⁻¹ : ℂ)
    else if q.1.val = (j.val + 2) % 3 ∧ q.2.val = (j.val + 1) % 3 then -((Real.sqrt 2)⁻¹ : ℂ)
    else 0

/-- Sanity: the noncyclic environment coordinate and the first cross coefficient. -/
example : exampleSevenDilation (0, 3) 0 = ((Real.sqrt 2 / 2 : ℝ) : ℂ) ∧
    exampleSevenDilation (1, 2) 0 = (1 / 2 : ℂ) := by
  norm_num [exampleSevenDilation]

/-- The direct-sum zero branch is exactly the scaled original vector. -/
example (c s : ℂ) (i j : Fin 3) (e : Fin 6) :
    exampleSevenMixtureDilation c s (i, Sum.inl e) j = c * exampleSevenDilation (i, e) j := rfl

/-- The antisymmetric sign is fixed by the printed order of the wedge. -/
example : antisymmetricDilation (2, 1) 0 = -((Real.sqrt 2)⁻¹ : ℂ) := by
  norm_num [antisymmetricDilation]

end

end QAlgorithms.Papers.Independent.Intakenext100.P60


