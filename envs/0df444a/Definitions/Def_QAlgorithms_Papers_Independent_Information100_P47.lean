-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P47
-- name    : QAlgorithms_Papers_Independent_Information100_P47
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T11:33:40.229858+00:00
-- url     : https://prove2.me/theorems/d8a1c86d-874b-4176-80e9-d0194ee544cf
-- title:
--   Definitions for Maximal coherence of quantum measurement and the resource theory of sharpness
-- statement:
--   The objects the formalized statements of *Maximal coherence of quantum measurement and the resource theory of sharpness* (arXiv:2607.05847) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Mat`: PDF p.2: matrices on a d-dimensional complex space.
--   - `Measurement`: PDF p.2: a fixed, finite set of n outcome labels.
--   - `IsProbability`: PDF pp.3–4: one probability vector for all outcome labels.
--   - `Probability`: PDF p.4: the probability simplex, including distributions with zero entries.
--   - `trivial`: PDF p.3: the trivial POVM with outcome distribution p.
--   - `IsIncoherent`: PDF p.2, Eq.(2): whole diagonal POVMs, with completeness enforced separately.
--   - `IsUnitary`: PDF p.4, Eq.(15): the full unitary group, in matrix form.
--   - `rotate`: PDF p.4, Eq.(15): simultaneous conjugation of every effect.
--   - `IsCPUnital`: PDF p.4, Eq.(12): a CP unital Heisenberg map between possibly different dimensions. The rectangular Kraus operators are those of the trace-preserving Schrödinger dual.
--   - `Distance`: PDF pp.2–4: a family of distances, with the outcome set unchanged by preprocessing.
--   - `IsDistance`: PDF p.2: faithfulness and CP-unital contractivity, without symmetry or triangle axioms.
--   - `UnitaryInvariant`: PDF p.5: simultaneous unitary invariance on valid POVMs.
--   - `mixture`: PDF p.10, Eq.(A1): finite probability-weighted mixtures of whole measurements.
--   - `JointConvex`: PDF pp.6,10: joint convexity with the same weights on both arguments.
--   - `coherence`: PDF p.2, Eq.(4): the extremal distance value over complete incoherent POVMs.
--   - `sharpness`: PDF p.4, Eq.(13): distance to trivial POVMs, minimized over one probability simplex.
--   - `maxCoherence`: PDF p.4, Eq.(15): optimization over the entire unitary group.
--   - `CommonEigenbasis`: PDF p.5, Theorem 2: one common eigenbasis and normalized conditional probabilities.
--   - `CommonMUB`: PDF p.5, Corollary 3: eigenbases may be chosen inside degenerate eigenspaces. The common MUB need not be unbiased to the original reference basis.
--   - `ElementContractive`: PDF p.5, Eq.(30): the same effect distance is contractive under each CP unital map. This is stronger than aggregate POVM contractivity and is used outcome by outcome.
--   - `ElementAdditive`: PDF p.5, Corollary 3: additivity uses one element distance for every outcome.
--   - `spectralNorm`: PDF pp.5–6, Eq.(32): spectral norm, as the supremum on Euclidean unit vectors.
--   - `spectralDistance`: PDF p.5, Eq.(32): retain the factor 1/2 in the spectral distance.
--   - `fuzzify`: PDF p.4, Eq.(12): mixing preprocessing with trivial noise, preserving outcome labels.
--   - `mixedUnitary`: PDF p.6, Theorem 5: a finite mixed-unitary dual, not an arbitrary unital map.
--   - `born`: PDF p.3, Eq.(5): normalized density matrices and Born outcome probabilities.
--   - `StatisticalDistance`: PDF pp.3,10: statistical distances are functions of two probability vectors.
--   - `inducedDistance`: PDF p.3, Eq.(5): the supremum over trace-one density matrices.
--   - `StatisticalJointConvex`: PDF p.10, Eq.(A1): no contractivity or triangle assumption is needed here.
--   - `totalVariation`: PDF p.8: D1 is maximal classical total variation, not a sum of effect trace norms.
--   - `conditional`: PDF p.3, Eq.(7): conditional reference-system operator, after tracing out the input.
--   - `diamondDistance`: PDF p.3, Eq.(7): diamond measurement distance, allowing every finite ancillary size.
--   - `sigmaX`: PDF pp.7–8: Pauli matrices in the fixed computational basis.
--   - `sigmaY`: PDF pp.7–8: Pauli Y, with the standard complex sign convention.
--   - `sigmaZ`: PDF p.7: Pauli Z for Bloch-vector effects.
--   - `bloch`: PDF p.7: the Bloch linear combination r dot sigma.
--   - `xyPOVM`: PDF p.7: joint X–Y POVM, with x=2i+j and coefficient 1/sqrt(2).
--   - `IsTetrahedron`: PDF p.7: all tetrahedral orientations and labelings, without choosing an interpolation.
--   - `sicPOVM`: PDF p.7: the tetrahedral rank-one qubit SIC effects, each weighted by 1/4.
--   - `phasePOVM`: PDF p.8, Eqs.(40)–(41): the effective two-outcome measurement of fringe visibility nu.
--   - `phaseProbability`: PDF p.8, Eq.(42): statistics on the specified input state |+><+|.
--   - `fisherInformation`: PDF p.8, Eq.(43): Fisher information with terms of zero probability omitted. At nu=1 and deterministic phases this is zero, not a continuous extension.
--   - `maxFisherInformation`: PDF p.8, Eq.(44): the extremal value, bounded and attained in the stated visibility range.
-- source:
--   Maximal coherence of quantum measurement and the resource theory of sharpness, arXiv:2607.05847v1, https://arxiv.org/abs/2607.05847v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

/-!
Statements from Baek–Jo–Nha, arXiv:2607.05847v1.
All new definitions are local to this paper. Distances take values in the complete
nonnegative extended reals, allowing divergences and avoiding real-supremum junk.
The infimum/supremum definitions specify extremal values. Attainment for the three
concrete distances is a supporting obligation, never an extra hypothesis. Generic
minimum/maximum-based results are deferred: see the assigned HARD.md and GAPS.json.
The reference basis is the standard basis of `Fin d`.
-/

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Matrix

namespace QAlgorithms.Papers.Independent.Information100.P47

/-- PDF p.2: matrices on a d-dimensional complex space. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- PDF p.2: a fixed, finite set of n outcome labels. -/
abbrev Measurement (d n : ℕ) := Fin n → Mat d

/-- PDF pp.3–4: one probability vector for all outcome labels. -/
def IsProbability {n : ℕ} (p : Fin n → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- PDF p.4: the probability simplex, including distributions with zero entries. -/
abbrev Probability (n : ℕ) := {p : Fin n → ℝ // IsProbability p}

/-- PDF p.3: the trivial POVM with outcome distribution p. -/
def trivial {d n : ℕ} (p : Fin n → ℝ) : Measurement d n :=
  fun x => (p x : ℂ) • (1 : Mat d)

/-- PDF p.2, Eq.(2): whole diagonal POVMs, with completeness enforced separately. -/
def IsIncoherent {d n : ℕ} (A : Measurement d n) : Prop :=
  ∀ x i j, i ≠ j → A x i j = 0

/-- PDF p.4, Eq.(15): the full unitary group, in matrix form. -/
def IsUnitary {d : ℕ} (U : Mat d) : Prop := Uᴴ * U = 1 ∧ U * Uᴴ = 1

/-- PDF p.4, Eq.(15): simultaneous conjugation of every effect. -/
def rotate {d n : ℕ} (U : Mat d) (A : Measurement d n) : Measurement d n :=
  fun x => Uᴴ * A x * U

/-- PDF p.4, Eq.(12): a CP unital Heisenberg map between possibly different dimensions.
The rectangular Kraus operators are those of the trace-preserving Schrödinger dual. -/
def IsCPUnital {d e : ℕ} (F : Mat d → Mat e) : Prop :=
  ∃ (k : ℕ) (K : Fin k → Matrix (Fin d) (Fin e) ℂ),
    (∑ j, (K j)ᴴ * K j = 1) ∧ ∀ X, F X = ∑ j, (K j)ᴴ * X * K j

/-- PDF pp.2–4: a family of distances, with the outcome set unchanged by preprocessing. -/
abbrev Distance := (d n : ℕ) → Measurement d n → Measurement d n → ℝ≥0∞

/-- PDF p.2: faithfulness and CP-unital contractivity, without symmetry or triangle axioms. -/
def IsDistance (D : Distance) : Prop :=
  (∀ d n, 0 < d → 0 < n → ∀ A B : Measurement d n,
    IsPOVM A → IsPOVM B → (D d n A B = 0 ↔ A = B)) ∧
  (∀ d e n, 0 < d → 0 < e → 0 < n → ∀ (A B : Measurement d n),
    IsPOVM A → IsPOVM B → ∀ F : Mat d → Mat e, IsCPUnital F →
      D e n (fun x => F (A x)) (fun x => F (B x)) ≤ D d n A B)

/-- PDF p.5: simultaneous unitary invariance on valid POVMs. -/
def UnitaryInvariant (D : Distance) : Prop :=
  ∀ d n, 0 < d → 0 < n → ∀ (A B : Measurement d n),
    IsPOVM A → IsPOVM B → ∀ U : Mat d, IsUnitary U →
      D d n (rotate U A) (rotate U B) = D d n A B

/-- PDF p.10, Eq.(A1): finite probability-weighted mixtures of whole measurements. -/
def mixture {d n k : ℕ} (p : Fin k → ℝ) (A : Fin k → Measurement d n) :
    Measurement d n := fun x => ∑ j, (p j : ℂ) • A j x

/-- PDF pp.6,10: joint convexity with the same weights on both arguments. -/
def JointConvex (D : Distance) : Prop :=
  ∀ d n k, 0 < d → 0 < n → ∀ (p : Fin k → ℝ), IsProbability p →
    ∀ (A B : Fin k → Measurement d n), (∀ j, IsPOVM (A j)) →
      (∀ j, IsPOVM (B j)) →
      D d n (mixture p A) (mixture p B) ≤
        ∑ j, ENNReal.ofReal (p j) * D d n (A j) (B j)

/-- PDF p.2, Eq.(4): the extremal distance value over complete incoherent POVMs. -/
def coherence (D : Distance) {d n : ℕ} (A : Measurement d n) : ℝ≥0∞ :=
  ⨅ B : {B : Measurement d n // IsPOVM B ∧ IsIncoherent B}, D d n A B.val

/-- PDF p.4, Eq.(13): distance to trivial POVMs, minimized over one probability simplex. -/
def sharpness (D : Distance) {d n : ℕ} (A : Measurement d n) : ℝ≥0∞ :=
  ⨅ p : Probability n, D d n A (trivial p.val)

/-- PDF p.4, Eq.(15): optimization over the entire unitary group. -/
def maxCoherence (D : Distance) {d n : ℕ} (A : Measurement d n) : ℝ≥0∞ :=
  ⨆ U : {U : Mat d // IsUnitary U}, coherence D (rotate U.val A)

/-- PDF p.5, Theorem 2: one common eigenbasis and normalized conditional probabilities. -/
def CommonEigenbasis {d n : ℕ} (A : Measurement d n) : Prop :=
  ∃ U : Mat d, IsUnitary U ∧ ∃ p : Fin n → Fin d → ℝ,
    (∀ x i, 0 ≤ p x i) ∧ (∀ i, ∑ x, p x i = 1) ∧
    ∀ x, A x = U * Matrix.diagonal (fun i => (p x i : ℂ)) * Uᴴ

/-- PDF p.5, Corollary 3: eigenbases may be chosen inside degenerate eigenspaces.
The common MUB need not be unbiased to the original reference basis. -/
def CommonMUB {d n : ℕ} (A : Measurement d n) : Prop :=
  ∃ V : Mat d, IsUnitary V ∧ ∀ x, ∃ E : Mat d, IsUnitary E ∧
    ∃ lam : Fin d → ℝ, (∀ i, 0 ≤ lam i) ∧
      A x = E * Matrix.diagonal (fun i => (lam i : ℂ)) * Eᴴ ∧
      ∀ i j, ‖∑ k, conj (E k i) * V k j‖ = 1 / Real.sqrt (d : ℝ)

/-- PDF p.5, Eq.(30): the same effect distance is contractive under each CP unital map.
This is stronger than aggregate POVM contractivity and is used outcome by outcome. -/
def ElementContractive (delta : (d : ℕ) → Mat d → Mat d → ℝ≥0∞) : Prop :=
  ∀ d e, 0 < d → 0 < e → ∀ X Y : Mat d, IsEffect X → IsEffect Y →
    ∀ F : Mat d → Mat e, IsCPUnital F → delta e (F X) (F Y) ≤ delta d X Y

/-- PDF p.5, Corollary 3: additivity uses one element distance for every outcome. -/
def ElementAdditive (D : Distance)
    (delta : (d : ℕ) → Mat d → Mat d → ℝ≥0∞) : Prop :=
  ∀ d n, 0 < d → 0 < n → ∀ A B : Measurement d n,
    IsPOVM A → IsPOVM B → D d n A B = ∑ x, delta d (A x) (B x)

/-- PDF pp.5–6, Eq.(32): spectral norm, as the supremum on Euclidean unit vectors. -/
def spectralNorm {d : ℕ} (X : Mat d) : ℝ≥0∞ :=
  ⨆ v : {v : EuclideanSpace ℂ (Fin d) // ‖v‖ = 1},
    ENNReal.ofReal ‖act X v.val‖

/-- PDF p.5, Eq.(32): retain the factor 1/2 in the spectral distance. -/
def spectralDistance : Distance := fun _ _ A B => (1 / 2 : ℝ≥0∞) *
  ∑ x, spectralNorm (A x - B x)

/-- PDF p.4, Eq.(12): mixing preprocessing with trivial noise, preserving outcome labels. -/
def fuzzify {d e n : ℕ} (F : Mat d → Mat e) (alpha : ℝ) (q : Fin n → ℝ)
    (A : Measurement d n) : Measurement e n :=
  fun x => (alpha : ℂ) • F (A x) + ((1 - alpha) : ℂ) • trivial q x

/-- PDF p.6, Theorem 5: a finite mixed-unitary dual, not an arbitrary unital map. -/
def mixedUnitary {d n k : ℕ} (p : Fin k → ℝ) (W : Fin k → Mat d)
    (A : Measurement d n) : Measurement d n :=
  mixture p (fun j => rotate (W j) A)

/-- PDF p.3, Eq.(5): normalized density matrices and Born outcome probabilities. -/
def born {d n : ℕ} (A : Measurement d n) (rho : Mat d) : Fin n → ℝ :=
  fun x => effectProb (A x) rho

/-- PDF pp.3,10: statistical distances are functions of two probability vectors. -/
abbrev StatisticalDistance := (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞

/-- PDF p.3, Eq.(5): the supremum over trace-one density matrices. -/
def inducedDistance (delta : StatisticalDistance) : Distance :=
  fun d n A B => ⨆ rho : {rho : Mat d // IsDensityMatrix rho},
    delta n (born A rho.val) (born B rho.val)

/-- PDF p.10, Eq.(A1): no contractivity or triangle assumption is needed here. -/
def StatisticalJointConvex (delta : StatisticalDistance) : Prop :=
  ∀ n k, 0 < n → ∀ alpha : Fin k → ℝ, IsProbability alpha →
    ∀ p q : Fin k → Fin n → ℝ,
      (∀ j, IsProbability (p j)) → (∀ j, IsProbability (q j)) →
      delta n (fun x => ∑ j, alpha j * p j x) (fun x => ∑ j, alpha j * q j x) ≤
        ∑ j, ENNReal.ofReal (alpha j) * delta n (p j) (q j)

/-- PDF p.8: D1 is maximal classical total variation, not a sum of effect trace norms. -/
def totalVariation : StatisticalDistance := fun _ p q =>
  ENNReal.ofReal ((∑ x, |p x - q x|) / 2)

/-- PDF p.3, Eq.(7): conditional reference-system operator, after tracing out the input. -/
def conditional {d r : ℕ} (X : Mat d)
    (rho : Matrix (Fin d × Fin r) (Fin d × Fin r) ℂ) : Mat r :=
  fun a b => ∑ i, ∑ j, X i j * rho (j, a) (i, b)

/-- PDF p.3, Eq.(7): diamond measurement distance, allowing every finite ancillary size. -/
def diamondDistance : Distance := fun d _ A B =>
  ⨆ r : ℕ, ⨆ rho : {rho : Matrix (Fin d × Fin r) (Fin d × Fin r) ℂ //
    IsDensityMatrix rho},
    ENNReal.ofReal ((∑ x, traceNorm (conditional (A x - B x) rho.val)) / 2)

/-- PDF pp.7–8: Pauli matrices in the fixed computational basis. -/
def sigmaX : Mat 2 := !![0, 1; 1, 0]

/-- PDF pp.7–8: Pauli Y, with the standard complex sign convention. -/
def sigmaY : Mat 2 := !![0, -Complex.I; Complex.I, 0]

/-- PDF p.7: Pauli Z for Bloch-vector effects. -/
def sigmaZ : Mat 2 := !![1, 0; 0, -1]

/-- PDF p.7: the Bloch linear combination r dot sigma. -/
def bloch (r : Fin 3 → ℝ) : Mat 2 :=
  (r 0 : ℂ) • sigmaX + (r 1 : ℂ) • sigmaY + (r 2 : ℂ) • sigmaZ

/-- PDF p.7: joint X–Y POVM, with x=2i+j and coefficient 1/sqrt(2). -/
def xyPOVM : Measurement 2 4 := fun x =>
  (1 / 4 : ℂ) • ((1 : Mat 2) + ((1 / Real.sqrt 2 : ℝ) : ℂ) •
    ((((-1 : ℝ) ^ (x.val / 2)) : ℂ) • sigmaX +
      (((-1 : ℝ) ^ (x.val % 2)) : ℂ) • sigmaY))

/-- PDF p.7: all tetrahedral orientations and labelings, without choosing an interpolation. -/
def IsTetrahedron (r : Fin 4 → Fin 3 → ℝ) : Prop :=
  (∀ x, ∑ i, r x i ^ 2 = 1) ∧
  (∀ x y, x ≠ y → ∑ i, r x i * r y i = -(1 / 3 : ℝ))

/-- PDF p.7: the tetrahedral rank-one qubit SIC effects, each weighted by 1/4. -/
def sicPOVM (r : Fin 4 → Fin 3 → ℝ) : Measurement 2 4 :=
  fun x => (1 / 4 : ℂ) • ((1 : Mat 2) + bloch (r x))

/-- PDF p.8, Eqs.(40)–(41): the effective two-outcome measurement of fringe visibility nu. -/
def phasePOVM (nu phi : ℝ) : Measurement 2 2 :=
  let plus := (1 / 2 : ℂ) • ((1 : Mat 2) + (nu : ℂ) •
    ((Real.cos phi : ℂ) • sigmaX + (Real.sin phi : ℂ) • sigmaY))
  fun x => if x = 0 then plus else 1 - plus

/-- PDF p.8, Eq.(42): statistics on the specified input state |+><+|. -/
def phaseProbability (nu phi : ℝ) (x : Fin 2) : ℝ :=
  if x = 0 then (1 + nu * Real.cos phi) / 2 else (1 - nu * Real.cos phi) / 2

/-- PDF p.8, Eq.(43): Fisher information with terms of zero probability omitted.
At nu=1 and deterministic phases this is zero, not a continuous extension. -/
def fisherInformation (nu phi : ℝ) : ℝ :=
  ∑ x : Fin 2, if 0 < phaseProbability nu phi x then
    (deriv (fun theta => phaseProbability nu theta x) phi) ^ 2 /
      phaseProbability nu phi x else 0

/-- PDF p.8, Eq.(44): the extremal value, bounded and attained in the stated visibility range. -/
def maxFisherInformation (nu : ℝ) : ℝ := sSup (Set.range (fisherInformation nu))

/-! Definition sanity examples. They pin interfaces, signs, normalizations, and boundaries. -/

example {d n : ℕ} (p : Fin n → ℝ) (x : Fin n) :
    trivial (d := d) p x = (p x : ℂ) • (1 : Mat d) := rfl

example {d n : ℕ} (A : Measurement d n) : rotate 1 A = A := by
  funext x
  simp [rotate]

example {d n : ℕ} (A : Measurement d n) :
    fuzzify (fun X : Mat d => X) 1 (fun _ => 0) A = A := by
  funext x
  simp [fuzzify]

example : sigmaY 0 1 = -Complex.I := rfl

example (phi : ℝ) (x : Fin 2) : phaseProbability 0 phi x = 1 / 2 := by
  simp [phaseProbability]

example {d n : ℕ} (D : Distance) (A : Measurement d n) :
    sharpness D A = ⨅ p : Probability n, D d n A (trivial p.val) := rfl

example {d : ℕ} : IsCPUnital (fun X : Mat d => X) := by
  refine ⟨1, (fun _ => (1 : Mat d)), ?_, ?_⟩
  · simp
  · intro X
    simp

example (d n : ℕ) : spectralDistance d n 0 0 = 0 := by
  simp [spectralDistance, spectralNorm, act]

example (n : ℕ) (p : Fin n → ℝ) : totalVariation n p p = 0 := by
  simp [totalVariation]

example {d r : ℕ} (rho : Matrix (Fin d × Fin r) (Fin d × Fin r) ℂ) :
    conditional (0 : Mat d) rho = 0 := by
  ext a b
  simp [conditional]

example {d n : ℕ} (rho : Mat d) : born (0 : Measurement d n) rho = 0 := by
  funext x
  simp [born, effectProb]

end QAlgorithms.Papers.Independent.Information100.P47


