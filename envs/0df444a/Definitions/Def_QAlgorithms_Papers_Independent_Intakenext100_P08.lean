-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P08
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P08
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T03:57:50.018767+00:00
-- url     : https://prove2.me/theorems/2c754209-ac66-4271-8f35-8d48b6cd7c29
-- title:
--   Definitions for Achievable rates for the Gaussian quantum channel
-- statement:
--   The objects the formalized statements of *Achievable rates for the Gaussian quantum channel* (arXiv:quant-ph/0105058) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Generator`: Real row-generator matrices (28), PDF p.3. Nonsingularity is a theorem hypothesis.
--   - `rowLattice`: Source (28), PDF p.3: the integer span of the rows, with their actual Euclidean metric.
--   - `alternatingGram`: Source (29), PDF p.4: alternating pairing matrix of the row basis.
--   - `SymplecticallyIntegral`: Source p.4: every entry of the alternating pairing matrix is an integer.
--   - `symplecticDual`: Source p.4: vectors pairing integrally with every point of the row lattice.
--   - `dualGenerator`: Source (31), PDF p.4: the computed dual generator, not a free parameter.
--   - `DualCosets`: Source (43), PDF p.4: actual cosets represented by dual-lattice vectors. For integral M, these are the elements of Ldual/L. The finite-cardinality assertion is a conclusion, never a field of this definition.
--   - `unitBallVolume`: Source (48), PDF p.5: Lebesgue volume of the open Euclidean unit ball.
--   - `displacementLaw`: Source (2), (6), PDF pp.1–2: independent N(0,v) coordinates, transported by a measurable equivalence to Euclidean phase space. Here v is the variance.
--   - `voronoiCell`: Source p.5: the closed central Voronoi cell. Gaussian-null boundaries permit this definite choice of tie convention.
--   - `decodingFailure`: Geometric decoding failure, PDF pp.5–7, computed from the normalized noise law. It is not a quantum error or a free error parameter.
--   - `displacementTail`: Atypical-displacement tail omitted explicitly in the source's (59)–(64), PDF pp.6–7.
--   - `physicalNormalizer`: Physical normalizer scale from (52), (62), for integer multiplicity lambda^N.
--   - `complementaryErrorFunction`: Complementary error function in (71), (92), PDF pp.7,10. This standard finite-interval formula avoids improper-integral default values.
--   - `roundedResidue`: Source p.7: nearest-integer square-lattice syndrome, reduced modulo d. Mathlib's round breaks half-integer ties upwards; all such shifts are Gaussian-null.
--   - `xErrorProbability`: The X-error probability in (71), computed from the q displacement.
--   - `zErrorProbability`: The Z-error probability in (71), computed from the independent p displacement.
--   - `cyclicX`: The finite cyclic shift in (69), PDF p.7. No ideal oscillator eigenspace is assumed.
--   - `cyclicZ`: The finite clock in (69), PDF p.7, with the source's positive phase.
--   - `gridSymbol`: The exact centered alphabet underlying (90)–(92), PDF p.10; adjacent symbols differ by 2t.
--   - `gridDecode`: Nearest-symbol decoder for the finite centered alphabet, PDF p.10. Rounding gives an index on the infinite grid; clipping gives the nearest finite symbol.
--   - `gridMeanPower`: Exact uniform mean-symbol power of the finite alphabet (source (90) uses an approximation).
--   - `gridSymbolError`: Error probability conditional on the actual transmitted symbol, PDF p.10.
-- source:
--   Achievable rates for the Gaussian quantum channel, arXiv:quant-ph/0105058v1, https://arxiv.org/abs/quant-ph/0105058v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P02
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P10

/-!
Statements from Harrington–Preskill, quant-ph/0105058v1.
Only the algebraic and classical geometric results are asserted. Ideal Weyl
comb states are not treated as normalized oscillator states. See HARD.md for
operational claims and the Gram-classification ambiguity. Compilation pending.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P08

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal

-- Accepted grouped index and source-sign matrix; no paper-local copies.
open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase sigma)
-- The accepted predicate uses column bases and -sigma: apply it to S.transpose.
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)
-- The accepted pairing has the opposite sign: exchange its two arguments below.
open QAlgorithms.Papers.Independent.Frontier30.P10 (symplecticPair)

/-- Real row-generator matrices (28), PDF p.3. Nonsingularity is a theorem hypothesis. -/
abbrev Generator (N : ℕ) := Matrix (Phase N) (Phase N) ℝ

/-- Source (28), PDF p.3: the integer span of the rows, with their actual Euclidean metric. -/
def rowLattice {N : ℕ} (M : Generator N) : Submodule ℤ (EuclideanSpace ℝ (Phase N)) :=
  Submodule.span ℤ (Set.range fun i => WithLp.toLp 2 (M i))

/-- Source (29), PDF p.4: alternating pairing matrix of the row basis. -/
def alternatingGram {N : ℕ} (M : Generator N) : Generator N :=
  M * sigma N * M.transpose

/-- Source p.4: every entry of the alternating pairing matrix is an integer. -/
def SymplecticallyIntegral {N : ℕ} (M : Generator N) : Prop :=
  ∀ i j, ∃ z : ℤ, alternatingGram M i j = (z : ℝ)

/-- Source p.4: vectors pairing integrally with every point of the row lattice. -/
def symplecticDual {N : ℕ} (M : Generator N) : Set (EuclideanSpace ℝ (Phase N)) :=
  {x | ∀ y ∈ rowLattice M, ∃ z : ℤ, symplecticPair (WithLp.ofLp y) (WithLp.ofLp x) = (z : ℝ)}

/-- Source (31), PDF p.4: the computed dual generator, not a free parameter. -/
noncomputable def dualGenerator {N : ℕ} (M : Generator N) : Generator N :=
  (alternatingGram M)⁻¹ * M

/-- Source (43), PDF p.4: actual cosets represented by dual-lattice vectors.
For integral M, these are the elements of Ldual/L. The finite-cardinality
assertion is a conclusion, never a field of this definition. -/
def DualCosets {N : ℕ} (M : Generator N) :=
  {c : EuclideanSpace ℝ (Phase N) ⧸ (rowLattice M).toAddSubgroup //
    ∃ x ∈ symplecticDual M, (QuotientAddGroup.mk x :
      EuclideanSpace ℝ (Phase N) ⧸ (rowLattice M).toAddSubgroup) = c}

/-- Source (48), PDF p.5: Lebesgue volume of the open Euclidean unit ball. -/
noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

/-- Source (2), (6), PDF pp.1–2: independent N(0,v) coordinates, transported
by a measurable equivalence to Euclidean phase space. Here v is the variance. -/
noncomputable def displacementLaw (N : ℕ) (v : NNReal) : Measure (EuclideanSpace ℝ (Phase N)) :=
  Measure.map (MeasurableEquiv.toLp 2 (Phase N → ℝ))
    (Measure.pi fun _ : Phase N => gaussianReal 0 v)

/-- Source p.5: the closed central Voronoi cell. Gaussian-null boundaries
permit this definite choice of tie convention. -/
def voronoiCell {N : ℕ} (M : Generator N) : Set (EuclideanSpace ℝ (Phase N)) :=
  {x | ∀ y ∈ rowLattice M, ‖x‖ ≤ ‖x - y‖}

/-- Geometric decoding failure, PDF pp.5–7, computed from the normalized noise law.
It is not a quantum error or a free error parameter. -/
noncomputable def decodingFailure {N : ℕ} (M : Generator N) (v : NNReal) : ℝ :=
  (displacementLaw N v (voronoiCell M)ᶜ).toReal

/-- Atypical-displacement tail omitted explicitly in the source's (59)–(64), PDF pp.6–7. -/
noncomputable def displacementTail (N : ℕ) (v : NNReal) (a : ℝ) : ℝ :=
  (displacementLaw N v {x | a < ‖x‖}).toReal

/-- Physical normalizer scale from (52), (62), for integer multiplicity lambda^N. -/
noncomputable def physicalNormalizer {N : ℕ} (hbar : ℝ) (lambda : ℕ)
    (S : Generator N) : Generator N :=
  Real.sqrt (2 * Real.pi * hbar / (lambda : ℝ)) • S

/-- Complementary error function in (71), (92), PDF pp.7,10.
This standard finite-interval formula avoids improper-integral default values. -/
noncomputable def complementaryErrorFunction (x : ℝ) : ℝ :=
  1 - (2 / Real.sqrt Real.pi) * ∫ t in (0 : ℝ)..x, Real.exp (-(t ^ 2))

/-- Source p.7: nearest-integer square-lattice syndrome, reduced modulo d.
Mathlib's round breaks half-integer ties upwards; all such shifts are Gaussian-null. -/
noncomputable def roundedResidue (d : ℕ) (delta x : ℝ) : ZMod d :=
  (round (x / delta) : ℤ)

/-- The X-error probability in (71), computed from the q displacement. -/
noncomputable def xErrorProbability (d : ℕ) (delta : ℝ) (v : NNReal) : ℝ :=
  (((gaussianReal 0 v).prod (gaussianReal 0 v))
    {x : ℝ × ℝ | roundedResidue d delta x.1 ≠ 0}).toReal

/-- The Z-error probability in (71), computed from the independent p displacement. -/
noncomputable def zErrorProbability (d : ℕ) (delta : ℝ) (v : NNReal) : ℝ :=
  (((gaussianReal 0 v).prod (gaussianReal 0 v))
    {x : ℝ × ℝ | roundedResidue d delta x.2 ≠ 0}).toReal

/-- The finite cyclic shift in (69), PDF p.7. No ideal oscillator eigenspace is assumed. -/
def cyclicX (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i.val = (j.val + 1) % d then 1 else 0

/-- The finite clock in (69), PDF p.7, with the source's positive phase. -/
noncomputable def cyclicZ (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun j =>
    Complex.exp (Complex.I * (2 * Real.pi * (j.val : ℝ) / (d : ℝ) : ℝ))

/-- The exact centered alphabet underlying (90)–(92), PDF p.10; adjacent symbols differ by 2t. -/
def gridSymbol (d : ℕ) (t : ℝ) (j : Fin d) : ℝ :=
  (2 * (j.val : ℝ) - (d : ℝ) + 1) * t

/-- Nearest-symbol decoder for the finite centered alphabet, PDF p.10.
Rounding gives an index on the infinite grid; clipping gives the nearest finite symbol. -/
noncomputable def gridDecode (d : ℕ) [NeZero d] (t y : ℝ) : Fin d :=
  ⟨min (round ((y / t + (d : ℝ) - 1) / 2)).toNat (d - 1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (NeZero.pos d) (by decide))⟩

/-- Exact uniform mean-symbol power of the finite alphabet (source (90) uses an approximation). -/
noncomputable def gridMeanPower (d : ℕ) (t : ℝ) : ℝ :=
  (∑ j : Fin d, (gridSymbol d t j) ^ 2) / (d : ℝ)

/-- Error probability conditional on the actual transmitted symbol, PDF p.10. -/
noncomputable def gridSymbolError (d : ℕ) [NeZero d] (t : ℝ) (v : NNReal)
    (j : Fin d) : ℝ :=
  (gaussianReal 0 v {x | gridDecode d t (gridSymbol d t j + x) ≠ j}).toReal

/-! Sanity examples pin definitions without proving any source theorem. -/

example : sigma 1 (Sum.inl 0) (Sum.inr 0) = 1 := by
  norm_num [sigma, Matrix.fromBlocks]

example {N : ℕ} (y : EuclideanSpace ℝ (Phase N)) :
    symplecticPair (WithLp.ofLp y) 0 = 0 := by
  simp [symplecticPair]

example {N : ℕ} (M : Generator N) : (0 : EuclideanSpace ℝ (Phase N)) ∈ rowLattice M :=
  Submodule.zero_mem _

example {N : ℕ} (M : Generator N) : (0 : EuclideanSpace ℝ (Phase N)) ∈ symplecticDual M := by
  intro y hy
  exact ⟨0, by simp [symplecticPair]⟩

example (N : ℕ) : IsSymplectic (1 : Generator N).transpose := by
  simp [IsSymplectic]

example {N : ℕ} (M : Generator N) : (0 : EuclideanSpace ℝ (Phase N)) ∈ voronoiCell M := by
  intro y hy
  simp

example : complementaryErrorFunction 0 = 1 := by
  simp [complementaryErrorFunction]

example (d : ℕ) (delta : ℝ) : roundedResidue d delta 0 = 0 := by
  simp [roundedResidue]

example : cyclicX 2 1 0 = 1 := by
  norm_num [cyclicX]

example (d : ℕ) : cyclicZ d = Matrix.diagonal (fun j =>
    Complex.exp (Complex.I * (2 * Real.pi * (j.val : ℝ) / (d : ℝ) : ℝ))) := rfl

example (t : ℝ) : gridSymbol 2 t 0 = -t := by
  norm_num [gridSymbol]

example (t : ℝ) : gridMeanPower 2 t = t ^ 2 := by
  simp [gridMeanPower, gridSymbol, Fin.sum_univ_two] <;> ring

example {N : ℕ} (M : Generator N) :
    dualGenerator M = (alternatingGram M)⁻¹ * M := rfl

example {N : ℕ} (M : Generator N) : Nonempty (DualCosets M) := by
  refine ⟨⟨QuotientAddGroup.mk (0 : EuclideanSpace ℝ (Phase N)), 0, ?_, rfl⟩⟩
  intro y hy
  exact ⟨0, by simp [symplecticPair]⟩

example : unitBallVolume 2 = Real.pi := by
  norm_num [unitBallVolume, EuclideanSpace.volume_ball, Real.Gamma_two,
    Real.sq_sqrt (le_of_lt Real.pi_pos), Real.pi_pos.le]

example (N : ℕ) (v : NNReal) : displacementLaw N v Set.univ = 1 := by
  simp [displacementLaw,
    Measure.map_apply (MeasurableEquiv.toLp 2 (Phase N → ℝ)).measurable
      MeasurableSet.univ]

example {N : ℕ} (lambda : ℕ) (S : Generator N) :
    physicalNormalizer 0 lambda S = 0 := by
  simp [physicalNormalizer]

end QAlgorithms.Papers.Independent.Intakenext100.P08


