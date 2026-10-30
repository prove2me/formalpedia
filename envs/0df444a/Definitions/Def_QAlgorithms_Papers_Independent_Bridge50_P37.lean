-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37
-- name    : QAlgorithms_Papers_Independent_Bridge50_P37
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T18:34:56.987637+00:00
-- url     : https://prove2.me/theorems/952d1128-b918-4986-81f6-042b84f70c5e
-- title:
--   Definitions for Positivity of linear maps under tensor powers
-- statement:
--   The objects the formalized statements of *Positivity of linear maps under tensor powers* (arXiv:1502.05630) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `matrixUnitExtension`: Matrix-unit linear extension (§II p.4); bundles the explicit coordinate formulas.
--   - `tensorLinearMap`: Full tensor action, including entangled inputs (§I p.2).
--   - `tensorLinearPower`: Bundled constant-family piSuperop formula (Definition 1 p.2). At degree zero the register is the one-dimensional empty product.
--   - `NTensorStable`: Positive map with positive full n-copy action, at positive degree (Definition 1 p.2). The base positivity implements the explicit p.2 convention that every n-tensor-stable positive map is positive. Without it, -id would pass at even n; see the discrepancy log.
--   - `TensorStable`: One map positive at every positive tensor degree (Definition 1 p.2).
--   - `basisTransposeLinearMap`: Fixed-basis transpose (§II p.4).
--   - `OutputCoPositive`: Output transpose composed with P is CP (Example I.1 p.2).
--   - `Nontrivial`: Nontriviality alone, separate from finite- or all-degree positivity (p.2).
--   - `hsAdjoint`: Hilbert--Schmidt adjoint, not entrywise conjugation (§II p.4).
--   - `inducedTrace`: Induced trace norm on the compact unit ball; equivalent to the source sphere (p.4).
--   - `inducedInfinity`: Induced operator norm, using the Euclidean spectral norm (§II p.4).
--   - `normalizedEntangledProjection`: Normalized maximally entangled projection (§II p.4), using the frozen vector.
--   - `productValues`: Unit vectors on each entire local space, allowing entanglement among copies (p.5).
--   - `minProduct`: Compact product-state minimum (p.5); Lemma 3 also states attainment.
--   - `NoProductKernel`: No nonzero product vector in the kernel, across A:B only (p.5).
--   - `ProductBlockPositive`: Hermitian product-positive cone, not merely a real-part test (pp.4,23).
--   - `SeparableMap`: Arbitrary rectangular separable CP maps; Kraus families are unnormalized (p.17).
--   - `RectangularEBPositive`: EB on every PSD input and every finite ancilla, without TP (Theorem 9 p.24).
--   - `FullySeparablePositive`: Full multipartite separability, with arbitrary unnormalized PSD factors (p.7).
--   - `LocallyEA`: k-local entanglement annihilation of the full output (§IV A p.7).
--   - `InfinityEA`: The same channel annihilates at every positive tensor degree (§IV A p.7).
--   - `Distillable`: Finite-copy two-qubit local-filter distillability, equivalent to LOCC distillability by quant-ph/9801069 after Eq. (9). Same body as accepted Support50.P39.IsDistillable, with second instead of first partial transpose (equivalent by full transpose). Filters can be rescaled to Kraus contractions; trace>0 excludes zero postselection (p.18).
--   - `NPPTBound`: A normalized entangled NPPT state that is LOCC-undistillable (pp.3--4).
--   - `wernerMap`: Werner--Holevo family Eq. (2) p.3; theorems require d>=2.
--   - `candidateMap`: W_p tensor (transpose composed with W_p), with exactly this grouping (p.3).
--   - `flipParamWernerState`: Werner state with swap expectation p, Eq. (A1), p.23.
--   - `isotropicState`: Isotropic state with maximally entangled overlap p (Appendix A p.23).
--   - `reductionMap`: Reduction map Gamma(X)=tr(X)I-X (Lemma 8 p.19).
--   - `distanceCP`: Negative spectral mass of the normalized Choi matrix, Eq. (15), p.14.
--   - `unitalize`: Filtered unitalization constructed from R itself (p.9).
--   - `recurrenceParameter`: The actual p constructed by Eq. (22), using its generalized inverse (p.21).
--   - `recurrenceR`: The recurrence update r_d(p), Eq. (20), p.20.
--   - `recurrenceG`: Canceled expression for g, resolving its removable endpoint p=1 (p.21).
--   - `bipartiteHaarTwirl`: Both normalized Haar twirls (pp.22--24). In the isotropic case the second factor is conjugate U, not U-adjoint. Continuous compact-group integrands are integrable.
--   - `outputEigenvalues`: Eigenvalue objective on every density input, Eq. (4), p.5.
--   - `minimumOutputEigenvalue`: Minimum output eigenvalue including the kernel (pp.5,24), with attainment below.
--   - `cpCodingErrors`: All finite CP coding sums, Eq. (17), p.15; no TP or contraction imposed.
--   - `separableErrors`: Separable Choi-distillation errors at k actual copies, Eq. (19), p.17.
--   - `parallelError`: Actual parallel coding error, with factor one half only here (Definition 2 p.8).
--   - `parallelErrors`: The infimum ranges over actual CPTP encoders and decoders (Lemma 5 p.13).
--   - `ParallelCode`: Actual parallel code on n copies of the output register (Eq. (14), p.13). This is the source's fixed-base presentation with d equal to the output dimension.
--   - `ParallelCode.error`: Half-diamond error of the code's actual channel (Eq. (8), p.8).
--   - `ParallelCode.rate`: Rate for fixed base equal to the output dimension, in bits per call (p.13).
--   - `DiamondAchievable`: Exactly the optimized-error definition in Eq. (8), p.8, with fixed d=2. The value sets contain replacement channels and lie in [0,1]. EReal limsup avoids identifying divergent rates with a default real value.
--   - `diamondQuantumCapacity`: Operational quantum capacity (Definition 2 p.8). For finite channels the feasible rate set is bounded by the input/output log dimension. Zero is included explicitly as the nonnegative supremum convention, also when no positive-length rate is feasible.
--   - `ParallelStrongConverse`: Strong converse on actual parallel codes: positive rate gap, block lengths tending infinity, computed errors tending to one exponentially (Eq. (14), p.13).
--   - `flatProduct`: Product channel on canonically enumerated product bases (Eq. (11), p.10).
--   - `messageKraus`: Product Kraus branch with both classical outcomes sent to the other party (Eq. (11)).
--   - `messageRound`: One complete message-exchange round, with local normalized Kraus families (p.10).
--   - `SequentialLOCC`: Finite sequential LOCC channels generated by local CPTP operations and the explicit classical-message rounds of Eq. (11), p.10. Local CPTP operations also allow retaining, discarding and relabelling local registers between rounds. This is distinct from PPT preservation and contains no communication channel calls.
--   - `flatTranspose`: Whole-B partial transpose on an enumerated A:B register (pp.10--11).
--   - `AllowedAssistance`: Assistance class: actual LOCC, or arbitrary CPTP PPT-preserving channels (p.11). All four local dimensions are positive; this does not define LOCC by PPT preservation.
--   - `sendMap`: One actual channel use moves Alice's port to Bob, leaving both memories intact (Definition 3 pp.10--11). Off-diagonal memory blocks are retained.
--   - `CommunicationProtocol`: Actual sequential protocol, with the use count tied to sendMap constructors. Arbitrary assistance can occur before, between and after all calls (Eq. (12), p.11).
--   - `TwoPartyCode`: Actual (N,m,epsilon) scheme of Definition 3 (pp.10--11); epsilon is computed below.
--   - `TwoPartyCode.endChannel`: Identify the one-dimensional end memories with the scalar algebra (Eq. (12)).
--   - `TwoPartyCode.error`: Computed half-diamond error of the actual full channel, Eq. (12), p.11.
--   - `TwoPartyCode.rate`: Rate in bits per call, Definition 3 p.11.
--   - `AssistedAchievable`: The source's vanishing-error, limsup achievable rates; assistance class kept explicit (p.11).
--   - `diamondAssistedCapacity`: Q2 for ppt=false; capacity with arbitrary PPT-preserving assistance for ppt=true (p.11).
--   - `AssistedStrongConverse`: Strong converse keeps liminf distinct from achievability's limsup (Theorem 7 p.12).
--   - `capacityBound`: Theorem 6's explicit expression; inverse and map remain actual data (p.8).
--   - `converseBound`: Eq. (14) uses the normalized Choi trace norm in its denominator, p.13.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, https://arxiv.org/abs/1502.05630v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P30
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P39

/-! Statements of arXiv:1502.05630v2. Positive finite dimensions, fixed orthonormal
bases, complex-linear maps, normalized reference-first Choi matrices throughout.
Theorem 8 uses its proof's normalized conclusion; see SOURCE_CORRECTIONS.md.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter MeasureTheory

-- Only the following exact definition bodies are reused from pinned accepted papers.
open QAlgorithms.Papers.Independent.Information100.P04 (gamma copies)
open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)
open QAlgorithms.Papers.Independent.Information100.P50 (maxEigenvalue)
open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Information100.P69 (diamond)
open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)
open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)
open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

namespace QAlgorithms.Papers.Independent.Bridge50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Matrix-unit linear extension (§II p.4); bundles the explicit coordinate formulas. -/
def matrixUnitExtension (c : B → B → A → A → ℂ) : MatrixMap A B where
  toFun X := fun a b => ∑ i, ∑ j, c a b i j * X i j
  map_add' X Y := by
    ext a b
    change (∑ i, ∑ j, c a b i j * (X i j + Y i j)) =
      (∑ i, ∑ j, c a b i j * X i j) + (∑ i, ∑ j, c a b i j * Y i j)
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' z X := by
    ext a b
    change (∑ i, ∑ j, c a b i j * (z * X i j)) =
      z * (∑ i, ∑ j, c a b i j * X i j)
    simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

/-- Full tensor action, including entangled inputs (§I p.2). -/
def tensorLinearMap (P : MatrixMap A B) (Q : MatrixMap C D) : MatrixMap (A × C) (B × D) :=
  matrixUnitExtension fun a b i j =>
    P (Matrix.single i.1 j.1 1) a.1 b.1 * Q (Matrix.single i.2 j.2 1) a.2 b.2

/-- Bundled constant-family piSuperop formula (Definition 1 p.2).
At degree zero the register is the one-dimensional empty product. -/
def tensorLinearPower (P : MatrixMap A B) (n : ℕ) : MatrixMap (Fin n → A) (Fin n → B) :=
  matrixUnitExtension fun a b i j => ∏ k, P (Matrix.single (i k) (j k) 1) (a k) (b k)

/-- Positive map with positive full n-copy action, at positive degree (Definition 1 p.2).
The base positivity implements the explicit p.2 convention that every n-tensor-stable
positive map is positive. Without it, -id would pass at even n; see the discrepancy log. -/
def NTensorStable (P : MatrixMap A B) (n : ℕ) : Prop :=
  0 < n ∧ IsPositiveMap P ∧ IsPositiveMap (tensorLinearPower P n)

/-- One map positive at every positive tensor degree (Definition 1 p.2). -/
def TensorStable (P : MatrixMap A B) : Prop := ∀ n, 0 < n → NTensorStable P n

/-- Fixed-basis transpose (§II p.4). -/
def basisTransposeLinearMap (A : Type) [Fintype A] : MatrixMap A A where
  toFun X := X.transpose
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Output transpose composed with P is CP (Example I.1 p.2). -/
def OutputCoPositive (P : MatrixMap A B) : Prop := Entanglement.IsCompletelyPositive ((basisTransposeLinearMap B).comp P)

/-- Nontriviality alone, separate from finite- or all-degree positivity (p.2). -/
def Nontrivial (P : MatrixMap A B) : Prop := ¬ Entanglement.IsCompletelyPositive P ∧ ¬ OutputCoPositive P

/-- Hilbert--Schmidt adjoint, not entrywise conjugation (§II p.4). -/
def hsAdjoint (P : MatrixMap A B) : MatrixMap B A :=
  matrixUnitExtension fun a b i j => conj (P (Matrix.single a b 1) i j)

/-- Induced trace norm on the compact unit ball; equivalent to the source sphere (p.4). -/
def inducedTrace (P : MatrixMap A B) : ℝ :=
  sSup {r | ∃ X : Mat A, traceNorm X ≤ 1 ∧ r = traceNorm (P X)}

/-- Induced operator norm, using the Euclidean spectral norm (§II p.4). -/
def inducedInfinity (P : MatrixMap A B) : ℝ :=
  sSup {r | ∃ X : Mat A, specNorm X ≤ 1 ∧ r = specNorm (P X)}

/-- Normalized maximally entangled projection (§II p.4), using the frozen vector. -/
def normalizedEntangledProjection (A : Type) [Fintype A] [Nonempty A] [DecidableEq A] : Mat (A × A) :=
  pureDensity (finiteMaxEntangled A)

/-- Unit vectors on each entire local space, allowing entanglement among copies (p.5). -/
def productValues (X : Mat (A × B)) : Set ℝ :=
  {r | ∃ u : EuclideanSpace ℂ A, ∃ v : EuclideanSpace ℂ B,
    ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ r = (inner ℂ (tensorVec u v) (act X (tensorVec u v))).re}

/-- Compact product-state minimum (p.5); Lemma 3 also states attainment. -/
def minProduct (X : Mat (A × B)) : ℝ := sInf (productValues X)

/-- No nonzero product vector in the kernel, across A:B only (p.5). -/
def NoProductKernel (X : Mat (A × B)) : Prop :=
  ∀ u : EuclideanSpace ℂ A, ∀ v : EuclideanSpace ℂ B,
    u ≠ 0 → v ≠ 0 → act X (tensorVec u v) ≠ 0

/-- Hermitian product-positive cone, not merely a real-part test (pp.4,23). -/
def ProductBlockPositive (X : Mat (A × B)) : Prop :=
  X.IsHermitian ∧ ∀ u : EuclideanSpace ℂ A, ∀ v : EuclideanSpace ℂ B,
    0 ≤ (inner ℂ (tensorVec u v) (act X (tensorVec u v))).re

/-- Arbitrary rectangular separable CP maps; Kraus families are unnormalized (p.17). -/
def SeparableMap (S : MatrixMap (A × B) (C × D)) : Prop :=
  ∃ m : ℕ, ∃ F : Fin m → Matrix C A ℂ, ∃ G : Fin m → Matrix D B ℂ,
    ∀ X, S X = ∑ i, Matrix.kronecker (F i) (G i) * X * (Matrix.kronecker (F i) (G i))ᴴ

/-- EB on every PSD input and every finite ancilla, without TP (Theorem 9 p.24). -/
def RectangularEBPositive (T : MatrixMap A B) : Prop :=
  ∀ r : ℕ, 0 < r → ∀ X : Mat (Fin r × A), X.PosSemidef →
    Entanglement.IsSeparablePositive (idTensorSuperop T X)

/-- Full multipartite separability, with arbitrary unnormalized PSD factors (p.7). -/
def FullySeparablePositive {k : ℕ} (X : Mat (Fin k → A)) : Prop :=
  ∃ m : ℕ, ∃ F : Fin m → Fin k → Mat A,
    (∀ i j, (F i j).PosSemidef) ∧ X = ∑ i, (fun a b => ∏ j, F i j (a j) (b j))

/-- k-local entanglement annihilation of the full output (§IV A p.7). -/
def LocallyEA (T : MatrixMap A B) (k : ℕ) : Prop :=
  0 < k ∧ ∀ X : Mat (Fin k → A), X.PosSemidef → FullySeparablePositive (tensorLinearPower T k X)

/-- The same channel annihilates at every positive tensor degree (§IV A p.7). -/
def InfinityEA (T : MatrixMap A B) : Prop := ∀ k, 0 < k → LocallyEA T k

/-- Finite-copy two-qubit local-filter distillability, equivalent to LOCC distillability
by quant-ph/9801069 after Eq. (9). Same body as accepted Support50.P39.IsDistillable,
with second instead of first partial transpose (equivalent by full transpose).
Filters can be rescaled to Kraus contractions; trace>0 excludes zero postselection (p.18). -/
def Distillable (X : Mat (A × B)) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ F : Matrix (Fin 2) (Fin n → A) ℂ,
    ∃ G : Matrix (Fin 2) (Fin n → B) ℂ,
      let Y := Matrix.kronecker F G * copies X n * (Matrix.kronecker F G)ᴴ
      0 < Y.trace.re ∧ ¬ (gamma Y).PosSemidef

/-- A normalized entangled NPPT state that is LOCC-undistillable (pp.3--4). -/
def NPPTBound (X : Mat (A × B)) : Prop :=
  IsDensityMatrix X ∧ ¬ Entanglement.IsSeparablePositive X ∧
    ¬ (gamma X).PosSemidef ∧ ¬ Distillable X

/-- Werner--Holevo family Eq. (2) p.3; theorems require d>=2. -/
def wernerMap (d : ℕ) (p : ℝ) : MatrixMap (Fin d) (Fin d) :=
  matrixUnitExtension fun a b i j => (1 / ((d : ℂ)^2 - 1)) *
    (((d : ℂ) - p) * (if i = j then 1 else 0) * (if a = b then 1 else 0) -
      (1 - (d : ℂ) * p) * (if a = j ∧ b = i then 1 else 0))

/-- W_p tensor (transpose composed with W_p), with exactly this grouping (p.3). -/
def candidateMap (d : ℕ) (p : ℝ) : MatrixMap (Fin d × Fin d) (Fin d × Fin d) :=
  tensorLinearMap (wernerMap d p) ((basisTransposeLinearMap (Fin d)).comp (wernerMap d p))

/-- Werner state with swap expectation p, Eq. (A1), p.23. -/
def flipParamWernerState (d : ℕ) (p : ℝ) : Mat (Fin d × Fin d) :=
  (((d : ℝ) - p) / (d * ((d : ℝ)^2 - 1)) : ℂ) • 1 +
    (((d : ℝ) * p - 1) / (d * ((d : ℝ)^2 - 1)) : ℂ) • (swapMatrix (I := Fin d))

/-- Isotropic state with maximally entangled overlap p (Appendix A p.23). -/
def isotropicState (d : ℕ) [NeZero d] (p : ℝ) : Mat (Fin d × Fin d) :=
  (p : ℂ) • normalizedEntangledProjection (Fin d) + (((1-p) / ((d : ℝ)^2-1) : ℝ) : ℂ) • (1-normalizedEntangledProjection (Fin d))

/-- Reduction map Gamma(X)=tr(X)I-X (Lemma 8 p.19). -/
def reductionMap (A : Type) [Fintype A] [DecidableEq A] : MatrixMap A A :=
  matrixUnitExtension fun a b i j =>
    (if i = j then 1 else 0) * (if a = b then 1 else 0) -
      (if a = i ∧ b = j then 1 else 0)

/-- Negative spectral mass of the normalized Choi matrix, Eq. (15), p.14. -/
def distanceCP [Nonempty A] (P : MatrixMap A B) : ℝ :=
  (traceNorm (normalizedChoi P) - (normalizedChoi P).trace.re) / 2

/-- Filtered unitalization constructed from R itself (p.9). -/
def unitalize [Nonempty B] (R : MatrixMap A B) : MatrixMap A B :=
  (matrixUnitExtension fun a b i j => inverseSqrt (R 1) a i * conj (inverseSqrt (R 1) b j)).comp R

/-- The actual p constructed by Eq. (22), using its generalized inverse (p.21). -/
def recurrenceParameter [Nonempty A] [Nonempty B] (P : MatrixMap A B) : ℝ :=
  let Z := inverseSqrt (Matrix.kronecker (1 : Mat A) (P 1))
  maxEigenvalue (Z * normalizedChoi P * Z)

/-- The recurrence update r_d(p), Eq. (20), p.20. -/
def recurrenceR (d : ℕ) (p : ℝ) : ℝ :=
  (1+p*(p*d*(d^2+d-1)-2)) / (p^2*d^3-2*p*d+d^2+d-1)

/-- Sanity: the maximally entangled endpoint is fixed by recurrence, p.20. -/
example : recurrenceR 2 1 = 1 := by norm_num [recurrenceR]

/-- Canceled expression for g, resolving its removable endpoint p=1 (p.21). -/
def recurrenceG (d : ℕ) (p : ℝ) : ℝ :=
  ((d : ℝ)-1) * (d*(1+p)+2) / (p^2*d^3-2*p*d+d^2+d-1)

/-- Both normalized Haar twirls (pp.22--24). In the isotropic case the second factor
is conjugate U, not U-adjoint. Continuous compact-group integrands are integrable. -/
def bipartiteHaarTwirl (d : ℕ) (isotropic : Bool) (X : Mat (Fin d × Fin d)) : Mat (Fin d × Fin d) :=
  fun a b => ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    let V := if isotropic then (fun i j => conj ((U : Mat (Fin d)) i j)) else (U : Mat (Fin d))
    let K := Matrix.kronecker (U : Mat (Fin d)) V
    (K * X * Kᴴ) a b ∂Schur.unitaryHaar d

/-- Eigenvalue objective on every density input, Eq. (4), p.5. -/
def outputEigenvalues (T : MatrixMap A B) : Set ℝ :=
  {r | ∃ X : Mat A, IsDensityMatrix X ∧ r = minEigenvalue (T X)}

/-- Minimum output eigenvalue including the kernel (pp.5,24), with attainment below. -/
def minimumOutputEigenvalue (T : MatrixMap A B) : ℝ := sInf (outputEigenvalues T)

/-- All finite CP coding sums, Eq. (17), p.15; no TP or contraction imposed. -/
def cpCodingErrors (P : MatrixMap A B) (k : ℕ) : Set ℝ :=
  {r | ∃ m : ℕ, 0 < m ∧ ∃ E : Fin m → MatrixMap A (Fin k → A),
    ∃ F : Fin m → MatrixMap (Fin k → B) A,
      (∀ i, Entanglement.IsCompletelyPositive (E i) ∧ Entanglement.IsCompletelyPositive (F i)) ∧
      r = diamond ((LinearMap.id : MatrixMap A A) - ∑ i, (F i).comp ((tensorLinearPower P k).comp (E i)))}

/-- Separable Choi-distillation errors at k actual copies, Eq. (19), p.17. -/
def separableErrors [Nonempty A] (P : MatrixMap A B) (k : ℕ) : Set ℝ :=
  {r | ∃ S : MatrixMap ((Fin k → A) × (Fin k → B)) (A × A),
    SeparableMap S ∧ r = traceNorm (normalizedEntangledProjection A - S (copies (normalizedChoi P) k))}

/-- Sanity: the bundled power is exactly the frozen full-register tensor formula (p.2). -/
example (P : MatrixMap A B) (n : ℕ) (X : Mat (Fin n → A)) :
    tensorLinearPower P n X = piSuperop (fun _ : Fin n => P) X := by
  ext a b
  change (∑ i, ∑ j, (∏ k, P (Matrix.single (i k) (j k) 1) (a k) (b k)) * X i j) =
    ∑ i, ∑ j, X i j * ∏ k, P (Matrix.single (i k) (j k) 1) (a k) (b k)
  simp only [mul_comm]

/-- Sanity: the canceled recurrence reaches the source's threshold value (p.21). -/
example : recurrenceG 2 (1/2) = 1 := by norm_num [recurrenceG]

/-- Sanity: transpose is an involution in the fixed basis (p.4). -/
example (X : Mat A) : basisTransposeLinearMap A (basisTransposeLinearMap A X) = X := rfl

/-- Sanity: generalized inverse square root keeps zero on the kernel (p.21). -/
example [Nonempty A] : inverseSqrt (0 : Mat A) = 0 := by simp [inverseSqrt, cfc_zero]

/-- Sanity: canceled endpoint at the smallest nontrivial dimension (p.21). -/
example : recurrenceG 2 1 = 2 / 3 := by norm_num [recurrenceG]

/-- Sanity: zero-copy matrix tensors are scalar one, not the zero algebra (p.15). -/
example (X : Mat (A × B)) (a b : (Fin 0 → A) × (Fin 0 → B)) :
    copies X 0 a b = 1 := by simp [copies]

/-- Sanity: maximally entangled projection is normalized at scalar dimension (p.4). -/
example : normalizedEntangledProjection Unit ((),()) ((),()) = 1 := by simp [normalizedEntangledProjection, pureDensity, finiteMaxEntangled]

/-- Actual parallel coding error, with factor one half only here (Definition 2 p.8). -/
def parallelError {L : Type} [Fintype L] [DecidableEq L] (T : MatrixMap A B) (m : ℕ)
    (E : MatrixMap L (Fin m → A)) (F : MatrixMap (Fin m → B) L) : ℝ :=
  diamond ((LinearMap.id : MatrixMap L L) - F.comp ((tensorLinearPower T m).comp E)) / 2

/-- The infimum ranges over actual CPTP encoders and decoders (Lemma 5 p.13). -/
def parallelErrors {L : Type} [Fintype L] [DecidableEq L]
    (T : MatrixMap A B) (m : ℕ) : Set ℝ :=
  {r | ∃ E : MatrixMap L (Fin m → A), ∃ F : MatrixMap (Fin m → B) L,
    IsChannel E ∧ IsChannel F ∧ r = parallelError T m E F}

/-- Actual parallel code on n copies of the output register (Eq. (14), p.13).
This is the source's fixed-base presentation with d equal to the output dimension. -/
structure ParallelCode (T : MatrixMap A B) where
  n : ℕ
  m : ℕ
  npos : 0 < n
  mpos : 0 < m
  encoder : MatrixMap (Fin n → B) (Fin m → A)
  decoder : MatrixMap (Fin m → B) (Fin n → B)
  encoderChannel : IsChannel encoder
  decoderChannel : IsChannel decoder

/-- Half-diamond error of the code's actual channel (Eq. (8), p.8). -/
def ParallelCode.error {T : MatrixMap A B} (K : ParallelCode T) : ℝ :=
  parallelError T K.m K.encoder K.decoder

/-- Rate for fixed base equal to the output dimension, in bits per call (p.13). -/
def ParallelCode.rate {T : MatrixMap A B} (K : ParallelCode T) : ℝ :=
  (K.n : ℝ) * Real.logb 2 (Fintype.card B) / K.m

/-- Exactly the optimized-error definition in Eq. (8), p.8, with fixed d=2.
The value sets contain replacement channels and lie in [0,1]. EReal limsup avoids
identifying divergent rates with a default real value. -/
def DiamondAchievable (T : MatrixMap A B) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∃ n m : ℕ → ℕ, (∀ v, 0 < n v ∧ 0 < m v) ∧
    Tendsto (fun v => sInf (parallelErrors (L := Fin (n v) → Fin 2) T (m v))) atTop (nhds 0) ∧
    Filter.limsup (fun v => (((n v : ℝ) / m v) : EReal)) atTop = (r : EReal)

/-- Operational quantum capacity (Definition 2 p.8). For finite channels the feasible
rate set is bounded by the input/output log dimension. Zero is included explicitly
as the nonnegative supremum convention, also when no positive-length rate is feasible. -/
def diamondQuantumCapacity (T : MatrixMap A B) : ℝ := sSup ({0} ∪ {r | DiamondAchievable T r})

/-- Strong converse on actual parallel codes: positive rate gap, block lengths tending
infinity, computed errors tending to one exponentially (Eq. (14), p.13). -/
def ParallelStrongConverse (T : MatrixMap A B) (r : ℝ) : Prop :=
  ∀ K : ℕ → ParallelCode T, Tendsto (fun v => (K v).m) atTop atTop →
    (r : EReal) < Filter.liminf (fun v => ((K v).rate : EReal)) atTop →
    Tendsto (fun v => (K v).error) atTop (nhds 1) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ v0 : ℕ, ∀ v ≥ v0,
        1 - (K v).error ≤ Real.exp (-c * (K v).m)

/-- Product channel on canonically enumerated product bases (Eq. (11), p.10). -/
def flatProduct {a b c d : ℕ} (E : MatrixMap (Fin a) (Fin c)) (F : MatrixMap (Fin b) (Fin d)) :
    MatrixMap (Fin (a*b)) (Fin (c*d)) :=
  matrixUnitExtension fun o p x y =>
    let oo : Fin c × Fin d := finProdFinEquiv.symm o
    let pp : Fin c × Fin d := finProdFinEquiv.symm p
    let xx : Fin a × Fin b := finProdFinEquiv.symm x
    let yy : Fin a × Fin b := finProdFinEquiv.symm y
    E (Matrix.single xx.1 yy.1 1) oo.1 pp.1 * F (Matrix.single xx.2 yy.2 1) oo.2 pp.2

/-- Product Kraus branch with both classical outcomes sent to the other party (Eq. (11)). -/
def messageKraus {a b c d i j : ℕ}
    (E : Fin i → Matrix (Fin c) (Fin a) ℂ) (F : Fin j → Matrix (Fin d) (Fin b) ℂ)
    (s : Fin i) (t : Fin j) : Matrix (Fin ((c*j)*(d*i))) (Fin (a*b)) ℂ :=
  fun o x =>
    let oo : Fin (c*j) × Fin (d*i) := finProdFinEquiv.symm o
    let aa : Fin c × Fin j := finProdFinEquiv.symm oo.1
    let bb : Fin d × Fin i := finProdFinEquiv.symm oo.2
    let xx : Fin a × Fin b := finProdFinEquiv.symm x
    if aa.2 = t ∧ bb.2 = s then E s aa.1 xx.1 * F t bb.1 xx.2 else 0

/-- One complete message-exchange round, with local normalized Kraus families (p.10). -/
def messageRound {a b c d i j : ℕ}
    (E : Fin i → Matrix (Fin c) (Fin a) ℂ) (F : Fin j → Matrix (Fin d) (Fin b) ℂ) :
    MatrixMap (Fin (a*b)) (Fin ((c*j)*(d*i))) :=
  matrixUnitExtension fun o p x y => ∑ s, ∑ t,
    messageKraus E F s t o x * conj (messageKraus E F s t p y)

/-- Finite sequential LOCC channels generated by local CPTP operations and the
explicit classical-message rounds of Eq. (11), p.10. Local CPTP operations also allow
retaining, discarding and relabelling local registers between rounds. This is distinct
from PPT preservation and contains no communication channel calls. -/
inductive SequentialLOCC : (a b c d : ℕ) → MatrixMap (Fin (a*b)) (Fin (c*d)) → Prop
  | local {a b c d : ℕ} (E : MatrixMap (Fin a) (Fin c)) (F : MatrixMap (Fin b) (Fin d))
      (hE : IsChannel E) (hF : IsChannel F) : SequentialLOCC a b c d (flatProduct E F)
  | message {a b c d i j : ℕ}
      (E : Fin i → Matrix (Fin c) (Fin a) ℂ) (F : Fin j → Matrix (Fin d) (Fin b) ℂ)
      (hE : IsKrausFamily E) (hF : IsKrausFamily F) :
      SequentialLOCC a b (c*j) (d*i) (messageRound E F)
  | comp {a b c d e f : ℕ} {E : MatrixMap (Fin (a*b)) (Fin (c*d))}
      {F : MatrixMap (Fin (c*d)) (Fin (e*f))} (hE : SequentialLOCC a b c d E) (hF : SequentialLOCC c d e f F) :
      SequentialLOCC a b e f (F.comp E)

/-- Whole-B partial transpose on an enumerated A:B register (pp.10--11). -/
def flatTranspose (a b : ℕ) : MatrixMap (Fin (a*b)) (Fin (a*b)) :=
  flatProduct (LinearMap.id : MatrixMap (Fin a) (Fin a)) (basisTransposeLinearMap (Fin b))

/-- Assistance class: actual LOCC, or arbitrary CPTP PPT-preserving channels (p.11).
All four local dimensions are positive; this does not define LOCC by PPT preservation. -/
def AllowedAssistance (ppt : Bool) (a b c d : ℕ) (L : MatrixMap (Fin (a*b)) (Fin (c*d))) : Prop :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧
    if ppt then IsChannel L ∧ Entanglement.IsCompletelyPositive
      ((flatTranspose c d).comp (L.comp (flatTranspose a b))) else SequentialLOCC a b c d L

/-- One actual channel use moves Alice's port to Bob, leaving both memories intact
(Definition 3 pp.10--11). Off-diagonal memory blocks are retained. -/
def sendMap {a b : ℕ} (T : MatrixMap (Fin a) (Fin b)) (u v : ℕ) :
    MatrixMap (Fin ((a*u)*v)) (Fin (u*(b*v))) :=
  matrixUnitExtension fun o p x y =>
    let oo : Fin u × Fin (b*v) := finProdFinEquiv.symm o
    let pp : Fin u × Fin (b*v) := finProdFinEquiv.symm p
    let ox : Fin b × Fin v := finProdFinEquiv.symm oo.2
    let px : Fin b × Fin v := finProdFinEquiv.symm pp.2
    let xx : Fin (a*u) × Fin v := finProdFinEquiv.symm x
    let yy : Fin (a*u) × Fin v := finProdFinEquiv.symm y
    let ax : Fin a × Fin u := finProdFinEquiv.symm xx.1
    let ay : Fin a × Fin u := finProdFinEquiv.symm yy.1
    if oo.1 = ax.2 ∧ pp.1 = ay.2 ∧ ox.2 = xx.2 ∧ px.2 = yy.2
    then T (Matrix.single ax.1 ay.1 1) ox.1 px.1 else 0

/-- Actual sequential protocol, with the use count tied to sendMap constructors.
Arbitrary assistance can occur before, between and after all calls (Eq. (12), p.11). -/
inductive CommunicationProtocol {a b : ℕ} (T : MatrixMap (Fin a) (Fin b)) (ppt : Bool) :
    (u v x y m : ℕ) → MatrixMap (Fin (u*v)) (Fin (x*y)) → Prop
  | assistance {u v x y : ℕ} (L : MatrixMap (Fin (u*v)) (Fin (x*y)))
      (h : AllowedAssistance ppt u v x y L) : CommunicationProtocol T ppt u v x y 0 L
  | call (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
      CommunicationProtocol T ppt (a*u) v u (b*v) 1 (sendMap T u v)
  | comp {u v x y z w m n : ℕ} {E : MatrixMap (Fin (u*v)) (Fin (x*y))}
      {F : MatrixMap (Fin (x*y)) (Fin (z*w))} (hE : CommunicationProtocol T ppt u v x y m E)
      (hF : CommunicationProtocol T ppt x y z w n F) : CommunicationProtocol T ppt u v z w (m+n) (F.comp E)

/-- Actual (N,m,epsilon) scheme of Definition 3 (pp.10--11); epsilon is computed below. -/
structure TwoPartyCode {a b : ℕ} (T : MatrixMap (Fin a) (Fin b)) (ppt : Bool) where
  N : ℕ
  m : ℕ
  Npos : 0 < N
  mpos : 0 < m
  channel : MatrixMap (Fin (N*1)) (Fin (1*N))
  valid : CommunicationProtocol T ppt N 1 1 N m channel

/-- Identify the one-dimensional end memories with the scalar algebra (Eq. (12)). -/
def TwoPartyCode.endChannel {a b : ℕ} {T : MatrixMap (Fin a) (Fin b)} {ppt : Bool}
    (K : TwoPartyCode T ppt) : MatrixMap (Fin K.N) (Fin K.N) :=
  matrixUnitExtension fun o p x y => K.channel
    (Matrix.single (finProdFinEquiv (x, (0 : Fin 1))) (finProdFinEquiv (y, (0 : Fin 1))) 1)
    (finProdFinEquiv ((0 : Fin 1),o)) (finProdFinEquiv ((0 : Fin 1),p))

/-- Computed half-diamond error of the actual full channel, Eq. (12), p.11. -/
def TwoPartyCode.error {a b : ℕ} {T : MatrixMap (Fin a) (Fin b)} {ppt : Bool}
    (K : TwoPartyCode T ppt) : ℝ :=
  diamond ((LinearMap.id : MatrixMap (Fin K.N) (Fin K.N)) - K.endChannel) / 2

/-- Rate in bits per call, Definition 3 p.11. -/
def TwoPartyCode.rate {a b : ℕ} {T : MatrixMap (Fin a) (Fin b)} {ppt : Bool}
    (K : TwoPartyCode T ppt) : ℝ := Real.logb 2 K.N / K.m

/-- The source's vanishing-error, limsup achievable rates; assistance class kept explicit (p.11). -/
def AssistedAchievable {a b : ℕ} (T : MatrixMap (Fin a) (Fin b)) (ppt : Bool) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∃ K : ℕ → TwoPartyCode T ppt,
    Tendsto (fun v => (K v).error) atTop (nhds 0) ∧
    Filter.limsup (fun v => ((K v).rate : EReal)) atTop = (r : EReal)

/-- Q2 for ppt=false; capacity with arbitrary PPT-preserving assistance for ppt=true (p.11). -/
def diamondAssistedCapacity {a b : ℕ} (T : MatrixMap (Fin a) (Fin b)) (ppt : Bool) : ℝ :=
  sSup {r | AssistedAchievable T ppt r}

/-- Strong converse keeps liminf distinct from achievability's limsup (Theorem 7 p.12). -/
def AssistedStrongConverse {a b : ℕ} (T : MatrixMap (Fin a) (Fin b)) (ppt : Bool) (r : ℝ) : Prop :=
  ∀ K : ℕ → TwoPartyCode T ppt, Tendsto (fun v => (K v).m) atTop atTop →
    (r : EReal) < Filter.liminf (fun v => ((K v).rate : EReal)) atTop →
    Tendsto (fun v => (K v).error) atTop (nhds 1) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ v0 : ℕ, ∀ v ≥ v0,
        1 - (K v).error ≤ Real.exp (-c * (K v).m)

/-- Theorem 6's explicit expression; inverse and map remain actual data (p.8). -/
def capacityBound (T : MatrixMap A B) (P : MatrixMap C B) (R : MatrixMap B C) : ℝ :=
  Real.logb 2 (diamond (R.comp T) * specNorm (hsAdjoint P 1)) *
    Real.logb 2 (Fintype.card B) / Real.logb 2 (diamond (hsAdjoint P))

/-- Eq. (14) uses the normalized Choi trace norm in its denominator, p.13. -/
def converseBound [Nonempty B] (T : MatrixMap A B) (P : MatrixMap C B) (R : MatrixMap B C) : ℝ :=
  Real.logb 2 (diamond (R.comp T) * specNorm (hsAdjoint P 1)) *
    Real.logb 2 (Fintype.card B) /
      Real.logb 2 (traceNorm (tensorLinearMap (hsAdjoint P) (LinearMap.id : MatrixMap B B) (normalizedEntangledProjection B)))

/-- Sanity: an actual code's error has the specified half factor, p.8. -/
example {T : MatrixMap A B} (K : ParallelCode T) :
    K.error = parallelError T K.m K.encoder K.decoder := rfl

/-- Sanity: call counting is structural, not an unrelated free cost, p.11. -/
example {a b : ℕ} (T : MatrixMap (Fin a) (Fin b)) (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    CommunicationProtocol T false (a*u) v u (b*v) 1 (sendMap T u v) := CommunicationProtocol.call u v hu hv

end QAlgorithms.Papers.Independent.Bridge50.P37


