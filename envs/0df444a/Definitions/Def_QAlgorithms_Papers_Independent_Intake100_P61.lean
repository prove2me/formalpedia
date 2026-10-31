-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P61
-- name    : QAlgorithms_Papers_Independent_Intake100_P61
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T11:00:48.268925+00:00
-- url     : https://prove2.me/theorems/7c4d8f7e-d876-47e9-82c5-9d003f7b2633
-- title:
--   Definitions for Composable security proof for continuous-variable quantum key distribution with coherent states
-- statement:
--   The objects the formalized statements of *Composable security proof for continuous-variable quantum key distribution with coherent states* (arXiv:1408.5689) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `vectorSquare`: PDF pp.20–22: Euclidean squared norm of unbundled coordinates.
--   - `realDot`: PDF pp.21–22: real Euclidean inner product.
--   - `firstCoordinates`: PDF pp.20–22: first k coordinates, padded with zeros in the original space.
--   - `halfProjection`: PDF pp.20–21: actual projection U* P_k U v. A normalized invariant Borel probability on U(m) or O(m) is Haar; the range U* span(e_0,...,e_(k-1)) is uniform.
--   - `pairDensityLaw`: PDF p.22: actual density Q(X,Y) against 8n-dimensional Lebesgue measure.
--   - `transposeRotation`: PDF p.22: literal symmetry (X,Y) -> (O X,O^T Y). No identification with the passive optical U(2n) action is made.
--   - `nonnegativeVolume`: PDF pp.22–23: nonnegative half-line Lebesgue reference measure.
--   - `quadrantLaw`: PDF pp.22–23: one joint law constructed from p on the nonnegative quadrant.
--   - `firstMarginalDensity`: PDF pp.22–23: marginal density from that same p.
--   - `densityConditionalMean`: PDF pp.22–23, E21/E28: extended conditional mean from p(y|x)=p(x,y)/p_X(x). This differs from Advance50.P02.conditionalMean, which is a finite cq entropy. Zero or infinite marginal-density fibers are null for a probability law and are assigned zero. Infinite means on positive finite fibers remain infinity.
--   - `empiricalEntropy`: PDF pp.17–18, D26: plug-in one-symbol entropy in bits.
--   - `iidWordProbability`: PDF pp.17–18: iid event probability with actual product weights from p.
-- source:
--   Composable security proof for continuous-variable quantum key distribution with coherent states, arXiv:1408.5689v3, https://arxiv.org/abs/1408.5689v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P30

/-! Leverrier, arXiv:1408.5689v3. Classical components with explicit laws.
Source corrections and deferred quantum interfaces are recorded in the unit.
Compilation is pending the separate mechanical handoff. -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Intake100.P61

attribute [local instance] Classical.propDecidable Classical.decEq

-- The frozen frequency formula specializes exactly to the source alphabet Fin (2 ^ d).
open QAlgorithms.Papers.Independent.Advance50.P30 (empiricalFrequency)

/-- PDF pp.20–21: Borel outcomes on U(m) over C or O(m) over R. -/
instance rotationMeasurable (K : Type) [RCLike K] (m : ℕ) :
    MeasurableSpace (Matrix.unitaryGroup (Fin m) K) := borel _

/-- PDF pp.20–21: the preceding sigma algebra is precisely Borel. -/
instance rotationBorel (K : Type) [RCLike K] (m : ℕ) :
    BorelSpace (Matrix.unitaryGroup (Fin m) K) := ⟨rfl⟩

/-- PDF pp.20–22: Euclidean squared norm of unbundled coordinates. -/
def vectorSquare {K : Type} [RCLike K] {m : ℕ} (v : Fin m → K) : ℝ :=
  ∑ i, ‖v i‖ ^ 2

/-- PDF pp.21–22: real Euclidean inner product. -/
def realDot {m : ℕ} (v w : Fin m → ℝ) : ℝ := ∑ i, v i * w i

/-- PDF pp.20–22: first k coordinates, padded with zeros in the original space. -/
def firstCoordinates {K : Type} [Zero K] {m : ℕ} (k : ℕ) (v : Fin m → K) : Fin m → K :=
  fun i => if i.val < k then v i else 0

/-- PDF pp.20–21: actual projection U* P_k U v. A normalized invariant Borel
probability on U(m) or O(m) is Haar; the range U* span(e_0,...,e_(k-1)) is uniform. -/
def halfProjection {K : Type} [RCLike K] {m : ℕ}
    (U : Matrix.unitaryGroup (Fin m) K) (k : ℕ) (v : Fin m → K) : Fin m → K :=
  (star (U : Matrix (Fin m) (Fin m) K)).mulVec
    (firstCoordinates k ((U : Matrix (Fin m) (Fin m) K).mulVec v))

example {K : Type} [RCLike K] {m : ℕ} : vectorSquare (0 : Fin m → K) = 0 := by
  simp [vectorSquare]

example {m : ℕ} (v : Fin m → ℝ) : realDot v 0 = 0 := by
  simp [realDot]

example {K : Type} [Zero K] {m : ℕ} (v : Fin m → K) : firstCoordinates 0 v = 0 := by
  funext i
  simp [firstCoordinates]

example {K : Type} [RCLike K] {m : ℕ}
    (U : Matrix.unitaryGroup (Fin m) K) (k : ℕ) : halfProjection U k 0 = 0 := by
  have hzero : firstCoordinates k (0 : Fin m → K) = 0 := by
    funext i
    simp [firstCoordinates]
  simp only [halfProjection, Matrix.mulVec_zero, hzero]

/-- PDF p.22: actual density Q(X,Y) against 8n-dimensional Lebesgue measure. -/
def pairDensityLaw (n : ℕ)
    (q : ((Fin (4 * n) → ℝ) × (Fin (4 * n) → ℝ)) → ℝ≥0∞) :
    Measure ((Fin (4 * n) → ℝ) × (Fin (4 * n) → ℝ)) := volume.withDensity q

/-- PDF p.22: literal symmetry (X,Y) -> (O X,O^T Y).
No identification with the passive optical U(2n) action is made. -/
def transposeRotation {m : ℕ} (O : Matrix.unitaryGroup (Fin m) ℝ)
    (v : (Fin m → ℝ) × (Fin m → ℝ)) : (Fin m → ℝ) × (Fin m → ℝ) :=
  ((O : Matrix (Fin m) (Fin m) ℝ).mulVec v.1,
    (O : Matrix (Fin m) (Fin m) ℝ).transpose.mulVec v.2)

example (n : ℕ) : pairDensityLaw n (fun _ => 0) = 0 := by
  simp [pairDensityLaw]

example {m : ℕ} (O : Matrix.unitaryGroup (Fin m) ℝ) :
    transposeRotation O (0, 0) = (0, 0) := by
  simp [transposeRotation, Matrix.mulVec]

/-- PDF pp.22–23: nonnegative half-line Lebesgue reference measure. -/
def nonnegativeVolume : Measure ℝ := volume.restrict (Set.Ici 0)

/-- PDF pp.22–23: one joint law constructed from p on the nonnegative quadrant. -/
def quadrantLaw (p : ℝ × ℝ → ℝ≥0∞) : Measure (ℝ × ℝ) :=
  (nonnegativeVolume.prod nonnegativeVolume).withDensity p

/-- PDF pp.22–23: marginal density from that same p. -/
def firstMarginalDensity (p : ℝ × ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, p (x, y) ∂nonnegativeVolume

/-- PDF pp.22–23, E21/E28: extended conditional mean from p(y|x)=p(x,y)/p_X(x).
This differs from Advance50.P02.conditionalMean, which is a finite cq entropy.
Zero or infinite marginal-density fibers are null for a probability law and
are assigned zero. Infinite means on positive finite fibers remain infinity. -/
def densityConditionalMean (p : ℝ × ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  let px := firstMarginalDensity p x
  if px = 0 ∨ px = ⊤ then 0
  else ∫⁻ y, ENNReal.ofReal y * (p (x, y) / px) ∂nonnegativeVolume

example : quadrantLaw (fun _ => 0) = 0 := by
  simp [quadrantLaw]

example (x : ℝ) : firstMarginalDensity (fun _ => 0) x = 0 := by
  simp [firstMarginalDensity]

example (x : ℝ) : densityConditionalMean (fun _ => 0) x = 0 := by
  simp [densityConditionalMean, firstMarginalDensity]

/-- PDF pp.17–18, D26: plug-in one-symbol entropy in bits. -/
def empiricalEntropy {d n : ℕ} (word : Fin n → Fin (2 ^ d)) : ℝ :=
  -∑ a, empiricalFrequency word a * Real.logb 2 (empiricalFrequency word a)

/-- PDF pp.17–18: iid event probability with actual product weights from p. -/
def iidWordProbability {d : ℕ} (p : Fin (2 ^ d) → ℝ) (n : ℕ)
    (event : (Fin n → Fin (2 ^ d)) → Prop) : ℝ :=
  ∑ word : Fin n → Fin (2 ^ d), if event word then ∏ i, p (word i) else 0

example {d n : ℕ} (a : Fin (2 ^ d)) :
    empiricalFrequency (fun _ : Fin n => a) a = (n : ℝ) / n := by
  simp [empiricalFrequency]

example {d : ℕ} (p : Fin (2 ^ d) → ℝ) (n : ℕ) :
    iidWordProbability p n (fun _ => False) = 0 := by
  simp [iidWordProbability]

example {d : ℕ} (word : Fin 0 → Fin (2 ^ d)) : empiricalEntropy word = 0 := by
  simp [empiricalEntropy, empiricalFrequency]

end QAlgorithms.Papers.Independent.Intake100.P61


