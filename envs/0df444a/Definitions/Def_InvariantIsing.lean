-- Prove2me | Definitions.Def_InvariantIsing
-- name    : InvariantIsing
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:15.383732+00:00
-- url     : https://prove2.me/theorems/9d0da8b0-7518-4f9b-b463-34c14d97b838
-- statement:
--   This block sets up the notation for Ising models on N spins σ∈{±1}^N (spins are Boolean, with spinValue sending true to 1 and false to −1) and for a variational (replica-type) formula for their pressure. logPartition(H) is the log of the average of exp(H) over a finite configuration space. fieldEnergy(c,σ)=Σ c_i σ_i is a linear field energy. For an eigenvalue vector eig and a linear isometry (rotation) U of Euclidean space, rotatedEnergy is (1/2)Σ eig_i (Uσ)_i², and rotatedPressure is the normalized (1/N) log partition of rotatedEnergy plus fieldEnergy; matrixRotation turns an orthogonal matrix into such an isometry, using a proved norm-preservation lemma. An OverlapPath is a monotone function on ℝ with values in [0,1]; with the Lebesgue measure on (0,1), the deficit at r is 1−r−∫max(p(s)−r,0)ds. gaussianOperator(a,v,f) maps f to z↦E f(z+√v g) when a=0 and to a⁻¹ log E exp(a f(z+√v g)) otherwise, with g standard normal. A FieldStep is a finite increasing partition 0=cut₀<…<cut_{d+1}=1 with nonnegative nondecreasing step heights; it gives a step function, increments, and a fieldValue obtained by composing the Gaussian operators starting from log cosh and subtracting half the last height. The entropyFunctional of a path p is the supremum over field steps of fieldValue(h,0)+½∫p·h; spectralFunctional(R,p) is ½∫R(deficit(p,r))dr; variationalFunctional(R) is the infimum over paths of their sum, valued in the extended reals. For a measure μ, measureResolvent is ∫1/(b−y)dμ, measureInverse inverts it to the right of an edge e, and measureR is the R-transform-like function inverse minus 1/x for x>0 and the mean at x≤0. finiteSpectralMeasure builds a weighted sum of Dirac masses and is proved to be a probability measure when the weights are nonnegative and sum to 1; empiricalSpectralLaw is the uniform case, and spectralMinimum and spectralMaximum are extreme eigenvalues. The magnetic extension replaces the free infimum over b by constrainedFieldValue, the infimum of fieldValue(h,b)−bs, grouped with weights γ and magnetizations m into magnetic entropy and variational functionals; finiteMagneticFunctional takes a supremum over rational magnetizations with |m_a|<1 of Σγ_a c_a m_a plus the magnetic variational value. Simple-function approximations of a field law give simpleFieldValue and the limit magneticFieldFunctional(spectral,edge,field), and fieldWassersteinOne is the Wasserstein-1 distance defined via couplings. Further definitions include scaledSpectralLaw, groundStateEnergy as the maximum of the rotated energy over N, thermalVariationalValue (the variational value divided by β), data-based physical pressure with a random orthogonal matrix, ConditionalFieldOrbitLaw (a proposition saying the joint law of data and pressure equals that obtained from the data law and a measure on orthogonal matrices), spectralExcess, and Gaussian pattern objects: Marchenko–Pastur endpoints (1±√α)² with an atom of mass max(1−α,0) at 0, gaussianPatternLimit, Gaussian pattern sums with Hopfield-type pressure (1/N) log average exp(c‖Zᵀσ‖²/(2N)), the corresponding ground energy, and the pattern operator. No main theorem is stated beyond the proved basic lemmas.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InvariantIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InvariantIsing.lean; bytes 16..12402
-- Kind: block; original declaration names preserved; body compatibility edits recorded in manifest.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

-- Lean 4.33 compatibility: matrix measurable structure copied from
-- Mathlib/Analysis/Matrix/MeasurableSpace.lean at
-- d13f23b723b8a846827a245b89c10fc7d3f11612 (Lean 4.34.1).
-- Copyright (c) 2026 Gaëtan Serré. Apache 2.0; author: Gaëtan Serré.
namespace Matrix
instance {m n α : Type*} [MeasurableSpace α] : MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
end Matrix

namespace OAI

/-! All-temperature invariant Ising pressure and its magnetic, random-spectral,
ground-state, and Gaussian-pattern extensions. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Matrix Classical ENNReal
universe u
namespace InvariantIsing

abbrev Spin (N : ℕ) := Fin N → Bool

def spinValue (b : Bool) : ℝ := if b then 1 else -1

def logPartition {X : Type*} [Fintype X] (H : X → ℝ) : ℝ :=
  Real.log ((Fintype.card X : ℝ)⁻¹ * ∑ x, Real.exp (H x))

def fieldEnergy {N : ℕ} (c : Fin N → ℝ) (σ : Spin N) : ℝ :=
  ∑ i, c i * spinValue (σ i)

abbrev Rotation (N : ℕ) :=
  EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)

abbrev Orthogonal (N : ℕ) := Matrix.orthogonalGroup (Fin N) ℝ

def spinVector {N : ℕ} (σ : Spin N) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i => spinValue (σ i))

def rotatedEnergy {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N) (σ : Spin N) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, eig i * (U (spinVector σ) i) ^ 2

def rotatedPressure {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (c : Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * logPartition (fun σ => rotatedEnergy eig U σ + fieldEnergy c σ)


lemma orthogonal_mulVec_norm_sq {N : ℕ} (U : Orthogonal N)
    (v : EuclideanSpace ℝ (Fin N)) :
    ‖WithLp.toLp 2 ((U : Matrix (Fin N) (Fin N) ℝ) *ᵥ v.ofLp)‖ ^ 2 = ‖v‖ ^ 2 := by
  have hU : (U : Matrix (Fin N) (Fin N) ℝ)ᵀ *
      (U : Matrix (Fin N) (Fin N) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp U.property
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [pow_two]
  change ((U : Matrix (Fin N) (Fin N) ℝ) *ᵥ v.ofLp) ⬝ᵥ
      ((U : Matrix (Fin N) (Fin N) ℝ) *ᵥ v.ofLp) = v.ofLp ⬝ᵥ v.ofLp
  rw [← Matrix.dotProduct_transpose_mulVec, Matrix.mulVec_mulVec, hU,
    Matrix.one_mulVec]

def matrixRotation {N : ℕ} (U : Orthogonal N) : Rotation N :=
  { ((WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).trans
      (Matrix.UnitaryGroup.toLinearEquiv U)).trans
      (WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).symm with
    norm_map' := fun v => (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (orthogonal_mulVec_norm_sq U v) }

structure OverlapPath where
  val : ℝ → ℝ
  monotone : Monotone val
  nonneg : ∀ s, 0 ≤ val s
  le_one : ∀ s, val s ≤ 1

instance : CoeFun OverlapPath (fun _ => ℝ → ℝ) := ⟨OverlapPath.val⟩

def pathMeasure : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

def deficit (p : OverlapPath) (r : ℝ) : ℝ :=
  1 - r - ∫ s, max (p s - r) 0 ∂pathMeasure


def gaussianOperator (a v : ℝ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  if a = 0 then ∫ g, f (z + Real.sqrt v * g) ∂gaussianReal 0 1
  else a⁻¹ * Real.log (∫ g, Real.exp (a * f (z + Real.sqrt v * g)) ∂gaussianReal 0 1)

structure FieldStep where
  depth : ℕ
  cut : Fin (depth + 2) → ℝ
  ordered_cut : StrictMono cut
  first : cut 0 = 0
  last : cut (Fin.last (depth + 1)) = 1
  height : Fin (depth + 1) → ℝ
  nonneg : ∀ i, 0 ≤ height i
  ordered_height : Monotone height

def fieldFunction (h : FieldStep) (s : ℝ) : ℝ :=
  ∑ i : Fin (h.depth + 1),
    if h.cut i.castSucc < s ∧ s < h.cut i.succ then h.height i else 0

def fieldIncrement (h : FieldStep) (i : Fin (h.depth + 1)) : ℝ × ℝ :=
  (h.cut i.castSucc, h.height i -
    if hi : i.val = 0 then 0 else h.height ⟨i.val - 1, by omega⟩)

def fieldValue (h : FieldStep) (b : ℝ) : ℝ :=
  ((List.ofFn (fieldIncrement h)).foldr
    (fun av f => gaussianOperator av.1 av.2 f) (fun z => Real.log (Real.cosh z))) b -
    h.height (Fin.last h.depth) / 2

def fieldPairing (p : OverlapPath) (h : FieldStep) : ℝ :=
  ∫ s, p s * fieldFunction h s ∂pathMeasure

def entropyFunctional (p : OverlapPath) : EReal :=
  ⨆ h : FieldStep, ((fieldValue h 0 + fieldPairing p h / 2 : ℝ) : EReal)

def spectralFunctional (R : ℝ → ℝ) (p : OverlapPath) : ℝ :=
  (1 / 2 : ℝ) * ∫ r, R (deficit p r) ∂pathMeasure

def variationalFunctional (R : ℝ → ℝ) : EReal :=
  ⨅ p : OverlapPath, entropyFunctional p + (spectralFunctional R p : EReal)

def measureResolvent (μ : Measure ℝ) (b : ℝ) : ℝ := ∫ y, 1 / (b - y) ∂μ

def measureInverse (μ : Measure ℝ) (e x : ℝ) : ℝ :=
  if h : ∃ b, e < b ∧ measureResolvent μ b = x then h.choose else e

def measureR (μ : Measure ℝ) (e x : ℝ) : ℝ :=
  if 0 < x then measureInverse μ e x - 1 / x else ∫ y, y ∂μ

def finiteSpectralMeasure {ι : Type*} (ρ eig : ι → ℝ) : Measure ℝ :=
  Measure.sum fun a => ENNReal.ofReal (ρ a) • Measure.dirac (eig a)

theorem finiteSpectralMeasure_probability {ι : Type*} [Fintype ι] (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (hsum : ∑ a, ρ a = 1) :
    IsProbabilityMeasure (finiteSpectralMeasure ρ eig) := by
  apply HasSum.isProbabilityMeasure_sum_dirac hρ
  simpa only [hsum] using hasSum_fintype ρ


lemma empiricalSpectralWeight_sum {N : ℕ} (hN : 0 < N) :
    ∑ _i : Fin N, (1 : ℝ)/N=1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

def empiricalSpectralLaw {N : ℕ} (hN : 0 < N) (eig : Fin N → ℝ) : ProbabilityMeasure ℝ :=
  ⟨finiteSpectralMeasure (fun _ => (1 : ℝ)/N) eig,
    finiteSpectralMeasure_probability _ _ (fun _ => by positivity) (empiricalSpectralWeight_sum hN)⟩

def spectralMinimum {n : ℕ} (eig : Fin (n+1) → ℝ) : ℝ :=
  (Finset.univ.image eig).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)

def spectralMaximum {n : ℕ} (eig : Fin (n+1) → ℝ) : ℝ :=
  (Finset.univ.image eig).max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

def magneticBiasObjective (h : FieldStep) (s b : ℝ) : ℝ := fieldValue h b - b * s

def constrainedFieldValue (h : FieldStep) (s : ℝ) : ℝ :=
  sInf (range (magneticBiasObjective h s))

def magneticGroupValue {A : Type*} [Fintype A] (γ m : A → ℝ) (h : FieldStep) : ℝ :=
  ∑ a, γ a * constrainedFieldValue h (m a)


def magneticEntropyFunctional {A : Type*} [Fintype A] (γ m : A → ℝ)
    (p : OverlapPath) : EReal :=
  ⨆ h : FieldStep, ((magneticGroupValue γ m h + fieldPairing p h / 2 : ℝ) : EReal)

def magneticVariationalFunctional {A : Type*} [Fintype A] (R : ℝ → ℝ) (γ m : A → ℝ) : EReal :=
  ⨅ p : OverlapPath, magneticEntropyFunctional γ m p + (spectralFunctional R p : EReal)

def RationalMagnetization (A : Type*) := {m : A → ℚ // ∀ a, |(m a : ℝ)| < 1}

def finiteMagneticFunctional {A : Type*} [Fintype A] (R : ℝ → ℝ) (γ c : A → ℝ) : EReal :=
  ⨆ m : RationalMagnetization A,
    ((∑ a, γ a * c a * (m.val a : ℝ) : ℝ) : EReal) +
      magneticVariationalFunctional R γ (fun a => (m.val a : ℝ))

def finiteIndexWeight {Ω A : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (g : Ω → A) (a : A) : ℝ := P.real (g ⁻¹' {a})

def simpleFieldIndex {Ω : Type*} [MeasurableSpace Ω] (s : SimpleFunc Ω ℝ) (x : Ω) : s.range :=
  ⟨s x,s.mem_range_self x⟩

def simpleFieldWeight {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : SimpleFunc Ω ℝ) :=
  finiteIndexWeight P (simpleFieldIndex s)

abbrev SimpleFieldPositive {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : SimpleFunc Ω ℝ) :=
  {i : s.range // 0 < simpleFieldWeight P s i}

def simpleFieldValue {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (s : SimpleFunc Ω ℝ) (R : ℝ → ℝ) : ℝ :=
  (finiteMagneticFunctional R (fun i : SimpleFieldPositive P s => simpleFieldWeight P s i)
    (fun i => i.val.val)).toReal

def fieldSimpleApproximation (n : ℕ) : SimpleFunc ℝ ℝ :=
  SimpleFunc.approxOn id measurable_id (range (id : ℝ → ℝ) ∪ {0}) 0 (by simp) n

def magneticFieldFunctional (spectral : Measure ℝ) (edge : ℝ) (field : ProbabilityMeasure ℝ) : ℝ :=
  limUnder atTop (fun n => simpleFieldValue (field : Measure ℝ) (fieldSimpleApproximation n)
    (measureR spectral edge))

structure FieldLawCoupling (μ ν : ProbabilityMeasure ℝ) where
  law : ProbabilityMeasure (ℝ × ℝ)
  fst : (law : Measure (ℝ × ℝ)).map Prod.fst = (μ : Measure ℝ)
  snd : (law : Measure (ℝ × ℝ)).map Prod.snd = (ν : Measure ℝ)

def FieldLawCoupling.cost {μ ν : ProbabilityMeasure ℝ} (p : FieldLawCoupling μ ν) : ℝ≥0∞ :=
  ∫⁻ xy, ENNReal.ofReal |xy.1-xy.2| ∂(p.law : Measure (ℝ × ℝ))

def fieldWassersteinOne (μ ν : ProbabilityMeasure ℝ) : ℝ≥0∞ :=
  ⨅ p : FieldLawCoupling μ ν, p.cost

def scaledSpectralLaw (ν : ProbabilityMeasure ℝ) (β : ℝ) : ProbabilityMeasure ℝ :=
  ν.map (f := fun x => β*x) ((measurable_const.mul measurable_id).aemeasurable)

def groundStateEnergy {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N) : ℝ :=
  (N : ℝ)⁻¹ * Finset.univ.sup' Finset.univ_nonempty (rotatedEnergy eig U)

def thermalVariationalValue (ν : ProbabilityMeasure ℝ) (b β : ℝ) : ℝ :=
  (variationalFunctional (measureR (scaledSpectralLaw ν β : Measure ℝ) (β*b))).toReal/β

abbrev FieldSpectralData (N : ℕ) := (Fin N → ℝ) × (Fin N → ℝ)

def dataPhysicalPressure {N : ℕ} (d : FieldSpectralData N) (U : Orthogonal N) : ℝ :=
  rotatedPressure d.1 (matrixRotation U⁻¹) d.2

def ConditionalFieldOrbitLaw {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (d : Ω → FieldSpectralData N) (pressure : Ω → ℝ)
    (H : Measure (Orthogonal N)) : Prop :=
  P.map (fun ω => (d ω,pressure ω)) =
    ((P.map d).prod H).map (fun z => (z.1,dataPhysicalPressure z.1 z.2))

def spectralExcess {N : ℕ} (eig : Fin N → ℝ) (a b : ℝ) : ℝ :=
  (insert 0 (Finset.univ.image (fun i => max (a-eig i) (eig i-b)))).max'
    (Finset.insert_nonempty 0 _)


@[irreducible] def gaussianPatternCount (α : ℝ) (N : ℕ) : ℕ := ⌊α*N⌋₊

def marchenkoPasturA (α : ℝ) : ℝ := (1-Real.sqrt α)^2

def marchenkoPasturB (α : ℝ) : ℝ := (1+Real.sqrt α)^2

def marchenkoPasturLower (α : ℝ) : ℝ := if α ≤ 1 then 0 else marchenkoPasturA α

def marchenkoPasturMeasure (α : ℝ) : Measure ℝ :=
  ENNReal.ofReal (max (1-α) 0) • Measure.dirac 0 +
    volume.withDensity ((Icc (marchenkoPasturA α) (marchenkoPasturB α)).indicator
      (fun x => ENNReal.ofReal
        (Real.sqrt ((marchenkoPasturB α-x)*(x-marchenkoPasturA α))/(2*Real.pi*x))))

def gaussianPatternLimit (α c : ℝ) : ℝ :=
  (variationalFunctional (measureR ((marchenkoPasturMeasure α).map (fun x => c*x))
    (max (c*marchenkoPasturLower α) (c*marchenkoPasturB α)))).toReal


def gaussianPatternArray {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    Matrix (Fin N) (Fin m) ℝ := fun i j => z (i,j)

def gaussianPatternSum {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) (σ : Spin N) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 ((gaussianPatternArray z)ᵀ *ᵥ (fun i => spinValue (σ i)))

def gaussianPatternPressure {N m : ℕ} (c : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : ℝ :=
  (N : ℝ)⁻¹*logPartition (fun σ : Spin N => c/(2*N)*‖gaussianPatternSum z σ‖^2)


def gaussianPatternGroundEnergy {N m : ℕ} (ε : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) : ℝ :=
  (N : ℝ)⁻¹*Finset.univ.sup' Finset.univ_nonempty
    (fun σ : Spin N => ε/(2*N)*‖gaussianPatternSum z σ‖^2)


def gaussianPatternColumn {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m))
    (i : Fin N) : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun j => z (i,j))

def gaussianPatternOperator {N m : ℕ} (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    ((gaussianPatternArray z)ᵀ.mulVecLin.toContinuousLinearMap)



end InvariantIsing
end
end OAI


