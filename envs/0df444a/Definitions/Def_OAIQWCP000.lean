-- Prove2me | Definitions.Def_OAIQWCP000
-- name    : OAIQWCP000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T16:57:46.493691+00:00
-- url     : https://prove2.me/theorems/8e703f08-ec3c-4856-a3f0-37a9307bb88d
-- title:
--   OpenAI Gaussian replacement split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof that replacing the Gaussian rows used to select a message by independent rows raises the remaining conditional information by at most $O(d)$ (`OAI.CurrentProjection.criticalComparisonMain`). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Probability/GaussianReplacement` (OpenAI, *Replacing Gaussian observations in memory-constrained inference*, OpenAI Math Release, September 27, 2026, result family 140, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are the critical refinement of a message (`criticalRadius`, `ballRatio`, `criticalIndex`, `criticalMass`, `criticalLevel`, `criticalRefinement`, `criticalSignal`), the message posterior `messagePosterior` and the refinement `refineSignal`, together with the geometric and Gaussian helpers the proofs define. The bundle also contains the lemmas those definitions use in their bodies.
--
--   The definitions of the published statement (`uniformSphere`, `gaussianRows`, `label`, `swapLast`, `shannonEntropy`, `rowInformation`, `conditionalMutualInformation`, `actualExperiment`, `alignedExperiment`, `exposedInformation`, `ActualRowConclusion`, `CriticalComparisonMain` and the rest) are not repeated: the bundle imports them from the published bundle `Def_GaussianReplacement`. It imports no other bundle.
--
--   Modules: `ActualRow.lean`, `ConditionalInfo.lean`, `CriticalEntropy.lean`, `CriticalGeometry.lean`, `Density.lean`, `Entropy.lean`, `Geometry.lean`, `Gram.lean`, `Information.lean`, `MixedGeometry.lean`, `MixedReplica.lean`, `Posterior.lean`, `Refinement.lean`, `Sphere.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the three solutions of this split. One proves `OAI.CurrentProjection.actualRowMain` (the paper's Proposition 3.2, already published from OpenAI's comparator file), one proves the published intermediate statement `OAI.CurrentProjection.critical_refined_comparison` from it, and the third proves `OAI.CurrentProjection.criticalComparisonMain` from that. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Replacing Gaussian observations in memory-constrained inference, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 140; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Probability/GaussianReplacement at commit adc7f12

import Mathlib
import Definitions.Def_GaussianReplacement

section
-- module Solutions.OAIQW_CurrentProjection.Geometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection




section FrostmanGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


def HasLocalMassBound (ν : Measure E) (a : ℝ) : Prop :=
  ∀ t ∈ ν.support, ∀ r : ℝ, 0 < r →
    ν (Metric.closedBall t r) ≤ ENNReal.ofReal (r ^ a)

end FrostmanGeometry




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.MixedGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection

section MixedGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]


def AmbientGrowth (μ : Measure E) (a : ℕ) (A : ℝ) : Prop :=
  ∀ z : E, ∀ t : ℝ, 0 < t → μ (Metric.closedBall z t) ≤ ENNReal.ofReal (A * t ^ a)

end MixedGeometry


section MixedRadial
variable {E : Type*} [NormedAddCommGroup E] [innerProductSpaceRealE : InnerProductSpace ℝ E]
  [finiteDimensionalRealE : FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def radialShell (s : E) (R : ℝ) : Set E :=
  {u | R / 2 < ‖u - s‖ ∧ ‖u - s‖ ≤ R}



def mixedInverse (s : E) (V : Submodule ℝ E) (m r : ℕ) (u : E) : ℝ≥0∞ :=
  ENNReal.ofReal (‖u-s‖⁻¹ ^ r * (Metric.infDist (u-s) (V : Set E))⁻¹ ^ m)

def shellConstant (h a m r : ℕ) : ℝ := 2 ^ r * (1 + 3 ^ h * 2 ^ (a+m+1))

end MixedRadial


def sphereLift {d : ℕ} (ρ : Measure (Sphere d)) : Measure (Vector d) :=
  ρ.map Subtype.val




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Gram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection

open InnerProductSpace

section GramFactorization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ι : Type*} [Fintype ι]

variable (n : ℕ)
def gsUpper (v : Fin n → E) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  (if i = j then 1 else 0) +
    if i < j then ⟪gramSchmidt ℝ v i, v j⟫ / ‖gramSchmidt ℝ v i‖ ^ 2 else 0

end GramFactorization




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.MixedReplica
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace

section MixedReplica
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [measurableSpaceE : MeasurableSpace E] [borelSpaceE : BorelSpace E]


def mixedReplicaWeight (m r : ℕ) (s : E) {k : ℕ} (v : Fin k → E) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (‖v i-s‖⁻¹ ^ r * ‖gramSchmidt ℝ (fun j => v j-s) i‖⁻¹ ^ m)

end MixedReplica

section FixedGaussianKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


def rowKernel (φ : ℝ → ℝ≥0∞) {m : ℕ} (s u : E) (X : Fin m → E) : ℝ≥0∞ :=
  ∏ j, φ ⟪u-s, X j⟫

end FixedGaussianKernel

end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace





def cubeKernel (δ : ℝ) : ℝ → ℝ≥0∞ :=
  Set.indicator (Set.Icc (-δ) δ) (fun _ => ENNReal.ofReal ((2*δ)⁻¹))

instance sphereLift_isFiniteMeasure {d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ] :
    IsFiniteMeasure (sphereLift ρ) := by unfold sphereLift; infer_instance



def extendedCubeDensity {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d)
    (y : Fin k → ℝ) : ℝ≥0∞ :=
  liminf (fun j : ℕ => cubeAverage ρ G y (1/(j:ℝ))) atTop


def labelLaw {k d : ℕ} (ρ : Measure (Sphere d)) (G : Rows k d) : Measure (Fin k → ℝ) :=
  ρ.map (fun s : Sphere d => label G (s:Vector d))

instance labelLaw_isFiniteMeasure {k d : ℕ} (ρ : Measure (Sphere d)) [IsFiniteMeasure ρ]
    (G : Rows k d) : IsFiniteMeasure (labelLaw ρ G) := by unfold labelLaw; infer_instance




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Sphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace

section SphereBounds
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def unitBallLaw : Measure E :=
  ((volume : Measure E) (Metric.ball 0 1))⁻¹ • volume.restrict (Metric.closedBall 0 1)

def sphereLaw : Measure (Metric.sphere (0 : E) 1) :=
  let σ := (volume : Measure E).toSphere
  (σ Set.univ)⁻¹ • σ

instance unitBallLaw_probability : IsProbabilityMeasure (unitBallLaw : Measure E) := by
  constructor
  rw [unitBallLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    Measure.addHaar_closedBall _ _ (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [one_pow, ENNReal.ofReal_one, one_mul]
  exact ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume 0 zero_lt_one).ne'
    measure_ball_lt_top.ne

instance sphereLaw_probability [Nontrivial E] : IsProbabilityMeasure (sphereLaw (E := E)) := by
  constructor
  rw [sphereLaw, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel _ (measure_ne_top _ _)
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)).ne')
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'

end SphereBounds



open InformationTheory




end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

open InformationTheory



def messagePosterior {S W : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [StandardBorelSpace S] [Nonempty S] (P : Measure (S×W)) [IsFiniteMeasure P] : Kernel W S :=
  (P.map Prod.swap).condKernel

instance messagePosterior_markov {S W : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [StandardBorelSpace S] [Nonempty S] (P : Measure (S×W)) [IsFiniteMeasure P] :
    IsMarkovKernel (messagePosterior P) := by
  unfold messagePosterior
  infer_instance

def refineSignal {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure (S×W)) (e : S×W → E) : Measure (S×(W×E)) :=
  P.map (fun p => (p.1,(p.2,e p)))

instance refineSignal_finite {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure (S×W)) [IsFiniteMeasure P] (e : S×W → E) : IsFiniteMeasure (refineSignal P e) := by
  unfold refineSignal
  infer_instance

def natIntEquivNatNat : (ℕ×ℤ) ≃ᵐ (ℕ×ℕ) where
  toEquiv := (Equiv.refl ℕ).prodCongr Equiv.intEquivNat
  measurable_toFun := measurable_of_countable _
  measurable_invFun := measurable_of_countable _



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.ActualRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def actualRowsSignal {d m r : ℕ} {W : Type*}
    (p : ((Sphere d × W) × Rows m d) × Rows r d) : Rows (m+r) d × Sphere d :=
  (Fin.append p.1.2 p.2,p.1.1.1)

instance completeFamily_finite {W : Type*} [MeasurableSpace W] {d : ℕ}
    (π : Measure W) (ρ : PositiveMessage π → Measure (Sphere d))
    [hρ : ∀ w, IsFiniteMeasure (ρ w)] (w : W) : IsFiniteMeasure (completeFamily π ρ 0 w) := by
  unfold completeFamily
  split_ifs with h
  · exact hρ ⟨w,h⟩
  · infer_instance



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.ConditionalInfo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory




def swapAssoc {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B] :
    Z×(A×B) ≃ᵐ (Z×B)×A :=
  ((MeasurableEquiv.refl Z).prodCongr MeasurableEquiv.prodComm).trans MeasurableEquiv.prodAssoc.symm


def mutualInformation {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure (A×B)) : ℝ≥0∞ := klDiv P (P.fst.prod P.snd)





end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.CriticalGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory




def criticalRadius (j : ℕ) : ℝ := 2 * (1/2:ℝ)^j

def ballRatio {d : ℕ} (F : Measure (Sphere d)) (ℓ : ℕ) (s : Sphere d) (j : ℕ) : ℝ :=
  (F {x | dist (x:Vector d) (s:Vector d) ≤ criticalRadius j}).toReal / criticalRadius j ^ ℓ

lemma measurable_ballRatio {d : ℕ} (F : Measure (Sphere d)) [SFinite F] (ℓ j : ℕ) :
    Measurable (fun s => ballRatio F ℓ s j) := by
  have hm : MeasurableSet {p : Sphere d × Sphere d |
      dist (p.2:Vector d) (p.1:Vector d) ≤ criticalRadius j} :=
    measurableSet_le (by fun_prop) measurable_const
  exact (measurable_measure_prodMk_left hm).ennreal_toReal.div_const _


def criticalIndex {d : ℕ} (F : Measure (Sphere d)) (ℓ : ℕ) (s : Sphere d) : ℕ := by
  classical
  exact if h : ∃ j, ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j then Nat.find h else 0

def criticalMass {d : ℕ} (F : Measure (Sphere d)) (ℓ : ℕ) (s : Sphere d) : ℝ :=
  ballRatio F ℓ s (criticalIndex F ℓ s)

def criticalLevel {d : ℕ} (F : Measure (Sphere d)) (ℓ : ℕ) (s : Sphere d) : ℤ :=
  ⌈Real.log (criticalMass F ℓ s)⌉

lemma measurable_criticalIndex {d : ℕ} (F : Measure (Sphere d)) [SFinite F] (ℓ : ℕ) :
    Measurable (criticalIndex F ℓ) := by
  classical
  have hp (j : ℕ) : MeasurableSet {s | ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_ballRatio F ℓ i) (measurable_ballRatio F ℓ j))
  have he : MeasurableSet {s | ∃ j, ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j} := by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion hp
  apply measurable_to_countable'
  intro j
  change MeasurableSet {s | criticalIndex F ℓ s = j}
  by_cases hj : j = 0
  · subst j
    have hset : {s | criticalIndex F ℓ s = 0} =
        {s | ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s 0} ∪
        {s | ¬ ∃ j, ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j} := by
      ext s
      simp only [criticalIndex,mem_ofPred_eq,mem_union]
      split_ifs with h
      · simp [Nat.find_eq_zero,h]
      · simp [h]
    rw [hset]
    exact (hp 0).union he.compl
  · have hset : {s | criticalIndex F ℓ s = j} =
        {s | ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s j} ∩
        ⋂ k < j, {s | ¬ ∀ i, ballRatio F ℓ s i ≤ ballRatio F ℓ s k} := by
      ext s
      simp only [criticalIndex,mem_ofPred_eq,mem_inter_iff,mem_iInter]
      split_ifs with h
      · exact Nat.find_eq_iff h
      · simp only [eq_comm (a:=0),hj,false_iff,not_and]
        intro hs
        exact False.elim (h ⟨j,hs⟩)
    rw [hset]
    exact (hp j).inter (MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => (hp k).compl)))

lemma measurable_criticalMass {d : ℕ} (F : Measure (Sphere d)) [SFinite F] (ℓ : ℕ) :
    Measurable (criticalMass F ℓ) := by
  have hm : Measurable (fun p : Sphere d × ℕ => ballRatio F ℓ p.1 p.2) :=
    measurable_from_prod_countable_left (measurable_ballRatio F ℓ)
  have hpair : Measurable (fun s : Sphere d => (s,criticalIndex F ℓ s)) :=
    measurable_id.prodMk (measurable_criticalIndex F ℓ)
  have hcomp := hm.comp hpair
  change Measurable (fun s => ballRatio F ℓ s (criticalIndex F ℓ s))
  exact hcomp

lemma measurable_criticalLevel {d : ℕ} (F : Measure (Sphere d)) [SFinite F] (ℓ : ℕ) :
    Measurable (criticalLevel F ℓ) := (measurable_criticalMass F ℓ).log.ceil


def criticalClass {d : ℕ} (F : Measure (Sphere d)) (ℓ j : ℕ) (q : ℤ) : Set (Sphere d) :=
  {s | criticalIndex F ℓ s = j ∧ criticalLevel F ℓ s = q}


def criticalPosterior {d : ℕ} (F : Measure (Sphere d)) (ℓ j : ℕ) (q : ℤ) : Measure (Sphere d) :=
  (F (criticalClass F ℓ j q))⁻¹ • F.restrict (criticalClass F ℓ j q)



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.CriticalEntropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def criticalRefinement {d : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ)
    (p : Sphere d×W) : ℕ×ℤ :=
  (criticalIndex (messagePosterior P p.2) ℓ p.1, criticalLevel (messagePosterior P p.2) ℓ p.1)

lemma measurable_criticalRefinement {d : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] [Countable W] [MeasurableSingletonClass W]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ) :
    Measurable (criticalRefinement P ℓ) := by
  apply measurable_from_prod_countable_left
  intro w
  exact (measurable_criticalIndex (messagePosterior P w) ℓ).prodMk
    (measurable_criticalLevel (messagePosterior P w) ℓ)

def projectionJoint {d k : ℕ} (ρ : Measure (Sphere d)) (μ : Measure (Rows k d)) :
    Measure (Rows k d×(Fin k→ℝ)) :=
  (μ.prod ρ).map (fun z => (z.1,label z.1 (z.2:Vector d)))

def projectionSquare {k d : ℕ} (G : Rows k d) (v : Vector d) : ℝ := ∑ i, (label G v i)^2

def normalizer (R : ℝ) : ℝ := Real.sqrt (2*Real.pi*(R^2))

def radiusVariance (R : ℝ) : ℝ≥0 := ⟨R^2,sq_nonneg R⟩

def gaussianProductPDF {k : ℕ} (R : ℝ) (c y : Fin k → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal (c i) (radiusVariance R) (y i)

def coverPDF {k d : ℕ} (C : Finset (Sphere d)) (R : ℝ) (G : Rows k d) (y : Fin k→ℝ) : ℝ :=
  (C.card:ℝ)⁻¹ * ∑ c ∈ C, gaussianProductPDF R (label G (c:Vector d)) y



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Information
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory



def observedMessageMap {d k : ℕ} {W : Type*} (p : (Sphere d×W)×Rows k d) :
    (Rows k d×(Fin k→ℝ))×W := ((p.2,label p.2 (p.1.1:Vector d)),p.1.2)

def observedMessage {d k : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) : Measure ((Rows k d×(Fin k→ℝ))×W) :=
  P.map observedMessageMap

def posteriorProjectionKernel {d k : ℕ} {W : Type*} [MeasurableSpace W]
    [Nonempty (Sphere d)] (P : Measure (Sphere d×W)) [IsFiniteMeasure P]
    (γ : Measure (Rows k d)) : Kernel W (Rows k d×(Fin k→ℝ)) :=
  (messagePosterior P ×ₖ Kernel.const W γ).map
    (fun z : Sphere d×Rows k d => (z.2,label z.2 (z.1:Vector d)))



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Refinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


lemma refineSignal_probability {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace E] (P : Measure (S×W)) [IsProbabilityMeasure P]
    (e : S×W → E) (he : Measurable e) : IsProbabilityMeasure (refineSignal P e) := by
  unfold refineSignal
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_fst.prodMk (measurable_snd.prodMk he)).aemeasurable).mpr inferInstance

def refinementLoss {S W E : Type*} [MeasurableSpace S] [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure (S×W)) (e : S×W → E) (v : W×E) : ℝ :=
  -Real.log ((refineSignal P e).snd {v}).toReal + Real.log (P.snd {v.1}).toReal



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Posterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory


def criticalSignal {d : ℕ} {W : Type*} [MeasurableSpace W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ) : Measure (Sphere d×(W×(ℕ×ℤ))) :=
  refineSignal P (criticalRefinement P ℓ)

instance criticalSignal_probability {d : ℕ} {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsProbabilityMeasure P] (ℓ : ℕ) :
    IsProbabilityMeasure (criticalSignal P ℓ) :=
  refineSignal_probability P _ (measurable_criticalRefinement P ℓ)

def criticalB {d : ℕ} {W : Type*} [MeasurableSpace W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ) (v : W×(ℕ×ℤ)) : ℝ :=
  Real.exp ((v.2.2:ℝ)+(ℓ:ℝ)*Real.log 4+refinementLoss P (criticalRefinement P ℓ) v)

def criticalD {d : ℕ} {W : Type*} [MeasurableSpace W] [Nonempty (Sphere d)]
    (P : Measure (Sphere d×W)) [IsFiniteMeasure P] (ℓ : ℕ) (v : W×(ℕ×ℤ)) : ℝ :=
  Real.exp (-Real.log ((criticalSignal P ℓ).snd {v}).toReal)*(3*4^d)



def refineRows {d m : ℕ} {W E : Type*} [MeasurableSpace W] [MeasurableSpace E]
    (P : Measure ((Sphere d×W)×Rows m d)) (e : Sphere d×W → E) :
    Measure ((Sphere d×(W×E))×Rows m d) :=
  P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))



end CurrentProjection

end

end OAI
end


