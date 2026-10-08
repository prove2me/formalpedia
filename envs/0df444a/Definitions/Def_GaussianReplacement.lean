-- Prove2me | Definitions.Def_GaussianReplacement
-- name    : GaussianReplacement
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:12.982177+00:00
-- url     : https://prove2.me/theorems/abe24710-5acc-402d-bdcd-be55687f8b00
-- statement:
--   This block sets up a framework for replacing a unit-sphere signal by Gaussian random rows and compares information leaked about the signal, and it states six target properties as defined propositions rather than established theorems. Vectors lie in ℝ^d, Sphere(d) is the unit sphere with its normalized uniform probability measure (when d>0), and Rows(k,d) consists of k vectors in ℝ^d, with gaussianRows(k,d) making them independent standard Gaussians. For rows g and s on the sphere, label(g,s) is the vector of inner products ⟨s,g_i⟩. A measure ρ on the sphere has LocalGrowth(a,B) if every closed ball of radius t>0 around any z∈ℝ^d has ρ-mass at most B·t^a. cubeAverage(ρ,g,y,δ) is the ρ-mass of the points whose labels lie within δ of y in every coordinate, divided by (2δ)^k, and exactDensity is the limit of these averages along δ=1/j when it exists and is zero otherwise. AdmissibleDimensions(d,m,r,q) requires m,r,q≥1, m+r<d−1, and r−(q−1)≥1, and momentConstant is e^{Cd}·B·(1+max(log(D/B),0)). MixedMomentMain asserts that there is a constant C>0 such that, for every admissible tuple, finite ρ, and constants B,D>0 with ρ having local growth of order m+r with constant B and of order d−1 with constant D, the q-th moment bound holds: for every sphere point s and δ>0, the m-row average of the r-row average of the cube density, raised to the power q, is at most momentConstant^q. If also ρ is absolutely continuous with respect to the uniform measure, then outside a ρ-null measurable set of s, cube averages converge to the exact density for almost every Gaussian family of m+r rows, the same moment bound holds for the exact density, and when ρ≠0 the exact density is almost surely positive and finite. Information tools include rowInformation, the Kullback-Leibler divergence of a joint law from the product of its marginal with Gaussian rows, shannonEntropy of a discrete law, conditionalMutualInformation of the two coordinates of a pair given a third via conditional kernels, and extendedLogExpectation of the positive log part minus the negative log part. actualExperiment appends r fresh Gaussian rows to a law on (sphere point, message, m rows), actualObservation records the combined rows, message, and labels, and alignedExperiment keeps the sphere point, message, and combined rows. Two structures, ActualRowConclusion and ActualRowSourceConclusion, package conclusions: finite row information bounded by message entropy, absolutely continuous conditional label laws, almost sure convergence of cube averages to the exact density, integrable and bounded expected log(1+density) by information divided by q plus an averaged log(1+momentBound with constant 9), and a bound on the extended log expectation. Three comparison propositions follow, each asserting that for large d and a probability law whose sphere-and-row marginal is uniform times Gaussian, exposedInformation with fully fresh Gaussian rows is at most that of the aligned experiment plus an error. The critical version uses d/10 rows, extends to d/2 rows, requires entropy at most d², and has error Kd. The one-level version uses d/32 up to d/4 rows with a finite message type and an entropy-dependent error. The two-label version uses d/8 up to d/2 rows, entropy at most d², and error Cd. For a kernel κ, blockLaw, endingSignalLaw, freshInformation, and averagedFreshInformation, an average over k from (d+3)/4 to d/2, are defined. HybridBlockMain bounds the increase in averaged information after one block by an entropy-dependent amount, and by C'd when the entropy bound is at most d². FiberBlockMain bounds freshInformation at d/3 rows after a block with d/10 rows by its prior value plus Kd. Finally, a spherical fiber kernel and left and right two-point measures are defined, and FiberTwoPointMain asserts that for 1≤k<d−1 they are finite and equal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianReplacement.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianReplacement.lean; bytes 16..22013
-- Kind: block; original declaration names preserved; body compatibility edits recorded in manifest.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda.
-- Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at
-- d13f23b723b8a846827a245b89c10fc7d3f11612 records the alias (2026-08-20).
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InformationTheory
open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

namespace CurrentProjection

abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev Sphere (d : ℕ) := Metric.sphere (0 : Vector d) 1

abbrev Rows (k d : ℕ) := Fin k → Vector d

def uniformSphere (d : ℕ) : Measure (Sphere d) :=
  let σ := (volume : Measure (Vector d)).toSphere
  (σ Set.univ)⁻¹ • σ

def gaussianRows (k d : ℕ) : Measure (Rows k d) :=
  Measure.pi fun _ => stdGaussian (Vector d)

def label {k d : ℕ} (g : Rows k d) (s : Vector d) : Fin k → ℝ :=
  fun i => ⟪s, g i⟫

def LocalGrowth {d : ℕ} (ρ : Measure (Sphere d)) (a : ℕ) (B : ℝ) : Prop :=
  ∀ z : Vector d, ∀ t : ℝ, 0 < t →
    ρ {u | dist (u : Vector d) z ≤ t} ≤ ENNReal.ofReal (B * t ^ a)

def cubeAverage {k d : ℕ} (ρ : Measure (Sphere d)) (g : Rows k d)
    (y : Fin k → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * δ)⁻¹ ^ k) *
    ρ {u | ∀ i, |label g (u : Vector d) i - y i| ≤ δ}

def exactDensity {k d : ℕ} (ρ : Measure (Sphere d)) (g : Rows k d)
    (y : Fin k → ℝ) : ℝ≥0∞ := by
  classical
  let f := fun j : ℕ => (cubeAverage ρ g y (1 / (j : ℝ))).toReal
  exact if h : ∃ L : ℝ, Tendsto f atTop (𝓝 L) then ENNReal.ofReal h.choose else 0

def AdmissibleDimensions (d m r q : ℕ) : Prop :=
  1 ≤ m ∧ 1 ≤ r ∧ 1 ≤ q ∧ m + r < d - 1 ∧ m + r - m - (q - 1) ≥ 1

def momentConstant (C : ℝ) (d : ℕ) (B D : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (C * d) * B * (1 + max (Real.log (D / B)) 0))

def MixedMomentMain : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (d m r q : ℕ), AdmissibleDimensions d m r q →
    ∀ (ρ : Measure (Sphere d)), IsFiniteMeasure ρ →
    ∀ (B D : ℝ), 0 < B → 0 < D → LocalGrowth ρ (m+r) B → LocalGrowth ρ (d-1) D →
    (∀ (s : Sphere d) (δ : ℝ), 0 < δ →
      (∫⁻ X, (∫⁻ Z, cubeAverage ρ (Fin.append X Z)
        (label (Fin.append X Z) (s : Vector d)) δ ∂gaussianRows r d)^q
          ∂gaussianRows m d) ≤ (momentConstant C d B D)^q) ∧
    (ρ ≪ uniformSphere d → ∃ E : Set (Sphere d), MeasurableSet E ∧ ρ E = 0 ∧
      ∀ s ∉ E,
        (∀ᵐ G ∂gaussianRows (m+r) d,
          Tendsto (fun δ : ℝ => cubeAverage ρ G (label G (s : Vector d)) δ)
            (𝓝[>] 0) (𝓝 (exactDensity ρ G (label G (s : Vector d))))) ∧
        ((∫⁻ X, (∫⁻ Z, exactDensity ρ (Fin.append X Z)
          (label (Fin.append X Z) (s : Vector d)) ∂gaussianRows r d)^q
            ∂gaussianRows m d) ≤ (momentConstant C d B D)^q) ∧
        (ρ ≠ 0 → ∀ᵐ G ∂gaussianRows (m+r) d,
          0 < exactDensity ρ G (label G (s : Vector d)) ∧
          exactDensity ρ G (label G (s : Vector d)) < ∞))

instance gaussianRows_isProbabilityMeasure (k d : ℕ) : IsProbabilityMeasure (gaussianRows k d) := by
  unfold gaussianRows
  infer_instance

lemma measurable_own_label {k d : ℕ} :
    Measurable (fun z : Rows k d × Sphere d => label z.1 (z.2:Vector d)) := by
  apply Measurable.of_eval
  intro i
  exact (continuous_inner.comp <| (continuous_subtype_val.comp continuous_snd).prodMk
    ((continuous_apply i).comp continuous_fst)).measurable

def swapLast {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] :
    (A × B) × C ≃ᵐ (A × C) × B where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  measurable_invFun := (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd

def rowInformation {S W X : Type*} [MeasurableSpace S] [MeasurableSpace W]
    [MeasurableSpace X] (P : Measure ((S×W)×X)) (γ : Measure X) : ℝ≥0∞ :=
  klDiv P (P.fst.prod γ)

noncomputable def shannonEntropy {W : Type*} [MeasurableSpace W] (π : Measure W) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (-Real.log (π {w}).toReal) ∂π

def conditionalMutualInformation {Z A B : Type*} [MeasurableSpace Z]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B]
    (P : Measure (Z×(A×B))) [IsFiniteMeasure P] : ℝ≥0∞ := by
  classical
  exact if h : Nonempty (A×B) then
    letI := h
    InformationTheory.klDiv P (P.fst ⊗ₘ (P.condKernel.fst ×ₖ P.condKernel.snd))
  else 0

def actualExperiment {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d × W) × Rows m d)) :
    Measure (((Sphere d × W) × Rows m d) × Rows r d) := P.prod (gaussianRows r d)

instance actualExperiment_isProbabilityMeasure {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (actualExperiment (r:=r) P) :=
  inferInstanceAs (IsProbabilityMeasure (P.prod (gaussianRows r d)))

def actualObservation {d m r : ℕ} {W : Type*}
    (p : ((Sphere d × W) × Rows m d) × Rows r d) :
    (Rows (m+r) d × W) × (Fin (m+r) → ℝ) :=
  ((Fin.append p.1.2 p.2,p.1.1.2), label (Fin.append p.1.2 p.2) (p.1.1.1 : Vector d))

instance actualObservation_isProbabilityMeasure {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure ((actualExperiment (r:=r) P).map actualObservation) := by
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  have happ : Measurable
      (fun p : ((Sphere d × W) × Rows m d) × Rows r d => Fin.append p.1.2 p.2) :=
    (Fin.continuous_append m r).measurable.comp
      (measurable_fst.snd.prodMk measurable_snd)
  exact (happ.prodMk measurable_fst.fst.snd).prodMk
    (measurable_own_label.comp (happ.prodMk measurable_fst.fst.fst))

def selectedCube {k d : ℕ} {W : Type*} (ρ : W → Measure (Sphere d)) (δ : ℝ)
    (z : (Rows k d×W)×(Fin k → ℝ)) : ℝ≥0∞ := cubeAverage (ρ z.1.2) z.1.1 z.2 δ

def selectedExact {k d : ℕ} {W : Type*} (ρ : W → Measure (Sphere d))
    (z : (Rows k d×W)×(Fin k → ℝ)) : ℝ≥0∞ := exactDensity (ρ z.1.2) z.1.1 z.2

def momentBound (C : ℝ) (d : ℕ) (B D : ℝ) : ℝ :=
  Real.exp (C*d)*B*(1+max (Real.log (D/B)) 0)

def logPositive (x : ℝ≥0∞) : ℝ := max (Real.log x.toReal) 0

def logNegative (x : ℝ≥0∞) : ℝ≥0∞ := if x = 0 then ∞ else ENNReal.ofReal (-Real.log x.toReal)

def extendedLogExpectation {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (f : A → ℝ≥0∞) : EReal :=
  ((∫⁻ a, ENNReal.ofReal (logPositive (f a)) ∂μ) : EReal) -
    ((∫⁻ a, logNegative (f a) ∂μ) : EReal)

def PositiveMessage {W : Type*} [MeasurableSpace W] (π : Measure W) := {w : W // 0 < π {w}}

def completeFamily {W : Type*} [MeasurableSpace W] {T : Type*} (π : Measure W)
    (f : PositiveMessage π → T) (t₀ : T) (w : W) : T :=
  if h : 0 < π {w} then f ⟨w,h⟩ else t₀

structure ActualRowConclusion {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ρ : W → Measure (Sphere d)) (B D : W → ℝ) : Prop where
  row_finite : rowInformation P (gaussianRows m d) ≠ ∞
  row_le_entropy : (rowInformation P (gaussianRows m d)).toReal ≤
    (shannonEntropy (P.map swapLast).snd).toReal
  conditional_density : ∀ᵐ gw ∂((actualExperiment (r:=r) P).map actualObservation).fst,
    ((actualExperiment (r:=r) P).map actualObservation).condKernel gw ≪ volume
  actual_limit : ∀ᵐ p ∂actualExperiment (r:=r) P,
    Tendsto (fun j : ℕ => selectedCube ρ (1/(j:ℝ)) (actualObservation p)) atTop
      (𝓝 (selectedExact ρ (actualObservation p)))
  smoothed_bound : ∀ δ : ℝ, 0 < δ →
    Integrable (fun p => Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal))
      (actualExperiment (r:=r) P) ∧
    (∫ p, Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
      (rowInformation P (gaussianRows m d)).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  exact_integrable : Integrable (fun p => Real.log (1+(selectedExact ρ (actualObservation p)).toReal))
    (actualExperiment (r:=r) P)
  exact_bound : (∫ p, Real.log (1+(selectedExact ρ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
    (rowInformation P (gaussianRows m d)).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  entropy_bound : (rowInformation P (gaussianRows m d)).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst ≤
    (shannonEntropy (P.map swapLast).snd).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  positive_log_integrable : Integrable (fun p => logPositive (selectedExact ρ (actualObservation p)))
    (actualExperiment (r:=r) P)
  extended_log_bound : extendedLogExpectation (actualExperiment (r:=r) P)
    (fun p => selectedExact ρ (actualObservation p)) ≤
      (((rowInformation P (gaussianRows m d)).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst) : EReal)

def actualConditionalRowInformation {d m : ℕ} {W : Type*} [MeasurableSpace W]
    [StandardBorelSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsFiniteMeasure P] : ℝ≥0∞ :=
  conditionalMutualInformation (P.map (fun p => (p.1.1,(p.2,p.1.2))))

structure ActualRowSourceConclusion {d m r q : ℕ} {W : Type*} [MeasurableSpace W]
    [StandardBorelSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ρ : W → Measure (Sphere d)) (B D : W → ℝ) : Prop where
  row_finite : actualConditionalRowInformation P ≠ ∞
  row_le_entropy : (actualConditionalRowInformation P).toReal ≤
    (shannonEntropy (P.map swapLast).snd).toReal
  conditional_density : ∀ᵐ gw ∂((actualExperiment (r:=r) P).map actualObservation).fst,
    ((actualExperiment (r:=r) P).map actualObservation).condKernel gw ≪ volume
  actual_limit : ∀ᵐ p ∂actualExperiment (r:=r) P,
    Tendsto (fun j : ℕ => selectedCube ρ (1/(j:ℝ)) (actualObservation p)) atTop
      (𝓝 (selectedExact ρ (actualObservation p)))
  smoothed_bound : ∀ δ : ℝ, 0 < δ →
    Integrable (fun p => Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal))
      (actualExperiment (r:=r) P) ∧
    (∫ p, Real.log (1+(selectedCube ρ δ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
      (actualConditionalRowInformation P).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  exact_integrable : Integrable (fun p => Real.log (1+(selectedExact ρ (actualObservation p)).toReal))
    (actualExperiment (r:=r) P)
  exact_bound : (∫ p, Real.log (1+(selectedExact ρ (actualObservation p)).toReal) ∂actualExperiment (r:=r) P) ≤
    (actualConditionalRowInformation P).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  entropy_bound : (actualConditionalRowInformation P).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst ≤
    (shannonEntropy (P.map swapLast).snd).toReal/q +
      ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst
  positive_log_integrable : Integrable (fun p => logPositive (selectedExact ρ (actualObservation p)))
    (actualExperiment (r:=r) P)
  extended_log_bound : extendedLogExpectation (actualExperiment (r:=r) P)
    (fun p => selectedExact ρ (actualObservation p)) ≤
      (((actualConditionalRowInformation P).toReal/q +
        ∫ sw : Sphere d×W, Real.log (1+momentBound 9 d (B sw.2) (D sw.2)) ∂P.fst) : EReal)

def alignedExperiment {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) : Measure ((Sphere d×W)×Rows (m+r) d) :=
  (actualExperiment (r:=r) P).map (fun p => (p.1.1,Fin.append p.1.2 p.2))

instance alignedExperiment_probability {d m r : ℕ} {W : Type*} [MeasurableSpace W]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (alignedExperiment (r:=r) P) := by
  unfold alignedExperiment
  apply Measure.isProbabilityMeasure_map
  exact (measurable_fst.fst.prodMk
    ((Fin.continuous_append m r).measurable.comp
      (measurable_fst.snd.prodMk measurable_snd))).aemeasurable

def exposedJointMap {d k : ℕ} {W : Type*} (p : (Sphere d×W)×Rows k d) :
    (Rows k d×(Fin k → ℝ))×(Sphere d×W) := ((p.2,label p.2 (p.1.1:Vector d)),p.1)

def exposedInformation {d k : ℕ} {W : Type*} [MeasurableSpace W] [StandardBorelSpace W]
    (P : Measure ((Sphere d×W)×Rows k d)) [IsFiniteMeasure P] : ℝ≥0∞ :=
  conditionalMutualInformation (P.map exposedJointMap)

def CriticalComparisonMain : Prop :=
  ∃ (K : ℝ) (d₀ : ℕ), 0 < K ∧ ∀ (d : ℕ), d₀ ≤ d →
    ∀ (W : Type) [MeasurableSpace W] [Countable W] [MeasurableSingletonClass W],
    ∀ (P : Measure ((Sphere d×W)×Rows (d/10) d)) [IsProbabilityMeasure P],
    (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/10) d) →
    shannonEntropy (P.map swapLast).snd ≤ ENNReal.ofReal ((d:ℝ)^2) →
    exposedInformation (P.fst.prod (gaussianRows (d/10+(d/2-d/10)) d)) ≤
      exposedInformation (alignedExperiment (r:=d/2-d/10) P) + ENNReal.ofReal (K*d)

def OneLevelComparisonMain : Prop :=
  ∃ (C : ℝ) (d₀ : ℕ), 0 < C ∧ ∀ d, d₀ ≤ d →
    ∀ (U : Type) [MeasurableSpace U] [Finite U] [MeasurableSingletonClass U],
    ∀ (P : Measure ((Sphere d×U)×Rows (d/32) d)) [IsProbabilityMeasure P],
    (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/32) d) →
    exposedInformation (P.fst.prod (gaussianRows (d/32+(d/4-d/32)) d)) ≤
      exposedInformation (alignedExperiment (r:=d/4-d/32) P) +
      ENNReal.ofReal (C*((d:ℝ)+Real.log (1+(d:ℝ)+(shannonEntropy P.fst.snd).toReal)+
        (shannonEntropy P.fst.snd).toReal/(d:ℝ)))

def TwoLabelComparisonMain : Prop :=
  ∃ (C : ℝ) (d₀ : ℕ), 0 < C ∧ ∀ d, d₀ ≤ d →
    ∀ (V : Type) [MeasurableSpace V] [Finite V] [MeasurableSingletonClass V],
    ∀ (P : Measure ((Sphere d×V)×Rows (d/8) d)) [IsProbabilityMeasure P],
    (P.map swapLast).fst = (uniformSphere d).prod (gaussianRows (d/8) d) →
    shannonEntropy P.fst.snd ≤ ENNReal.ofReal ((d:ℝ)^2) →
    exposedInformation (P.fst.prod (gaussianRows (d/8+(d/2-d/8)) d)) ≤
      exposedInformation (alignedExperiment (r:=d/2-d/8) P) + ENNReal.ofReal (C*d)

def blockInput {d m : ℕ} {U : Type*} (z : (Sphere d × U) × Rows m d) :
    U × (Rows m d × (Fin m → ℝ)) :=
  (z.1.2, z.2, label z.2 (z.1.1 : Vector d))

lemma measurable_blockInput {d m : ℕ} {U : Type*} [MeasurableSpace U] :
    Measurable (blockInput (d:=d) (m:=m) (U:=U)) := by
  exact measurable_fst.snd.prodMk (measurable_snd.prodMk
    ((measurable_own_label (d:=d) (k:=m)).comp
      (measurable_snd.prodMk measurable_fst.fst)))

def blockLaw {d m : ℕ} {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d × U))
    (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) :
    Measure (((Sphere d × U) × Rows m d) × V) :=
  (P.prod (gaussianRows m d)) ⊗ₘ κ.comap blockInput measurable_blockInput

instance blockLaw_probability {d m : ℕ} {U V : Type*}
    [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d × U)) [IsProbabilityMeasure P]
    (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) [IsMarkovKernel κ] :
    IsProbabilityMeasure (blockLaw P κ) := by
  unfold blockLaw
  infer_instance

def endingSignalLaw {d m : ℕ} {U V : Type*}
    [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d × U))
    (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) : Measure (Sphere d × V) :=
  (blockLaw P κ).map (fun z => (z.1.1.1, z.2))

instance endingSignalLaw_probability {d m : ℕ} {U V : Type*}
    [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure (Sphere d × U)) [IsProbabilityMeasure P]
    (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) [IsMarkovKernel κ] :
    IsProbabilityMeasure (endingSignalLaw P κ) := by
  unfold endingSignalLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_fst.fst.fst.prodMk measurable_snd).aemeasurable

def freshInformation {d : ℕ} {U : Type*} [MeasurableSpace U] [StandardBorelSpace U]
    (P : Measure (Sphere d × U)) [IsFiniteMeasure P] (k : ℕ) : ℝ≥0∞ :=
  exposedInformation (P.prod (gaussianRows k d))

def hybridFirst (d : ℕ) : ℕ := (d+3)/4

def hybridLast (d : ℕ) : ℕ := d/2

def hybridCount (d : ℕ) : ℕ := hybridLast d - hybridFirst d + 1

def averagedFreshInformation {d : ℕ} {U : Type*}
    [MeasurableSpace U] [StandardBorelSpace U]
    (P : Measure (Sphere d × U)) [IsFiniteMeasure P] : ℝ :=
  (∑ k ∈ Finset.Icc (hybridFirst d) (hybridLast d), (freshInformation P k).toReal) /
    hybridCount d

def HybridBlockMain : Prop :=
  ∃ (C C' : ℝ) (d₀ : ℕ), 0 < C ∧ 0 < C' ∧ ∀ d, d₀ ≤ d →
    ∀ m, 1 ≤ m → m ≤ d/8 →
    ∀ (U V : Type) [Fintype U] [Fintype V]
      [MeasurableSpace U] [MeasurableSpace V]
      [MeasurableSingletonClass U] [MeasurableSingletonClass V],
    ∀ (P : Measure (Sphere d × U)) [IsProbabilityMeasure P],
    P.fst = uniformSphere d →
    ∀ (κ : Kernel (U × (Rows m d × (Fin m → ℝ))) V) [IsMarkovKernel κ],
    ∀ (B : ℝ), 0 ≤ B →
    shannonEntropy (endingSignalLaw P κ).snd ≤ ENNReal.ofReal B →
    averagedFreshInformation (endingSignalLaw P κ) - averagedFreshInformation P ≤
      C*m + (m:ℝ) / hybridCount d * (C + B / (d/8:ℕ)) + B / (d/32:ℕ) ∧
    (B ≤ (d:ℝ)^2 →
      averagedFreshInformation (endingSignalLaw P κ) - averagedFreshInformation P ≤ C'*d)

def FiberBlockMain : Prop :=
  ∃ (K : ℝ) (d₀ : ℕ), 0 < K ∧ ∀ d, d₀ ≤ d →
    ∀ (U V : Type) [Fintype U] [Fintype V]
      [MeasurableSpace U] [MeasurableSpace V]
      [MeasurableSingletonClass U] [MeasurableSingletonClass V],
    ∀ (P : Measure (Sphere d×U)) [IsProbabilityMeasure P],
    P.fst = uniformSphere d →
    ∀ (κ : Kernel (U×(Rows (d/10) d×(Fin (d/10)→ℝ))) V) [IsMarkovKernel κ],
    ∀ N : ℕ, 1 ≤ N → Fintype.card V ≤ N → Real.log N ≤ (d:ℝ)^2 →
    freshInformation (endingSignalLaw P κ) (d/3) ≤ freshInformation P (d/3) + ENNReal.ofReal (K*d)

def dependentMapKernel {A B D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace D] (κ : Kernel A B) (f : A×B → D) : Kernel A D :=
  (Kernel.id ×ₖ κ).map f

def fiberObservationLaw (d k : ℕ) : Measure ((Rows k d×(Fin k→ℝ))×Sphere d) :=
  ((gaussianRows k d).prod (uniformSphere d)).map
    (fun z => ((z.1,label z.1 (z.2:Vector d)),z.2))

instance uniformSphere_finite (d : ℕ) : IsFiniteMeasure (uniformSphere d) := by
  constructor
  unfold uniformSphere
  rw [Measure.smul_apply, smul_eq_mul]
  exact lt_of_le_of_lt (ENNReal.inv_mul_le_one _) ENNReal.one_lt_top

instance fiberObservationLaw_finite (d k : ℕ) : IsFiniteMeasure (fiberObservationLaw d k) := by
  unfold fiberObservationLaw
  infer_instance

lemma sphere_standardBorel (d : ℕ) : StandardBorelSpace (Sphere d) :=
  Metric.isClosed_sphere.measurableSet.standardBorel

def sphericalFiberKernel (d k : ℕ) [sphereNonempty : Nonempty (Sphere d)] :
    Kernel (Rows k d×(Fin k→ℝ)) (Sphere d) :=
  @Measure.condKernel (Rows k d×(Fin k→ℝ)) (Sphere d) _ _
    (sphere_standardBorel d) sphereNonempty
    (fiberObservationLaw d k) (fiberObservationLaw_finite d k)

instance sphericalFiberKernel_markov (d k : ℕ) [Nonempty (Sphere d)] :
    IsMarkovKernel (sphericalFiberKernel d k) := by
  unfold sphericalFiberKernel
  infer_instance

def fiberTwoPointLeft (d k : ℕ) [Nonempty (Sphere d)] : Measure (Rows k d×(Sphere d×Sphere d)) :=
  ((((gaussianRows k d).prod (uniformSphere d)).withDensity
    (fun z => exactDensity (uniformSphere d) z.1 (label z.1 (z.2:Vector d)))) ⊗ₘ
    ((sphericalFiberKernel d k).comap (fun z => (z.1,label z.1 (z.2:Vector d)))
      (measurable_fst.prodMk measurable_own_label))).map
    (fun z => (z.1.1,(z.1.2,z.2)))

def perpendicularRow {d : ℕ} (v g : Vector d) : Vector d :=
  letI : NormedAddCommGroup (Vector d) := PiLp.normedAddCommGroup 2 (fun _ : Fin d => ℝ)
  letI : InnerProductSpace ℝ (Vector d) := PiLp.innerProductSpace (fun _ : Fin d => ℝ)
  g - (⟪v,g⟫ / ‖v‖^2) • v

def perpendicularRowsKernel (d k : ℕ) : Kernel (Sphere d×Sphere d) (Rows k d) :=
  dependentMapKernel (Kernel.const (Sphere d×Sphere d) (gaussianRows k d))
    (fun z => fun i => perpendicularRow ((z.1.1:Vector d)-(z.1.2:Vector d)) (z.2 i))

def fiberTwoPointConstant (k : ℕ) : ℝ≥0∞ :=
  letI : OfNat ℝ 2 := @instOfNatAtLeastTwo ℝ 2 Real.instNatCast inferInstance
  letI : Mul ℝ := Real.instMul
  letI : Inv ℝ := Real.instInv
  letI : Pow ℝ ℕ := @NPow.toPow ℝ Real.instMonoid.toNPow
  ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹ ^ k)

def fiberDistanceWeight {d : ℕ} (k : ℕ) (z : Sphere d×Sphere d) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖(z.1:Vector d)-(z.2:Vector d)‖)⁻¹ ^ k

def fiberTwoPointRight (d k : ℕ) : Measure (Rows k d×(Sphere d×Sphere d)) :=
  letI : IsScalarTower ℝ≥0∞ ℝ≥0∞ ℝ≥0∞ := Semigroup.isScalarTower
  fiberTwoPointConstant k •
    Measure.map (Prod.swap : (Sphere d×Sphere d)×Rows k d → Rows k d×(Sphere d×Sphere d))
      (Measure.compProd
        (Measure.withDensity (Measure.prod (uniformSphere d) (uniformSphere d))
          (fiberDistanceWeight k))
        (perpendicularRowsKernel d k))

lemma uniformSphere_probability_of_pos {d : ℕ} (hd : 0 < d) :
    IsProbabilityMeasure (uniformSphere d) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  constructor
  rw [uniformSphere, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.inv_mul_cancel _ (measure_ne_top _ _)
  rw [Measure.toSphere_apply_univ]
  exact mul_ne_zero
    (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := Vector d)).ne')
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne'


def FiberTwoPointMain : Prop :=
  ∀ (d k : ℕ) (_hk : 1 ≤ k) (hkd : k < d-1),
    letI : IsProbabilityMeasure (uniformSphere d) :=
      uniformSphere_probability_of_pos (by omega)
    letI : Nonempty (Sphere d) := nonempty_of_isProbabilityMeasure (uniformSphere d)
    IsFiniteMeasure (fiberTwoPointLeft d k) ∧ IsFiniteMeasure (fiberTwoPointRight d k) ∧
      fiberTwoPointLeft d k = fiberTwoPointRight d k



end CurrentProjection
end
end OAI


