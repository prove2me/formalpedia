-- Prove2me | Definitions.Def_erdos146_core2
-- name    : erdos146_core2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-04T04:38:33.29259+00:00
-- url     : https://prove2.me/theorems/f13edd47-6ef6-4135-95a3-9117d974e061
-- title:
--   Degeneracy counterexample: child arrays, Hamming-ball host and the sampling thresholds
-- statement:
--   Second of two parts of the definitional core for the refutation of Erdős's 2-degenerate extremal conjecture (Erdős problem #146), transplanted from Chapter 10 of OpenAI's *Ten Advances in Mathematics and Theoretical Computer Science*. It imports the first part and completes the construction.
--
--   **Parent and child arrays.** A parent array $u = (u_a)_{a=1}^{L} \in U^L$ and a child array $z = (z_{\{a,b\}})$ indexed by pairs, with their coordinate kernels, mismatch counts, entropy potentials and average disagreement. The exclusion argument runs on the conditional-entropy functional $E(u,z) = \frac{1}{m}\sum_{j=1}^{m} H(Z_j \mid X_j, Y_j)$ of Section 7, where a parent pair is drawn uniformly and oriented by an independent fair coin. The thresholds are $A(\tau) = \kappa + \tau\log_2 3$ and $C(\tau) = 2h(\tau) - 1$, and the construction needs a sampling exponent $\beta$ with $A(\tau) < \beta < C(\tau)$. The *bad* child arrays are those of entropy at most $\beta - \delta$, which Lemma 7.1 excludes with probability at least $1 - 2s\,2^{-m}$.
--
--   **The sampled Hamming-ball host.** The host is the sampled Hamming-ball graph of Section 7: with $U = \{0,1\}^m$, two disjoint copies $U_L, U_R$ are joined whenever their Hamming distance is at most $k = \lfloor \tau m \rfloor$, and each vertex is retained independently with probability $p = 2^{-\beta m}$. This part defines the Hamming ball and its cardinality, the host graph, the retention measure, and the expected retained vertex and edge counts together with their second moments — the input to the second-moment argument that gives the host $\Omega(n^{3/2+\varepsilon})$ edges.
--
--   **Thresholds.** The Hamming radius $\tau$, the sampling exponent, the entropy gap and the extremal power $3/2 + \varepsilon$ of Theorem 1.2, in the explicit numerical form the manuscript fixes.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L12944-L18134

import Definitions.Def_erdos146_core1
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.InformationTheory.Hamming
import Mathlib.Probability.Distributions.SetBernoulli

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem pairTypeGroupChildOnes_card_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    (pairTypeGroupChildOnes parents children coordinate bitType).card ≤
      (pairTypeGroup parents coordinate bitType).card := by
  classical
  unfold pairTypeGroupChildOnes
  exact Finset.card_filter_le _ _

def flattenPairChildArray
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    PairLayer parentCount 1 × Fin dimension → Bool :=
  fun index => children index.1 index.2

theorem pairChildClassificationOnes_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (bitType : PairBitType) (coordinate : Fin dimension) :
    (classifiedWordOnes
      (pairCoordinateClassification parents) (bitType, coordinate)
      (flattenPairChildArray children)).card =
        (pairTypeGroupChildOnes parents children coordinate bitType).card := by
  classical
  apply Finset.card_bij (fun index _ => index.1)
  · intro index hindex
    have hclassified :
        index ∈
          (classificationGroup (pairCoordinateClassification parents)
            (bitType, coordinate)).filter
              (fun candidate =>
                flattenPairChildArray children candidate = true) := by
      simpa only [classifiedWordOnes] using hindex
    have hparts := Finset.mem_filter.mp hclassified
    have hgroup := (Finset.mem_filter.mp hparts.1).2
    have htype := congrArg Prod.fst hgroup
    have hcoordinate := congrArg Prod.snd hgroup
    have hcoord : index.2 = coordinate := by
      simpa [pairCoordinateClassification] using hcoordinate
    simp only [pairTypeGroupChildOnes, Finset.mem_filter]
    constructor
    · simp only [pairTypeGroup, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa [pairCoordinateClassification, hcoord] using htype
    · simpa [flattenPairChildArray, hcoord] using hparts.2
  · intro first hfirst second hsecond hequal
    apply Prod.ext
    · exact hequal
    · have hfirst_group :=
        (Finset.mem_filter.mp hfirst).1
      have hsecond_group :=
        (Finset.mem_filter.mp hsecond).1
      have hfirst_class :=
        (Finset.mem_filter.mp hfirst_group).2
      have hsecond_class :=
        (Finset.mem_filter.mp hsecond_group).2
      have hfirst_coordinate := congrArg Prod.snd hfirst_class
      have hsecond_coordinate := congrArg Prod.snd hsecond_class
      simpa [pairCoordinateClassification] using
        hfirst_coordinate.trans hsecond_coordinate.symm
  · intro pair hpair
    refine ⟨(pair, coordinate), ?_, rfl⟩
    have hpair_parts := Finset.mem_filter.mp hpair
    have hpair_type := (Finset.mem_filter.mp hpair_parts.1).2
    change
      (pair, coordinate) ∈
        (classificationGroup (pairCoordinateClassification parents)
          (bitType, coordinate)).filter
            (fun index => flattenPairChildArray children index = true)
    apply Finset.mem_filter.mpr
    constructor
    · unfold classificationGroup
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact Prod.ext hpair_type rfl
    · exact hpair_parts.2

noncomputable def pairChildCountProfile
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    PairTypeCountProfile parentCount dimension := by
  intro bitType coordinate
  refine ⟨(pairTypeGroupChildOnes parents children coordinate bitType).card, ?_⟩
  have hones := pairTypeGroupChildOnes_card_le
    parents children coordinate bitType
  have hgroup := pairTypeGroup_card_le parents coordinate bitType
  omega

noncomputable def pairChildArraysOfProfile
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    Finset (PairLayer parentCount 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => pairChildCountProfile parents children = profile)

noncomputable def pairChildArraysOfProfileEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : PairTypeCountProfile parentCount dimension) :
    ↥(pairChildArraysOfProfile parents profile) ≃
      ↥(classifiedBooleanWords
        (pairCoordinateClassification parents)
        (fun index : PairBitType × Fin dimension =>
          (profile index.1 index.2).val)) := by
  classical
  refine
    { toFun := fun children =>
        ⟨flattenPairChildArray children.val, ?_⟩
      invFun := fun word =>
        ⟨fun pair coordinate => word.val (pair, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership := children.property
    unfold pairChildArraysOfProfile at hmembership
    have hprofile := (Finset.mem_filter.mp hmembership).2
    simp only [classifiedBooleanWords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rintro ⟨bitType, coordinate⟩
    rw [pairChildClassificationOnes_card]
    have hcount := congrArg
      (fun candidate : PairTypeCountProfile parentCount dimension =>
        (candidate bitType coordinate).val) hprofile
    simpa [pairChildCountProfile] using hcount
  · simp only [pairChildArraysOfProfile, Finset.mem_filter,
      Finset.mem_univ, true_and]
    funext bitType
    funext coordinate
    apply Fin.ext
    change
      (pairTypeGroupChildOnes parents
        (fun pair coordinate => word.val (pair, coordinate))
        coordinate bitType).card = (profile bitType coordinate).val
    have hmembership := word.property
    unfold classifiedBooleanWords at hmembership
    have hprofile :=
      (Finset.mem_filter.mp hmembership).2 (bitType, coordinate)
    rw [← pairChildClassificationOnes_card]
    have hflatten :
        flattenPairChildArray
          (fun pair coordinate => word.val (pair, coordinate)) =
            word.val := by
      funext index
      rcases index with ⟨pair, coordinate⟩
      rfl
    rw [hflatten]
    exact hprofile
  · intro children
    apply Subtype.ext
    funext pair
    funext coordinate
    rfl
  · intro word
    apply Subtype.ext
    funext index
    rcases index with ⟨pair, coordinate⟩
    rfl

noncomputable def pairCoordinateConditionalEntropy
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℝ :=
  ∑ bitType : PairBitType,
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      binaryEntropy
        (((pairTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
          ((pairTypeGroup parents coordinate bitType).card : ℝ))

noncomputable def pairChildArrayEntropy
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    pairCoordinateConditionalEntropy parents children coordinate) /
      (dimension : ℝ)

noncomputable def pairParentCoordinateOneCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) : ℕ :=
  (booleanWordOnes (fun parent => parents parent coordinate)).card

theorem pairParentCoordinateOneCount_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    pairParentCoordinateOneCount parents coordinate ≤ parentCount := by
  classical
  unfold pairParentCoordinateOneCount booleanWordOnes
  calc
    (Finset.univ.filter
      (fun parent : Fin parentCount =>
        parents parent coordinate = true)).card ≤
        (Finset.univ : Finset (Fin parentCount)).card :=
      Finset.card_filter_le _ _
    _ = parentCount := by simp

noncomputable def pairParentCoordinateSupport
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) : Finset (Fin parentCount) := by
  classical
  exact Finset.univ.filter
    (fun parent => parents parent coordinate = outcome)

theorem pairCoordinateBitType_homogeneous_iff
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1)
    (outcome : Bool) :
    pairCoordinateBitType parents coordinate pair =
        (if outcome then (1 : PairBitType) else 0) ↔
      ∀ parent ∈ pair.val, parents parent coordinate = outcome := by
  classical
  obtain ⟨a, b, hab, hp⟩ := Finset.card_eq_two.mp pair.property
  cases outcome <;> cases ha : parents a coordinate <;>
    cases hb : parents b coordinate <;>
    simp_all [pairCoordinateBitType]

noncomputable def pairTypeGroupHomogeneousEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (outcome : Bool) :
    ↥(pairTypeGroup parents coordinate
      (if outcome then (1 : PairBitType) else 0)) ≃
      ↥((pairParentCoordinateSupport parents coordinate outcome).powersetCard 2) := by
  classical
  refine
    { toFun := fun pair => ⟨pair.val.val, ?_⟩
      invFun := fun support =>
        ⟨⟨support.val, ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership := pair.property
    unfold pairTypeGroup at hmembership
    have htype := (Finset.mem_filter.mp hmembership).2
    have hhomogeneous :=
      (pairCoordinateBitType_homogeneous_iff
        parents coordinate pair.val outcome).mp htype
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, pair.val.property⟩
    intro parent hparent
    unfold pairParentCoordinateSupport
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hhomogeneous parent hparent⟩
  · exact (Finset.mem_powersetCard.mp support.property).2
  · unfold pairTypeGroup
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply (pairCoordinateBitType_homogeneous_iff
      parents coordinate
      ⟨support.val, (Finset.mem_powersetCard.mp support.property).2⟩
      outcome).mpr
    intro parent hparent
    have hsubset :=
      (Finset.mem_powersetCard.mp support.property).1
    have hsupport := hsubset hparent
    unfold pairParentCoordinateSupport at hsupport
    exact (Finset.mem_filter.mp hsupport).2
  · intro pair
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro support
    apply Subtype.ext
    rfl

def pairBitTypeOfOutcomes (left right : Bool) : PairBitType :=
  if left = false ∧ right = false then 0
  else if left = true ∧ right = true then 1
  else 2

noncomputable def pairCoordinateKernel
    {parentCount dimension : ℕ}
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : BinaryPairKernel where
  parentProbability :=
    (pairParentCoordinateOneCount parents coordinate : ℝ) /
      (parentCount : ℝ)
  parentProbability_nonneg := by
    positivity
  parentProbability_le_one := by
    have hpositive : 0 < (parentCount : ℝ) := by
      exact_mod_cast hparents
    apply (div_le_one hpositive).mpr
    exact_mod_cast pairParentCoordinateOneCount_le parents coordinate
  childProbability left right :=
    ((pairTypeGroupChildOnes parents children coordinate
      (pairBitTypeOfOutcomes left right)).card : ℝ) /
        ((pairTypeGroup parents coordinate
          (pairBitTypeOfOutcomes left right)).card : ℝ)
  childProbability_nonneg := by
    intro left right
    positivity
  childProbability_le_one := by
    intro left right
    let bitType := pairBitTypeOfOutcomes left right
    have hle := pairTypeGroupChildOnes_card_le
      parents children coordinate bitType
    by_cases hzero : (pairTypeGroup parents coordinate bitType).card = 0
    · simp [bitType, hzero]
    · have hpositive :
          0 < ((pairTypeGroup parents coordinate bitType).card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      apply (div_le_one hpositive).mpr
      exact_mod_cast hle

noncomputable def pairChildCoordinateOneCount
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℕ :=
  (booleanWordOnes (fun pair => children pair coordinate)).card

noncomputable def pairCoordinatePairMismatchCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (pair : PairLayer parentCount 1) : ℕ := by
  classical
  exact (pair.val.filter
    (fun parent =>
      parents parent coordinate ≠ children pair coordinate)).card

noncomputable def pairParentArrayEntropyPotential
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ))) /
      (dimension : ℝ)

noncomputable def pairChildArrayEntropyPotential
    {parentCount dimension : ℕ}
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((pairChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 2 : ℝ))) /
      (dimension : ℝ)

noncomputable def pairChildArrayAverageDisagreement
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    empiricalAverageDisagreement parentCount
      (pairParentCoordinateOneCount parents coordinate)
      (pairCoordinateKernel (by omega) parents children coordinate)) /
    (dimension : ℝ)

noncomputable def badPairChildArrays
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    Finset (PairLayer parentCount 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => pairChildArrayEntropy parents children ≤ threshold)

noncomputable def hammingRetentionProbability (dimension : ℕ) : ℝ :=
  Real.exp (-(midpointBeta * (dimension : ℝ) * Real.log 2))

theorem hammingRetentionProbability_pos (dimension : ℕ) :
    0 < hammingRetentionProbability dimension := by
  unfold hammingRetentionProbability
  exact Real.exp_pos _

theorem hammingRetentionProbability_le_one (dimension : ℕ) :
    hammingRetentionProbability dimension ≤ 1 := by
  unfold hammingRetentionProbability
  apply Real.exp_le_one_iff.mpr
  have hproduct :
      0 ≤ midpointBeta * (dimension : ℝ) * Real.log 2 :=
    mul_nonneg
      (mul_nonneg midpointBeta_pos.le (Nat.cast_nonneg dimension))
      log_two_pos.le
  linarith

noncomputable def hammingRetentionParameter (dimension : ℕ) : unitInterval :=
  ⟨hammingRetentionProbability dimension,
    hammingRetentionProbability_pos dimension |>.le,
    hammingRetentionProbability_le_one dimension⟩

noncomputable def hammingRetentionMeasure (dimension : ℕ) :
    MeasureTheory.Measure (Set (Bool × HammingWord dimension)) :=
  ProbabilityTheory.setBernoulli Set.univ
    (hammingRetentionParameter dimension)

noncomputable def hammingExpectedRetainedVertexCount
    (dimension : ℕ) : ℝ :=
  ∑ vertex : Bool × HammingWord dimension,
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained}

noncomputable def hammingExpectedRetainedVertexSquare
    (dimension : ℕ) : ℝ :=
  ∑ first : Bool × HammingWord dimension,
    ∑ second : Bool × HammingWord dimension,
      (hammingRetentionMeasure dimension).real
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained ∧ second ∈ retained}

noncomputable def hammingRetainedVertexCount
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : ℝ := by
  classical
  exact ∑ vertex : Bool × HammingWord dimension,
    if vertex ∈ retained then 1 else 0

noncomputable def pairChildVertexFinset
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    Finset (Bool × HammingWord dimension) := by
  classical
  exact (Finset.univ : Finset (PairLayer parentCount 1)).image
    (fun pair => (side, children pair))

def pairChildRetentionEvent
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    Set (Set (Bool × HammingWord dimension)) :=
  {retained | ∀ pair, (side, children pair) ∈ retained}

noncomputable def badPairChildRetentionEvent
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) := by
  classical
  exact
    ⋃ children ∈
        (badPairChildArrays parents threshold).filter Function.Injective,
      pairChildRetentionEvent side children

noncomputable def badPairLayerRetentionEvent
    (parentCount dimension : ℕ)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ parents : Fin parentCount → HammingWord dimension,
    badPairChildRetentionEvent parents side threshold

noncomputable def badPairLayersRetentionEvent
    {depth : ℕ}
    (layerSizes : Fin depth → ℕ)
    (dimension : ℕ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ side : Bool, ⋃ layer : Fin depth,
    badPairLayerRetentionEvent (layerSizes layer) dimension side
      (midpointBeta - entropySlack)

noncomputable def hammingDifferenceSet {dimension : ℕ}
    (u v : HammingWord dimension) : Finset (Fin dimension) := by
  classical
  exact Finset.univ.filter (fun coordinate => u coordinate ≠ v coordinate)

noncomputable def hammingFlip {dimension : ℕ}
    (u : HammingWord dimension) (coordinates : Finset (Fin dimension)) :
    HammingWord dimension := by
  classical
  exact fun coordinate =>
    if coordinate ∈ coordinates then !(u coordinate) else u coordinate

theorem hammingDifferenceSet_flip {dimension : ℕ}
    (u : HammingWord dimension) (coordinates : Finset (Fin dimension)) :
    hammingDifferenceSet u (hammingFlip u coordinates) = coordinates := by
  classical
  ext coordinate
  by_cases hcoordinate : coordinate ∈ coordinates
  · simp [hammingDifferenceSet, hammingFlip, hcoordinate]
  · simp [hammingDifferenceSet, hammingFlip, hcoordinate]

theorem hammingFlip_differenceSet {dimension : ℕ}
    (u v : HammingWord dimension) :
    hammingFlip u (hammingDifferenceSet u v) = v := by
  classical
  funext coordinate
  cases hu : u coordinate <;> cases hv : v coordinate <;>
    simp [hammingFlip, hammingDifferenceSet, hu, hv]

noncomputable def hammingBall (dimension radius : ℕ)
    (u : HammingWord dimension) : Finset (HammingWord dimension) := by
  classical
  exact Finset.univ.filter (fun v => hammingDist u v ≤ radius)

noncomputable def boundedDifferenceSets (dimension radius : ℕ) :
    Finset (Finset (Fin dimension)) := by
  classical
  exact ((Finset.univ : Finset (Fin dimension)).powerset).filter
    (fun coordinates => coordinates.card ≤ radius)

noncomputable def hammingBallEquiv (dimension radius : ℕ)
    (u : HammingWord dimension) :
    ↥(hammingBall dimension radius u) ≃
      ↥(boundedDifferenceSets dimension radius) := by
  classical
  refine
    { toFun := fun v => ⟨hammingDifferenceSet u v.val, ?_⟩
      invFun := fun coordinates =>
        ⟨hammingFlip u coordinates.val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hball : hammingDist u v.val ≤ radius := by
      have hmembership : v.val ∈
          (Finset.univ.filter
            (fun w : HammingWord dimension => hammingDist u w ≤ radius)) := by
        simpa only [hammingBall] using v.property
      exact (Finset.mem_filter.mp hmembership).2
    simp only [boundedDifferenceSets, Finset.mem_filter,
      Finset.mem_powerset]
    refine ⟨Finset.subset_univ _, ?_⟩
    simpa [hammingDist, hammingDifferenceSet] using hball
  · have hcoordinates : coordinates.val.card ≤ radius := by
      have hmembership : coordinates.val ∈
          (((Finset.univ : Finset (Fin dimension)).powerset).filter
            (fun S => S.card ≤ radius)) := by
        simpa only [boundedDifferenceSets] using coordinates.property
      exact (Finset.mem_filter.mp hmembership).2
    simp only [hammingBall, Finset.mem_filter, Finset.mem_univ, true_and]
    change (hammingDifferenceSet u
      (hammingFlip u coordinates.val)).card ≤ radius
    simpa [hammingDifferenceSet_flip] using hcoordinates
  · intro v
    apply Subtype.ext
    exact hammingFlip_differenceSet u v.val
  · intro coordinates
    apply Subtype.ext
    exact hammingDifferenceSet_flip u coordinates.val

def hammingHost (dimension radius : ℕ) :
    SimpleGraph (Bool × HammingWord dimension) :=
  SimpleGraph.fromRel
    (fun x y => x.1 ≠ y.1 ∧ hammingDist x.2 y.2 ≤ radius)

noncomputable def hammingExpectedRetainedEdgeCount
    (dimension radius : ℕ) : ℝ :=
  ∑ left : HammingWord dimension,
    ∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then
        (hammingRetentionMeasure dimension).real
          {retained : Set (Bool × HammingWord dimension) |
            (false, left) ∈ retained ∧ (true, right) ∈ retained}
      else 0

noncomputable def hammingExpectedRetainedEdgeSquare
    (dimension radius : ℕ) : ℝ :=
  ∑ firstLeft : HammingWord dimension,
    ∑ firstRight : HammingWord dimension,
      ∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            (hammingRetentionMeasure dimension).real
              {retained : Set (Bool × HammingWord dimension) |
                (false, firstLeft) ∈ retained ∧
                (true, firstRight) ∈ retained ∧
                (false, secondLeft) ∈ retained ∧
                (true, secondRight) ∈ retained}
          else 0

noncomputable def retainedHammingWordEdges
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    Finset (HammingWord dimension × HammingWord dimension) := by
  classical
  exact Finset.univ.filter (fun edge =>
    hammingDist edge.1 edge.2 ≤ radius ∧
      (false, edge.1) ∈ retained ∧ (true, edge.2) ∈ retained)

noncomputable def hammingRetainedEdgeCount
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : ℝ := by
  classical
  exact
    ∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then 1 else 0

def retainedHammingHost (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : SimpleGraph retained :=
  (hammingHost dimension radius).induce retained

noncomputable def pairGraphCopyParentWords
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    Fin (Fintype.card (PairLayer baseSize layer.val)) →
      HammingWord dimension :=
  fun parent =>
    (copy
      (pairLayerEmbedding baseSize depth layer.val (by omega)
        ((pairLayerFinEquiv baseSize layer.val).symm parent))).val.2

noncomputable def pairGraphCopyChildWords
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1 →
      HammingWord dimension :=
  fun pair =>
    (copy
      (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((pairLayerPairEquiv baseSize layer.val) pair))).val.2

noncomputable def pairGraphCopyChildSide
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1) : Bool :=
  (copy
    (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
      ((pairLayerPairEquiv baseSize layer.val) reference))).val.1

noncomputable def pairGraphCopyLayerPotential
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin (depth + 1)) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      (((booleanWordOnes
        (fun vertex : PairLayer baseSize layer.val =>
          (copy
            (pairLayerEmbedding baseSize depth layer.val layer.isLt
              vertex)).val.2 coordinate)).card : ℝ) /
        (Fintype.card (PairLayer baseSize layer.val) : ℝ))) /
    (dimension : ℝ)

noncomputable def manuscriptHammingRadius (dimension : ℕ) : ℕ :=
  ⌊tau * (dimension : ℝ)⌋₊

noncomputable def sampledHammingEdgeEntropyRate : ℝ :=
  (1 - 2 * midpointBeta) * Real.log 2 + Real.binEntropy tau

noncomputable def manuscriptSamplingFailureBound
    (depth dimension : ℕ) : ℝ :=
  (((2 * depth : ℕ) : ℝ)) *
      Real.exp (-(dimension : ℝ) * Real.log 2) +
    4 / hammingExpectedRetainedVertexCount dimension +
    (4 / hammingExpectedRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) +
      8 / (hammingRetentionProbability dimension *
        ((2 ^ dimension : ℕ) : ℝ)))

noncomputable def manuscriptSamplingFailureEvent
    {depth : ℕ}
    (layerSizes : Fin depth → ℕ)
    (dimension : ℕ) : Set (Set (Bool × HammingWord dimension)) :=
  (badPairLayersRetentionEvent layerSizes dimension ∪
    {retained : Set (Bool × HammingWord dimension) |
      3 * hammingRetentionProbability dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        hammingRetainedVertexCount dimension retained}) ∪
    {retained : Set (Bool × HammingWord dimension) |
      hammingRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) retained <
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) / 2}

noncomputable def manuscriptVertexCount (dimension : ℕ) : ℕ :=
  ⌈3 * hammingRetentionProbability dimension *
    ((2 ^ dimension : ℕ) : ℝ)⌉₊

noncomputable def manuscriptExtremalPower : ℝ :=
  (3 : ℝ) / 2 + exponentGain

noncomputable def manuscriptEntropyGap : ℝ :=
  certifiedWindowWidth * Real.log 2 / 16

end

end Erdos146


