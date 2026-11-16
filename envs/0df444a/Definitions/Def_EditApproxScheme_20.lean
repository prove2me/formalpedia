-- Prove2me | Definitions.Def_EditApproxScheme_20
-- name    : EditApproxScheme_20
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-15T17:07:32.843224+00:00
-- url     : https://prove2.me/theorems/f1660b24-9062-49d6-a36e-7f0c051e5eab
-- title:
--   Edit-distance approximation scheme, part 20 of 20: top-level storage footprints
-- statement:
--   This is **part 20 of 20** of the definitions of a uniform almost-linear approximation scheme for edit distance, which the main statement `OAI.EditApproximation.almostLinearEditDistanceRawBandV3` is about. This part contains the top-level storage footprints: local programs, random-data requests, family refinement and active footprints, charged family tables, memo contents, temporary cells, accepted space terms, and the total space footprint `integerBinarySpaceFootprintRawBand`.
--
--   Each part imports the previous one, so importing part 20 brings all definitions into scope.
--
--   The definitions as a whole specify the following.
--
--   This block specifies an edit-distance algorithm together with its random-output distribution and explicit work and storage accounting. An edit script is a sequence of single-symbol insertions, deletions, and, when enabled, substitutions; edit(x,y) is the least script length with substitutions enabled. Its arithmetic layer represents natural numbers by least-significant-bit-first Boolean lists, integers by sign and magnitude, and unreduced rationals by signed binary numerators and positive binary denominators. Addition, subtraction, comparison, multiplication, division, rounding, powers, rational arithmetic, list processing, and denominator management return values with operation counts and have corresponding allocation functions. Integer symbols are encoded injectively as 2z for z≥0 and 2|z|−1 for z<0; binary trees recording symbol occurrences and position counts support substring membership queries. A target state is an interval [lo,hi) with 0≤lo≤hi≤|y|, whose distance from another state is the sum of the absolute endpoint differences. Source intervals split into M children at lo+⌊i(hi−lo)/M⌋, forming a tree of depth ⌈log_M(max(1,|x|))⌉; dyadic scales, endpoint grids, nearby cells, and rounded intervals give finite lists of candidate alignments. An action selects a center interval and one target interval per child; its score is the sum of child values, endpoint-connection costs, and a slope times the query-to-center distance. Bellman updates take the minimum of these scores and a fallback. Initial tables take minima of cones whose center value is max(⌈U/a⌉, absolute source–target length imbalance); warmup evaluates wide candidate lists, and refinement combines their previous values with sampled group actions and online actions. If c is the resulting cone value and o an available online minimum, the refinement is min(c,max(c/(1+δ),o)), or c when no online action exists. Bands retain contiguous child alignments near their expected positions whose cut shifts follow a prescribed affine relation to prefix costs. Their dyadic child envelopes dominate both b/M and initial child values; retained bands additionally satisfy total envelope ≤64Fb, admissibility after rounding, and child length imbalance at most twice its envelope. For each envelope scale h, group sampling uses k=min(M,⌈QMh/b⌉) child labels, evaluating the full sum when k=M and otherwise multiplying the sampled sum by M/k; the member with smallest estimated connection-plus-child cost is selected. Online actions use normalized envelope-weighted action vectors, accumulated gains and decrements, and a finite optimizer with step size 2/(j+2). Its smoothed logarithmic gradient uses the rational partial sum 2∑_{k<K}((r−1)/(r+1))^{2k+1}/(2k+1), smoothing G⁻⁵⁰, G⁶⁰ terms, and up to G⁸⁰ optimizer iterations; iteration j is sampled with weight j+1. Coarse seeds instead use padded B-ary source trees, dyadic shift bounds, mismatch costs, and twice the change in shift as transition cost. Random thresholds prune subtrees whose lengths fit their allowances and threshold the remaining child contributions; candidates have value 2(estimate+k), are minimized over dyadic k, rounded upward, and capped at N, with separate equality and large target-length branches. Successive seed passes use capped upper medians of scaled previous-copy outputs. Parameters depend explicitly on the external natural number N: h=⌈log₂⌈log₂(N+2)⌉⌉, H=2^h, f=⌈log₂(max(1,h))⌉, ℓ=2^f, p=⌊√⌊√⌊log₂ℓ⌋⌋⌋, B=H^p, M=2^⌊h/20⌋, P=H^{p+20}, T=2^⌊(3h+3)/4⌋, and S=⌊H/ℓ²⌋. Coarse thresholds use Q₀=H⁴ and allowance contraction 1/(64H). The initial factor is H^{p+4}; seed pass j has exponent (p+4)h−j(f−2), with natural subtraction, and the pass count is the natural ceiling quotient ((p+4)h−f)/(f−2). Refinement uses F=ℓ, slopes 32ℓ and 128ℓ, δ=ℓ⁻¹⁰, κ=τ=ℓ⁻⁴, θ=ℓ⁻⁴⁰, γ=ℓ⁻²⁰, η=ℓ⁵, group parameter Q=ℓ⁸⁰, and H² copies and random-source time slots. Finite query programs gather current, earlier, and shared child inputs and random draws; table requests record pass, copy, tree node, iteration, and interval. Decreasing request ranks make recursive evaluation terminate, and binary memoization stores completed rational answers while tracking fresh keys, requests, dictionary visits, and local work. Coarse draws and accepted finite-range draws have product-uniform laws; rejection sampling for a range of size r uses ⌈log₂r⌉ bits per attempt and a geometric failure count with success probability r/2^{⌈log₂r⌉}. The randomized branch is selected only when ε's numerator and denominator each occupy at most H bits, ℓ≥2^1000, ℓε≥10, and the bit length of the triangular mass of (H+M(40P+2)²+2)^80 is at most H. Otherwise the law is concentrated on a deterministic suffix dynamic program: matching one source symbol to an empty target piece costs 1, and to a nonempty piece costs its length minus its membership indicator, with minimization over successive target splits. The randomized answer is zero for equal inputs and otherwise the natural floor of the final root value capped at N. Work functions charge preprocessing, parameter construction, coarse computations and sampling, rejection bits, addressing, memo operations, local kernels, and output conversion. Storage functions sum stored inputs and occurrence indexes, rational memo contents, recursively accumulated temporary allocation, coarse arrays and scratch data, control data, and output space, with a separate dynamic-program allocation for fallback. These definitions impose no relationship between N and the input lengths and do not themselves assert an approximation ratio or asymptotic resource bound.
--
--   **Formalization Note** These 20 parts replace the single 1.4 MB block `Def_EditApproximation`, which was too large for the platform to import. In the source, the supporting lemmas were pasted as local `have` proofs inside the definition bodies: 948 copies of 145 lemmas. Each lemma is now proved once as a top-level theorem and cited by name; one lemma that nothing used was dropped. The file was then split into sequential parts by deleting declarations. All 1,403 declarations from the source keep exactly the same elaborated types.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/EditApproximation.lean#L11781-L12145 (line numbers refer to the lemma-lifted file, 12,145 lines)

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/EditApproximation.lean
-- Part 20 of 20 of the edit-distance approximation definitions: embedded proof lemmas lifted
-- to top-level theorems (OAI.EditApproximation.Lemmas.*), then split by skeleton subtraction.

import Definitions.Def_EditApproxScheme_19

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

attribute [local instance] queryArityNeZero queryRoundsNeZero

def queryLocalProgramFootprintRawBand
    {ι : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M : ℕ}
    [NeZero M]
    (parent : OAI.EditApproximation.TargetInterval source.length)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction)
    (t : ℕ)
    (readParent : OAI.EditApproximation.TargetInterval target.length →
  OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (readMass readInitial : Fin M × OAI.EditApproximation.TargetInterval target.length →
  OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (readGroup : OAI.EditApproximation.GroupScalarKey M F Q → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (readInteger : ℕ × OAI.EditApproximation.TargetInterval target.length →
  ℕ → OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval target.length)
    (readEarlier : Fin M × ℕ × OAI.EditApproximation.TargetInterval target.length →
  OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (readCurrent : Fin M × OAI.EditApproximation.TargetInterval target.length →
  OAI.EditApproximation.BitQuery ι OAI.EditApproximation.BinaryFraction)
    (hp : (key : OAI.EditApproximation.TargetInterval target.length) → (readParent key).Footprint)
    (hm : (key : Fin M × OAI.EditApproximation.TargetInterval target.length) → (readMass key).Footprint)
    (hi : (key : Fin M × OAI.EditApproximation.TargetInterval target.length) → (readInitial key).Footprint)
    (hg : (key : OAI.EditApproximation.GroupScalarKey M F Q) → (readGroup key).Footprint)
    (hz : (key : ℕ × OAI.EditApproximation.TargetInterval target.length) → (range : ℕ) → (readInteger key range).Footprint)
    (he : (key : Fin M × ℕ × OAI.EditApproximation.TargetInterval target.length) → (readEarlier key).Footprint)
    (hr : (key : Fin M × OAI.EditApproximation.TargetInterval target.length) → (readCurrent key).Footprint) : (OAI.EditApproximation.queryLocalProgramRawBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
    readParent readMass readInitial readGroup readInteger q readEarlier readCurrent).Footprint :=
OAI.EditApproximation.queryInitialGatherFootprint N P F exponent hP a q readParent hp
  (fun (keys : List (OAI.EditApproximation.TargetInterval target.length))
      (words : List OAI.EditApproximation.BinaryFraction) =>
    OAI.EditApproximation.queryLocalBandRawBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
      (OAI.EditApproximation.BinaryFraction.queryParentReadWithWork keys words) readMass readInitial readGroup
      readInteger q readEarlier readCurrent)
  fun (keys : List (OAI.EditApproximation.TargetInterval target.length))
    (words : List OAI.EditApproximation.BinaryFraction) =>
  OAI.EditApproximation.queryLocalBandFootprintRawBand source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa
    delta t (OAI.EditApproximation.BinaryFraction.queryParentReadWithWork keys words)
    (OAI.EditApproximation.BinaryFraction.queryParentReadAllocation keys words) readMass readInitial readGroup
    readInteger q readEarlier readCurrent hm hi hg hz he hr

def queryPhysicalRandomDataRequestFootprintRawBand
    {σ : Type u_1}
    {α : Type u_2}
    (source target : List α)
    {M J : ℕ}
    [NeZero M]
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction)
    (copies pass copy T S t : ℕ)
    (ht : 0 < t)
    (node : OAI.EditApproximation.PhysicalNode M J)
    (hbelow : ↑node.fst < J)
    (readGroup : OAI.EditApproximation.GroupScalarKey M F Q → OAI.EditApproximation.BitQuery σ OAI.EditApproximation.BinaryFraction)
    (readInteger : ℕ × OAI.EditApproximation.TargetInterval target.length →
  ℕ → OAI.EditApproximation.BitQuery σ OAI.EditApproximation.BinaryFraction)
    (q : OAI.EditApproximation.TargetInterval target.length)
    (hg : (key : OAI.EditApproximation.GroupScalarKey M F Q) → (readGroup key).Footprint)
    (hz : (key : ℕ × OAI.EditApproximation.TargetInterval target.length) → (range : ℕ) → (readInteger key range).Footprint) : (OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand source target N P F exponent H Q eM eF hP hM hF tau a eta kappa
    delta copies pass copy T S t ht node hbelow readGroup readInteger q).Footprint := by
  unfold OAI.EditApproximation.queryPhysicalRandomDataRequestRawBand
  apply OAI.EditApproximation.queryLocalProgramFootprintRawBand
  · intro r
    exact (OAI.EditApproximation.queryPhysicalTableReadFootprint copies T S _ _).mapKeysWithWork _ (fun _ => 1)
  · intro input
    apply OAI.EditApproximation.BitQuery.Footprint.mapKeysWithWork _ (fun _ => 1)
    apply OAI.EditApproximation.queryMeanReadFootprint
    intro j
    exact OAI.EditApproximation.queryPhysicalTableReadFootprint copies T S _ _
  · intro input
    exact (OAI.EditApproximation.queryPhysicalTableReadFootprint copies T S _ _).mapKeysWithWork _ (fun _ => 1)
  · intro key
    exact (hg key).mapKeysWithWork _ (fun _ => 1)
  · intro key range
    exact (hz key range).mapKeysWithWork _ (fun _ => 1)
  · intro input
    exact (OAI.EditApproximation.queryPhysicalEarlierReadFootprint copies pass copy T S t node hbelow q input).mapKeysWithWork _
      (fun _ => 1)
  · intro input
    exact (OAI.EditApproximation.queryPhysicalTableReadFootprint copies T S _ _).mapKeysWithWork _ (fun _ => 1)

def queryFamilyRefinementFootprintRawBand
    {α : Type u_1}
    {M J R : ℕ}
    [NeZero M]
    (source target : List α)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction)
    (passes copies pass copy T S t : ℕ)
    (ht : 0 < t)
    (node : OAI.EditApproximation.PhysicalNode M J)
    (hbelow : ↑node.fst < J)
    (time : Fin R)
    (q : OAI.EditApproximation.TargetInterval target.length) : (OAI.EditApproximation.queryFamilyRefinementRawBand source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
    passes copies pass copy T S t ht node hbelow time q).Footprint :=
OAI.EditApproximation.queryPhysicalRandomDataRequestFootprintRawBand source target N P F exponent H Q eM eF hP hM hF tau a eta
  kappa delta copies pass copy T S t ht node hbelow
  (OAI.EditApproximation.queryFamilyGroupRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time)
  (OAI.EditApproximation.queryFamilyOnlineRead target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩ time) q
  (OAI.EditApproximation.queryFamilyGroupReadFootprint target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩
    time)
  (OAI.EditApproximation.queryFamilyOnlineReadFootprint target N P F exponent H Q passes copies pass copy ⟨node, hbelow⟩
    time)

def queryFamilyActiveFootprintRawBand
    {α : Type u_1}
    {M J R : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List α)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction)
    (T S passes copies : ℕ)
    (request : OAI.EditApproximation.PhysicalTableRequest M J target.length)
    (hindex : T < request.index)
    (hbelow : ↑request.node.fst < J) : (OAI.EditApproximation.queryFamilyActiveRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta T S
    passes copies request hindex hbelow).Footprint := by
  exact
    (OAI.EditApproximation.queryFamilyRefinementFootprintRawBand source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta
      passes copies request.pass request.copy T S (request.index - T) (Nat.sub_pos_of_lt hindex)
      request.node hbelow (Fin.ofNat R (request.index - T - 1)) request.state).mapKeysWithWork _ (fun _ => 1)

def queryFamilyBoundedActiveFootprintRawBand
    {α : Type u_1}
    {M J R : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List α)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (tau a eta kappa delta : OAI.EditApproximation.BinaryFraction)
    (T S passes copies : ℕ)
    (parent : { r : OAI.EditApproximation.PhysicalTableRequest M J target.length //
  OAI.EditApproximation.PhysicalTableRequest.Bounded (passes + 1) copies T S r })
    (hindex : T < parent.val.index)
    (hbelow : ↑parent.val.node.fst < J) : (OAI.EditApproximation.queryFamilyBoundedActiveRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF tau a eta kappa delta T
    S passes copies parent hindex hbelow).Footprint :=
  OAI.EditApproximation.queryRestrictPhysicalBodyFootprint (passes + 1) copies T S parent _
    (OAI.EditApproximation.queryFamilyActiveFootprintRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta T S passes copies parent.val hindex hbelow)

def queryChargedFamilyTableFootprintRawBand
    {M J R passes copies T S : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List ℕ)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (A a : ℕ → OAI.EditApproximation.BinaryFraction)
    (tau eta kappa delta : OAI.EditApproximation.BinaryFraction)
    (multiplier : ℕ → ℕ)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts)
    (symbolBits positionBits : ℕ)
    (parent : { r : OAI.EditApproximation.PhysicalTableRequest M J target.length //
  OAI.EditApproximation.PhysicalTableRequest.Bounded (passes + 1) copies T S r }) : (OAI.EditApproximation.queryChargedFamilyTableRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa delta
    multiplier occurrence symbolBits positionBits parent).Footprint := by
  have hinit := OAI.EditApproximation.queryPhysicalInitialFootprint source target N P F (A parent.val.pass) (a parent.val.pass)
    multiplier parent occurrence symbolBits positionBits parent.val.state
  unfold OAI.EditApproximation.queryChargedFamilyTableRawBand
  refine OAI.EditApproximation.BitQuery.Footprint.chargeOf (OAI.EditApproximation.naturalWordLEAllocation parent.val.index.bits T.bits) ?_
  split
  · exact (OAI.EditApproximation.queryChargedWarmupFootprint source target N P F (A parent.val.pass) (a parent.val.pass)
      multiplier parent occurrence symbolBits positionBits).mapKeysWithWork _ (fun _ => 1)
  · refine OAI.EditApproximation.BitQuery.Footprint.chargeOf (parent.val.node.1.val.bits.length + J.bits.length) ?_
    split
    · let interval := OAI.EditApproximation.physicalSourceInterval source.length parent.val.node
      refine OAI.EditApproximation.BitQuery.Footprint.chargeOf (OAI.EditApproximation.saturatingSubtractAllocation interval.hi interval.lo +
        OAI.EditApproximation.naturalWordLEAllocation (OAI.EditApproximation.saturatingSubtractWithWork interval.hi interval.lo).1 [true]) ?_
      split
      · exact hinit.mapKeysWithWork _ (fun _ => 1)
      · exact (OAI.EditApproximation.queryFamilyBoundedActiveFootprintRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF
          tau (a parent.val.pass) eta kappa delta T S passes copies parent _ _).mapKeysWithWork _
          (fun _ => 1)
    · exact hinit.mapKeysWithWork _ (fun _ => 1)

def queryChargedFamilyGlobalFootprintRawBand
    {M J R passes copies T S : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List ℕ)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (A a : ℕ → OAI.EditApproximation.BinaryFraction)
    (tau eta kappa delta : OAI.EditApproximation.BinaryFraction)
    (multiplier : ℕ → ℕ)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts)
    (symbolBits positionBits : ℕ)
    (coarse : OAI.EditApproximation.PhysicalEntry M J target.length → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : OAI.EditApproximation.PhysicalEntry M J target.length → ℕ)
    (request : OAI.EditApproximation.ChargedPhysicalRequest M J target.length (passes + 1) copies T S) : (OAI.EditApproximation.queryChargedFamilyGlobalRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa delta
    multiplier occurrence symbolBits positionBits coarse request).Footprint := by
  cases request with
  | inl entry => exact OAI.EditApproximation.BitQuery.Footprint.compute (coarse entry) (allocation entry)
  | inr parent =>
    exact OAI.EditApproximation.queryChargedFamilyTableFootprintRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits parent

def queryFamilyMemoRawFootprintRawBand
    {M J R passes copies T S : ℕ}
    [NeZero M]
    [NeZero R]
    (source target : List ℕ)
    (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P)
    (hM : M = 2 ^ eM)
    (hF : F = 2 ^ eF)
    (A a : ℕ → OAI.EditApproximation.BinaryFraction)
    (tau eta kappa delta : OAI.EditApproximation.BinaryFraction)
    (multiplier : ℕ → ℕ)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts)
    (symbolBits positionBits : ℕ)
    (coarse : OAI.EditApproximation.PhysicalEntry M J target.length → OAI.EditApproximation.BinaryFraction × ℕ)
    (allocation : OAI.EditApproximation.PhysicalEntry M J target.length → ℕ)
    (draw : OAI.EditApproximation.PhysicalFamilyScalarDraw (M := M) (J := J) (R := R) target N P F exponent H Q passes copies)
    (key : OAI.EditApproximation.QueryFamilyMemoKey (M := M) (J := J) (R := R) (passes := passes) (copies := copies) (T := T) (S := S) target N P F exponent H Q) : (OAI.EditApproximation.queryFamilyMemoRawRawBand (R := R) source target N P F exponent H Q eM eF hP hM hF A a tau eta kappa delta
    multiplier occurrence symbolBits positionBits coarse draw key).Footprint := by
  cases key with
  | inl scalar =>
    exact OAI.EditApproximation.BitQuery.Footprint.computeOf (OAI.EditApproximation.queryFamilySourceWordWithWork target N P F exponent H Q draw scalar)
      (Nat.size (draw scalar).val + 2)
  | inr request =>
    exact (OAI.EditApproximation.queryChargedFamilyGlobalFootprintRawBand source target N P F exponent H Q eM eF hP hM hF
      A a tau eta kappa delta multiplier occurrence symbolBits positionBits coarse allocation request).mapKeysWithWork
        _ (fun _ => 1)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

attribute [local instance] queryArityNeZero queryRoundsNeZero

open MeasureTheory ProbabilityTheory

def computedQueryMemoRawFootprintRawBand
    (source target : List ℕ)
    (N : ℕ)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts)
    (symbolBits positionBits : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N)
    (key : OAI.EditApproximation.ComputedFamilyMemoKey source target N) : (OAI.EditApproximation.computedQueryMemoRawRawBand source target N occurrence symbolBits positionBits input key).Footprint := by
  exact
    OAI.EditApproximation.queryFamilyMemoRawFootprintRawBand source target N (OAI.EditApproximation.integerParameters N).P (OAI.EditApproximation.inputSmallLog N)
      (40 * OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80)
      (OAI.EditApproximation.heightExponent N / 20) (OAI.EditApproximation.smallLogExponent N) (OAI.EditApproximation.Lemmas.computedParameterP_pos N) rfl rfl
      (fun pass => (OAI.EditApproximation.scheduledSeedWordWithWork N pass).1)
      (fun pass => (OAI.EditApproximation.computedQueryParameters N pass).factor)
      (OAI.EditApproximation.computedQueryParameters N 0).tau (OAI.EditApproximation.computedQueryParameters N 0).eta
      (OAI.EditApproximation.computedQueryParameters N 0).kappa (OAI.EditApproximation.computedQueryParameters N 0).delta
      (OAI.EditApproximation.scheduledSeedMultiplier N) occurrence symbolBits positionBits
      (fun entry => (OAI.EditApproximation.BinaryFraction.nat (OAI.EditApproximation.clampedSeedNat input.1 entry), 0))
      (fun _ => 0) input.2 key

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open BitQuery

attribute [local instance] queryArityNeZero queryRoundsNeZero

def computedQueryMemoFootprintRawBand
    (source target : List ℕ)
    (N : ℕ)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts)
    (symbolBits positionBits : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N)
    (key : OAI.EditApproximation.ComputedFamilyMemoKey source target N) : (OAI.EditApproximation.computedQueryMemoNormalizedRawBand source target N occurrence symbolBits positionBits input
    key).Footprint := by
  exact
    (OAI.EditApproximation.computedQueryMemoRawFootprintRawBand source target N occurrence symbolBits positionBits input
          key).normalize
      (OAI.EditApproximation.computedQueryBase N) (OAI.EditApproximation.Lemmas.computedQueryBase_pos N)
      (OAI.EditApproximation.queryFamilyMemoRemaining target N (OAI.EditApproximation.integerParameters N).P
        (OAI.EditApproximation.inputSmallLog N) (40 * OAI.EditApproximation.smallLogExponent N)
        (OAI.EditApproximation.inputHeight N) (OAI.EditApproximation.inputSmallLog N ^ 80) key)

end OAI.EditApproximation

end

section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace OAI.EditApproximation

open Filter MeasureTheory

attribute [local instance] queryRoundsNeZero

def computedQueryTemporaryCellsFootprintRawBand (source target : List ℕ) (N : ℕ)
    (occurrence : OAI.EditApproximation.BinaryMemo OAI.EditApproximation.PositionCounts) (symbolBits positionBits : ℕ)
    (input : OAI.EditApproximation.ComputedFamilyInput source target N) : ℕ :=
  OAI.EditApproximation.BitQuery.Footprint.rankedBitMemoCells (OAI.EditApproximation.SourceRanked.rank OAI.EditApproximation.ChargedPhysicalRequest.rank)
    (OAI.EditApproximation.computedQueryMemoNormalizedRawBand source target N occurrence symbolBits positionBits input)
    (OAI.EditApproximation.computedQueryMemoFootprintRawBand source target N occurrence symbolBits positionBits input)
    (16384 * OAI.EditApproximation.inputHeight N + 5) (OAI.EditApproximation.computedFamilyMemoCode source target N (OAI.EditApproximation.inputHeight N ^ 2))
    (fun key => (OAI.EditApproximation.computedFamilyMemoCodeWithWork source target N (OAI.EditApproximation.inputHeight N ^ 2) key).2)
    (.inr (OAI.EditApproximation.localFinalRootRequest target N (OAI.EditApproximation.integerParameters N).T (OAI.EditApproximation.integerParameters N).S
      (OAI.EditApproximation.inputHeight N) (Nat.two_pow_pos _) (OAI.EditApproximation.finalTargetState target.length))) .empty

noncomputable def integerAcceptedSpaceTermsFootprintRawBand (source target : List ℤ) (N : ℕ)
    (epsilon : OAI.EditApproximation.BinaryFraction)
    (input : OAI.EditApproximation.ComputedFamilyInput (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) N) : List ℕ :=
  let x := source.map OAI.EditApproximation.integerSymbolCode
  let y := target.map OAI.EditApproximation.integerSymbolCode
  [8 * OAI.EditApproximation.integerPreevaluationWork source target N epsilon,
   2 * OAI.EditApproximation.integerStoredDataSpace source target,
   OAI.EditApproximation.computedQuerySetupAllocation N,
   (OAI.EditApproximation.computedQueryMemoResultRawBand x y N (OAI.EditApproximation.integerOccurrenceIndex source target)
     (OAI.EditApproximation.integerInputSymbolBits source target) (OAI.EditApproximation.integerInputPositionBits target) input).memory.fractionStorage,
   OAI.EditApproximation.computedQueryTemporaryCellsFootprintRawBand x y N (OAI.EditApproximation.integerOccurrenceIndex source target)
     (OAI.EditApproximation.integerInputSymbolBits source target) (OAI.EditApproximation.integerInputPositionBits target) input,
   OAI.EditApproximation.computedFamilyCoarseCopyStorage x y N input,
   OAI.EditApproximation.computedFamilyCoarseArrayCapacity x y N input,
   OAI.EditApproximation.computedFamilyCoarseScratchCapacity x y N input,
   OAI.EditApproximation.computedFamilyCoarseControlCapacity x y N input,
   4 * (OAI.EditApproximation.inputHeight N + (OAI.EditApproximation.integerParameters N).B + 4),
   OAI.EditApproximation.integerFinalAllocationRawBand source target N input,
   8 * (N + 1)]

noncomputable def integerBinarySpaceFootprintRawBand (source target : List ℤ) (N : ℕ) (epsilon : OAI.EditApproximation.BinaryFraction)
    (outcome : OAI.EditApproximation.ComputedFullOutcome (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) N) : ℕ :=
  if OAI.EditApproximation.physicalLargeInput N epsilon then
    match outcome with
    | .inl _ => 8 * OAI.EditApproximation.integerPreevaluationWork source target N epsilon +
        2 * OAI.EditApproximation.integerStoredDataSpace source target +
        OAI.EditApproximation.suffixDPAllocation (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) + 8 * (N + 1)
    | .inr execution => (OAI.EditApproximation.integerAcceptedSpaceTermsFootprintRawBand source target N epsilon
        (OAI.EditApproximation.computedExecutionAccepted _ _ N execution)).sum
  else 8 * OAI.EditApproximation.integerPreevaluationWork source target N epsilon +
    2 * OAI.EditApproximation.integerStoredDataSpace source target +
    OAI.EditApproximation.suffixDPAllocation (source.map OAI.EditApproximation.integerSymbolCode) (target.map OAI.EditApproximation.integerSymbolCode) + 8 * (N + 1)

end OAI.EditApproximation

end


