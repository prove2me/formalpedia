-- Prove2me | Definitions.Def_OAIQ075A003
-- name    : OAIQ075A003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T07:53:34.493099+00:00
-- url     : https://prove2.me/theorems/f301b62b-8335-4a51-8862-4b1d68bb713b
-- title:
--   Definitions bundle OAIQ075A003 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 57 declarations of OpenAI's Lean: 18 definitions, 2 inductive types or structures, 5 instances and 32 theorems. The definitions and types are `OAI.Generator.Tracial.AlgebraProjection`, `OAI.Generator.Tracial.CornerPartition`, `OAI.Generator.Tracial.CornerPartition.blockIndices`, `OAI.Generator.Tracial.CornerPartition.joint`, `OAI.Generator.Tracial.CornerPartition.jointPiece`, `OAI.Generator.Tracial.CornerPartition.ofFamily`, `OAI.Generator.Tracial.CornerPartition.pinch`, `OAI.Generator.Tracial.CornerPartition.refineBlocks`, `OAI.Generator.Tracial.DyadicIndex`, `OAI.Generator.Tracial.PartialIsometry`, `OAI.Generator.Tracial.PartialIsometry.Extends`, `OAI.Generator.Tracial.PartialIsometry.zero`, `OAI.Generator.Tracial.coordinateInclusion`, `OAI.Generator.Tracial.cornerSpectralShift`, `OAI.Generator.Tracial.identityProjection`, `OAI.Generator.Tracial.kernelProjection`, `OAI.Generator.Tracial.rangeProjection`, `OAI.Generator.WOTClosed`, `OAI.HochschildFinitePhase.phase`, `OAI.HochschildPatching.wordCoeff`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_FinitePhases`, `BoundedHochschild_MixedWords`, `FactorGeneration_Bicommutant`, `FactorGeneration_OperatorLimits`, `FactorGeneration_PartialIsometries`, `FactorGeneration_Pinching`, `FactorGeneration_ProjectionLimits`, `FactorGeneration_SpectralApproximation`, `FactorGeneration_SpectralPinching`, `FactorGeneration_Supports`, `FactorGeneration_Target`, `FactorGeneration_TraceTopology`, `FactorGeneration_TracialInclusion`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A007`, `OAIQ075A008`, `OAIQ075A009`, `OAIQ075A010`, `OAIQ075A011` and `OAIQ075A012`; the statements `OAI_KadisonSimilarity_TracialCornerGeometry_exists_orthogonal_unitaries_of_normal_matrix_tower` and `OAI_KadisonSimilarity_TracialCornerGeometry_rightSupportInput_of_normal_range`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ075_KS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Subtype.starOrderedRing`: the order a closed ⋆-subalgebra of a C⋆-algebra inherits
(Kadison similarity, oaiq-075). -/
theorem _root_.Subtype.starOrderedRing {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (S : StarSubalgebra ℂ A) [hS : IsClosed (S : Set A)] :
    StarOrderedRing S := by
  refine StarOrderedRing.of_nonneg_iff' (fun {a b} h c => ?_) (fun {s} => ?_)
  · show ((c : A) + (a : A)) ≤ (c : A) + (b : A)
    exact add_le_add le_rfl (show (a : A) ≤ (b : A) from h)
  · constructor
    · intro hs
      have hs' : (0 : A) ≤ (s : A) := hs
      have hmem : CFC.sqrt (s : A) ∈ S := by
        rw [CFC.sqrt_eq_real_sqrt _ hs']
        exact cfcₙ_mem (𝕜 := ℝ) (𝕜' := ℂ) (s := S) _ s.property
      refine ⟨⟨CFC.sqrt (s : A), hmem⟩, Subtype.ext ?_⟩
      show (s : A) = star (CFC.sqrt (s : A)) * CFC.sqrt (s : A)
      rw [CFC.sqrt_nonneg _ |>.isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self _ hs']
    · rintro ⟨t, rfl⟩
      show (0 : A) ≤ star (t : A) * (t : A)
      exact star_mul_self_nonneg _

/-- A closed ⋆-subalgebra of a C⋆-algebra is star ordered (d13f23b finds this by instance search). -/
instance starSubalgebraStarOrderedRing {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)] : StarOrderedRing S :=
  Subtype.starOrderedRing S
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FinitePhases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite additive characters, phase matrices and orthogonality. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open scoped BigOperators ComplexConjugate InnerProductSpace





open scoped BigOperators ComplexConjugate InnerProductSpace
namespace HochschildFinitePhase
variable {I : Type*} [DecidableEq I]

def phase (g : I → ZMod 3) (i : I) : ℂ := ZMod.stdAddChar (g i)

end HochschildFinitePhase
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MixedWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mixed-word Taylor expansions, moment corners and patch coefficients. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildPatching
variable {M : Type*} [CStarAlgebra M]


variable {I : Type*} (F : I → M)
def wordCoeff : Option I → M | none => 1 | some i => F i
end HochschildPatching

 

 

open scoped ComplexOrder





open Filter Topology
open scoped ComplexOrder





open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Target
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Generator

/-! Weak operator generation of concrete finite diffuse factors with separable Banach preduals. -/
noncomputable section
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Weak operator closedness, not operator norm closedness. -/
def WOTClosed (S : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ S}

end

end Generator

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Bicommutant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Finite diagonal amplification and the projection onto a simultaneous
operator orbit. These are the analytic ingredients of the bicommutant theorem. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

theorem starProjection_commutes_of_invariant (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (T : H →L[ℂ] H) (hT : ∀ x ∈ K,T x ∈ K) (hstar : ∀ x ∈ K,star T x ∈ K) :
    K.starProjection*T=T*K.starProjection := by
  ext x
  apply K.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hT _ (K.starProjection_apply_mem x)
  · intro y hy
    change inner ℂ (T x-T (K.starProjection x)) y=0
    rw [← map_sub]
    rw [← ContinuousLinearMap.adjoint_inner_right]
    exact K.starProjection_inner_eq_zero x _ (hstar y hy)

end

/-! The double commutant theorem for actual unital star subalgebras of B(H).
Finite simultaneous strong approximation constructs a WOT-convergent net.
No bounded approximation or separable-predual theorem is claimed here. -/

/-! Countable algebraic generators give a separable star algebra using only
continuous addition and scalar multiplication. No multiplication continuity is
required, so the result applies to the two-norm on a tracial quotient. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_OperatorLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Operator-norm completeness of the manuscript's concrete algebra, derived
from its actual double-commutant property. No quotient completeness is assumed. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem base_norm_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  exact Set.isClosed_centralizer _

instance baseCompleteSpace (M : VonNeumannAlgebra H) : CompleteSpace M.toStarSubalgebra :=
  (base_norm_closed M).completeSpace_coe

end

/-! Bounded operator families have weak operator ultralimits. This is proved
from Banach--Alaoglu and Riesz representation, not assumed as compactness. -/
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_weak_vector_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (v : ι → H) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) :
    ∃ z : H, ‖z‖ ≤ C ∧ ∀ y : H,
      Tendsto (fun i => inner ℂ y (v i)) (ω : Filter ι) (𝓝 (inner ℂ y z)) := by
  let f : ι → WeakDual ℂ H := fun i =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (v i))
  obtain ⟨d, hd, ht⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℂ H) C).ultrafilter_le_nhds
    (ω.map f) (by
      apply le_principal_iff.mpr
      change ∀ᶠ i in (ω : Filter ι), f i ∈ _
      exact Eventually.of_forall fun i => by
        simpa [f, Metric.mem_closedBall, dist_zero_right] using hv i)
  let z := (InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual d)
  refine ⟨z, ?_, ?_⟩
  · have hd' : ‖WeakDual.toStrongDual d‖ ≤ C := by
      simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hd
    simpa only [z, LinearIsometryEquiv.norm_map] using hd'
  · intro y
    have he : Tendsto (fun i => inner ℂ (v i) y) (ω : Filter ι)
        (𝓝 (inner ℂ z y)) := by
      have h := (WeakBilin.eval_continuous _ y).continuousAt.tendsto.comp ht
      change Tendsto (fun i => inner ℂ (v i) y) (ω : Filter ι) (𝓝 (d y)) at h
      rw [show inner ℂ z y = d y from InnerProductSpace.toDual_symm_apply]
      exact h
    have hs := he.star
    change Tendsto (fun i => (starRingEnd ℂ) (inner ℂ (v i) y)) (ω : Filter ι)
      (𝓝 ((starRingEnd ℂ) (inner ℂ z y))) at hs
    simpa only [inner_conj_symm] using hs

theorem exists_weak_operator_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (a : ι → H →L[ℂ] H) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    ∃ T : H →L[ℂ] H, ‖T‖ ≤ C ∧ ∀ x y : H,
      Tendsto (fun i => inner ℂ y (a i x)) (ω : Filter ι) (𝓝 (inner ℂ y (T x))) := by
  have h (x : H) := exists_weak_vector_ultralimit ω (fun i => a i x) (C * ‖x‖)
    (fun i => (a i).le_of_opNorm_le (ha i) x)
  choose v hv ht using h
  have hadd (x z : H) : v (x+z) = v x + v z := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (x+z) y)
    simpa only [map_add, inner_add_right] using (ht x y).add (ht z y)
  have hsmul (c : ℂ) (x : H) : v (c • x) = c • v x := by
    apply ext_inner_left ℂ
    intro y
    apply tendsto_nhds_unique (ht (c • x) y)
    simpa only [map_smul, inner_smul_right] using (ht x y).const_mul c
  let T : H →L[ℂ] H := LinearMap.mkContinuous
    { toFun := v, map_add' := hadd, map_smul' := hsmul } C hv
  exact ⟨T, T.opNorm_le_bound hC hv, ht⟩

/-- The double-commutant property retains the weak limit in the actual algebra. -/
theorem weak_operator_limit_mem (M : VonNeumannAlgebra H)
    {ι : Type*} {l : Filter ι} [l.NeBot] (a : ι → M.toStarSubalgebra)
    (T : H →L[ℂ] H)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i : H →L[ℂ] H) x)) l
      (𝓝 (inner ℂ y (T x)))) : T ∈ M := by
  change T ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro S hS
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  have he (i : ι) : inner ℂ y ((a i : H →L[ℂ] H) (S x)) =
      inner ℂ (star S y) ((a i : H →L[ℂ] H) x) := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    exact congrArg (fun R : H →L[ℂ] H => inner ℂ y (R x)) (hS (a i) (a i).property)
  have hh := (ht (S x) y).congr he
  have heq := tendsto_nhds_unique hh (ht x (star S y))
  simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left, mul_apply_eq_comp] using heq.symm

/-! Operator-norm balls of an actual von Neumann algebra are compact for the
weak operator topology, using the previously constructed operator ultralimits. -/

end Tracial

/-! Operator order bounds are closed in the weak operator topology. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Operator-norm bounded trace-norm limits remain in the same ball of the algebra, without requiring a cyclic trace vector. -/

/-! The least-norm point of the actual orbit hull is represented in M and
fixed by every conjugating unitary; its trace and distance bounds are retained. -/
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem convex_minimum_unique {K : Set H} (hK : Convex ℝ K) {x y : H}
    (hx : x ∈ K) (hy : y ∈ K) (hmin : ∀ z ∈ K, ‖x‖ ≤ ‖z‖) (hnorm : ‖y‖ = ‖x‖) : x = y := by
  have hm := hmin ((1/2 : ℝ) • x + (1/2 : ℝ) • y)
    (hK hx hy (by norm_num) (by norm_num) (by norm_num))
  rw [← smul_add, norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at hm
  have hp := parallelogram_law_with_norm ℂ x y
  have htriangle := norm_add_le x y
  have he : ‖x+y‖ = 2*‖x‖ := by linarith
  rw [he, hnorm] at hp
  have hz : ‖x-y‖ ^ 2 = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_ProjectionLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Projections with their algebraic range-inclusion order. -/
def AlgebraProjection (M : VonNeumannAlgebra H) :=
  {p : M.toStarSubalgebra // IsStarProjection p}

instance algebraProjectionPartialOrder : PartialOrder (AlgebraProjection M) where
  le p q := q.val * p.val = p.val
  le_refl p := p.property.isIdempotentElem.eq
  le_trans a b c hab hbc := by
    calc c.val * a.val = c.val * (b.val * a.val) := by rw [hab]
         _ = (c.val * b.val) * a.val := (mul_assoc _ _ _).symm
         _ = a.val := by rw [hbc, hab]
  le_antisymm a b hab hba := by
    apply Subtype.ext
    have h := congrArg star hab
    simp only [star_mul, a.property.isSelfAdjoint.star_eq,
      b.property.isSelfAdjoint.star_eq] at h
    exact h.symm.trans hba

theorem projection_mul_of_le {p q : AlgebraProjection M} (h : p ≤ q) :
    p.val * q.val = p.val := by
  have he := congrArg star h
  simpa only [star_mul, p.property.isSelfAdjoint.star_eq,
    q.property.isSelfAdjoint.star_eq] using he

end

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- At depth n there are 2^n indices; a successor appends a binary branch. -/
def DyadicIndex : ℕ → Type
  | 0 => Unit
  | n+1 => DyadicIndex n × Bool

instance dyadicIndexFintype : (n : ℕ) → Fintype (DyadicIndex n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @instFintypeProd _ _ (dyadicIndexFintype n) inferInstance

instance dyadicIndexDecidableEq (n : ℕ) : DecidableEq (DyadicIndex n) := Classical.decEq _

variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q = q ∧ q*p = q)

theorem orthogonal_subprojections {p q a b : AlgebraProjection M}
    (hpq : p.val*q.val=0) (ha : a ≤ p) (hb : b ≤ q) : a.val*b.val=0 := by
  calc a.val*b.val = (a.val*p.val)*(q.val*b.val) := by rw [projection_mul_of_le ha,hb]
       _ = a.val*(p.val*q.val)*b.val := by simp only [mul_assoc]
       _ = 0 := by rw [hpq,mul_zero,zero_mul]

end

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TracialInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Generator.Tracial

/-! The restricted faithful trace and the actual P^omega -> M^omega
inclusion. All constructions are on the bounded-sequence quotient. -/
noncomputable section
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M P : VonNeumannAlgebra H}
  (hPM : P ≤ M)

def coordinateInclusion : P.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra :=
  StarSubalgebra.inclusion hPM

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_PartialIsometries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual partial isometries, allowing distinct initial and final projections,
with the extension order and its exact trace distance. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

structure PartialIsometry (M : VonNeumannAlgebra H) where
  support : AlgebraProjection M
  val : M.toStarSubalgebra
  initial : star val*val=support.val

namespace PartialIsometry

def Extends (v w : PartialIsometry M) : Prop := w.val*v.support.val=v.val

@[ext] theorem ext {v w : PartialIsometry M} (h : v.val=w.val) : v=w := by
  have hp : v.support=w.support := by
    apply Subtype.ext
    calc v.support.val = star v.val*v.val := v.initial.symm
         _ = star w.val*w.val := by rw [h]
         _ = w.support.val := w.initial
  cases v
  cases w
  cases hp
  cases h
  rfl

end PartialIsometry

end

/-! Actual L2 limits of partial isometries and upper bounds of increasing
sequences, using their exact support-trace distance. -/

/-! Orthogonal patching with distinct source and target supports. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

def zero : PartialIsometry M := ⟨⟨0,IsStarProjection.zero _⟩,0,by simp⟩

theorem orthogonal_reverse (p q : AlgebraProjection M) (h : p.val*q.val=0) :
    q.val*p.val=0 := by
  simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
    q.property.isSelfAdjoint.star_eq,star_zero] using congrArg star h

end PartialIsometry

end

/-! A maximal actual partial isometry between subprojections of prescribed
projections. Chain upper bounds are constructed L2 limits, not assumed. -/
open Filter
open scoped Topology

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Pinching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- A finite projection partition of a corner, allowing zero pieces. -/
structure CornerPartition (p : AlgebraProjection M) where
  size : ℕ
  piece : Fin size → AlgebraProjection M
  orthogonal : ∀ i j, i ≠ j → (piece i).val * (piece j).val = 0
  total : ∑ i, (piece i).val = p.val

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem piece_le (i : Fin Q.size) : Q.piece i ≤ p := by
  change p.val * (Q.piece i).val = (Q.piece i).val
  rw [← Q.total, Finset.sum_mul]
  simpa only [(Q.piece i).property.isIdempotentElem.eq] using
    (Finset.sum_eq_single i (fun j _ hji => Q.orthogonal j i hji)
      (fun h => (h (Finset.mem_univ i)).elim))

def pinch (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  ∑ i, (Q.piece i).val * x * (Q.piece i).val

end CornerPartition

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M}

/-- Reindex an explicitly finite orthogonal family by Fin. -/
def ofFamily {ι : Type*} [Fintype ι] (a : ι → AlgebraProjection M)
    (ha : ∀ i j, i ≠ j → (a i).val*(a j).val=0)
    (ht : ∑ i, (a i).val=p.val) : CornerPartition p where
  size := Fintype.card ι
  piece i := a ((Fintype.equivFin ι).symm i)
  orthogonal i j hij := ha _ _ (fun h => hij ((Fintype.equivFin ι).symm.injective h))
  total := by simpa only using (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (a i).val)).trans ht

variable (Q : CornerPartition p) (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

theorem blockFamily_orthogonal (a b : (i : Fin Q.size) × Fin (R i).size) (hab : a ≠ b) :
    ((R a.1).piece a.2).val * ((R b.1).piece b.2).val = 0 := by
  by_cases h : a.1=b.1
  · obtain ⟨i,j⟩ := a
    obtain ⟨k,l⟩ := b
    dsimp at h ⊢
    subst k
    exact (R i).orthogonal j l (fun h => hab (by cases h; rfl))
  · exact orthogonal_subprojections (Q.orthogonal a.1 b.1 h)
      ((R a.1).piece_le a.2) ((R b.1).piece_le b.2)

theorem blockFamily_total :
    (∑ a : (i : Fin Q.size) × Fin (R i).size, ((R a.1).piece a.2).val) = p.val := by
  rw [Fintype.sum_sigma]
  simpa only [(R _).total] using Q.total

/-- All blocks are replaced by their chosen finite subpartitions. -/
def refineBlocks : CornerPartition p :=
  ofFamily (fun a : (i : Fin Q.size) × Fin (R i).size => (R a.1).piece a.2)
    (Q.blockFamily_orthogonal R) (Q.blockFamily_total R)

end CornerPartition

end

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Supports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- The orthogonal projection onto an operator's kernel belongs to its
von Neumann algebra. This uses the actual double-commutant definition. -/
theorem kernelProjection_mem (x : M.toStarSubalgebra) :
    (x.val.ker).starProjection ∈ M := by
  apply (VonNeumannAlgebra.IsStarProjection.mem_iff
    isStarProjection_starProjection M).mpr
  intro y hy
  rw [Submodule.range_starProjection]
  intro ξ hξ
  change x.val (y ξ)=0
  have hc := (VonNeumannAlgebra.mem_commutant_iff.mp hy) x.val x.property
  have he := congrArg (fun t : H →L[ℂ] H => t ξ) hc
  change x.val (y ξ)=y (x.val ξ) at he
  rw [he,show x.val ξ=0 from hξ,map_zero]

def kernelProjection (x : M.toStarSubalgebra) : AlgebraProjection M :=
  ⟨⟨x.val.ker.starProjection,kernelProjection_mem x⟩,by
    constructor
    · apply Subtype.ext
      exact (isStarProjection_starProjection
        (U := x.val.ker)).isIdempotentElem.eq
    · apply Subtype.ext
      exact (isStarProjection_starProjection
        (U := x.val.ker)).isSelfAdjoint.star_eq⟩

theorem mul_kernelProjection (x : M.toStarSubalgebra) : x*(kernelProjection x).val=0 := by
  apply Subtype.ext
  ext ξ
  exact Submodule.starProjection_apply_mem x.val.ker ξ

theorem kernelProjection_fixes (x : M.toStarSubalgebra) (ξ : H) (hξ : x.val ξ=0) :
    ((kernelProjection x).val : H →L[ℂ] H) ξ=ξ :=
  Submodule.starProjection_eq_self_iff.mpr hξ

/-- This is the largest algebra projection annihilated on the left by x. -/
theorem le_kernelProjection_iff (x : M.toStarSubalgebra) (q : AlgebraProjection M) :
    q ≤ kernelProjection x ↔ x*q.val=0 := by
  constructor
  · intro h
    calc x*q.val = x*((kernelProjection x).val*q.val) := by rw [h]
      _ = 0 := by rw [← mul_assoc,mul_kernelProjection,zero_mul]
  · intro h
    apply Subtype.ext
    ext ξ
    apply kernelProjection_fixes
    have he := congrArg (fun t : M.toStarSubalgebra => (t : H →L[ℂ] H) ξ) h
    exact he

/-- The projection onto the closed range of x, expressed via ker(x*). -/
def rangeProjection (x : M.toStarSubalgebra) : AlgebraProjection M :=
  ⟨1-(kernelProjection (star x)).val,(kernelProjection (star x)).property.one_sub⟩

theorem rangeProjection_mul (x : M.toStarSubalgebra) : (rangeProjection x).val*x=x := by
  have h := congrArg star (mul_kernelProjection (star x))
  simp only [star_mul,(kernelProjection (star x)).property.isSelfAdjoint.star_eq,
    star_star,star_zero] at h
  change (1-(kernelProjection (star x)).val)*x=x
  rw [sub_mul,one_mul,h,sub_zero]

/-- Minimality retains any prescribed corner supporting x. -/
theorem rangeProjection_le_iff (x : M.toStarSubalgebra) (q : AlgebraProjection M) :
    rangeProjection x ≤ q ↔ q.val*x=x := by
  constructor
  · intro h
    calc q.val*x = q.val*((rangeProjection x).val*x) := by rw [rangeProjection_mul]
      _ = x := by rw [← mul_assoc,h,rangeProjection_mul]
  · intro h
    let r : AlgebraProjection M := ⟨1-q.val,q.property.one_sub⟩
    have hz : star x*r.val=0 := by
      have hh := congrArg star h
      simp only [star_mul,q.property.isSelfAdjoint.star_eq] at hh
      change star x*(1-q.val)=0
      rw [mul_sub,mul_one,hh,sub_self]
    have hr := (le_kernelProjection_iff (star x) r).mpr hz
    have hs := projection_mul_of_le hr
    change (1-q.val)*(kernelProjection (star x)).val=1-q.val at hs
    change q.val*(1-(kernelProjection (star x)).val)=1-(kernelProjection (star x)).val
    simp only [sub_mul,one_mul] at hs
    simp only [mul_sub,mul_one]
    apply (sub_eq_sub_iff_add_eq_add).mpr
    have hh := (sub_eq_sub_iff_add_eq_add).mp hs
    simpa only [add_comm,add_left_comm,add_assoc] using hh

end

/-! Spectral sign cuts from continuous positive parts and actual range projections.
These are constructed operators, not assumed Borel functional calculus data. -/
open scoped CStarAlgebra

/-! A polar operator is constructed by extending the isometry on a range.
No polar-decomposition or projection-comparison hypothesis is used. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_isometric_range_factor (a x : H →L[ℂ] H)
    (hnorm : ∀ ξ, ‖x ξ‖ = ‖a ξ‖) :
    ∃ v : H →L[ℂ] H, v * a = x ∧
      star v * v = a.range.topologicalClosure.starProjection ∧
      v * a.range.topologicalClosure.starProjection = v := by
  let K := a.range.topologicalClosure
  let e : a.range →L[ℂ] K :=
    ⟨Submodule.inclusion a.range.le_topologicalClosure,
      continuous_inclusion a.range.le_topologicalClosure⟩
  have hd : DenseRange e :=
    (denseRange_inclusion_iff a.range.le_topologicalClosure).mpr (by rfl)
  have he : IsUniformInducing e :=
    (show Isometry e from fun _ _ => rfl).isUniformInducing
  let f : a.range →L[ℂ] H := x.toLinearMap.compLeftInverse a.toLinearMap
  have hf (ξ : H) : f ⟨a ξ, ⟨ξ, rfl⟩⟩ = x ξ :=
    LinearMap.compLeftInverse_apply_of_bdd _ _ ⟨1, by simp [hnorm]⟩ _ _ rfl
  let g : K →L[ℂ] H := f.extend e
  have hg (ξ : H) : g (e ⟨a ξ, ⟨ξ, rfl⟩⟩) = x ξ :=
    (ContinuousLinearMap.extend_eq f hd he _).trans (hf ξ)
  have hgNorm : ∀ ξ : K, ‖g ξ‖ = ‖ξ‖ := by
    intro ξ
    refine hd.induction_on (p := fun ζ : K => ‖g ζ‖=‖ζ‖) ξ
      (isClosed_eq (g.continuous.norm) continuous_norm) ?_
    rintro ⟨_, ζ, rfl⟩
    exact (congrArg norm (hg ζ)).trans (hnorm ζ)
  let v : H →L[ℂ] H := g.comp K.orthogonalProjectionOnto
  have hva : v * a = x := by
    ext ξ
    change g (K.orthogonalProjectionOnto (a ξ)) = x ξ
    have hh : K.orthogonalProjectionOnto (a ξ) = e ⟨a ξ, ⟨ξ,rfl⟩⟩ := by
      apply Subtype.ext
      exact Submodule.starProjection_eq_self_iff.mpr
        (a.range.le_topologicalClosure ⟨ξ,rfl⟩)
    rw [hh,hg]
  have hvs : v * K.starProjection = v := by
    ext ξ
    change g (K.orthogonalProjectionOnto (K.starProjection ξ)) =
      g (K.orthogonalProjectionOnto ξ)
    congr 1
    exact K.orthogonalProjectionOnto_mem_subspace_eq_self _
  refine ⟨v,hva,?_,hvs⟩
  have heq : (star v * v).toLinearMap = K.starProjection.toLinearMap := by
    apply (ext_inner_map _ _).mp
    intro ξ
    change inner ℂ ((star v) (v ξ)) ξ = inner ℂ (K.starProjection ξ) ξ
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left,
      inner_self_eq_norm_sq_to_K]
    change (‖g (K.orthogonalProjectionOnto ξ)‖ : ℂ)^2 = _
    rw [hgNorm]
    have hh := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (𝕜 := ℂ) (K.orthogonalProjectionOnto ξ) ξ
    rw [inner_self_eq_norm_sq_to_K] at hh
    rw [Submodule.starProjection_apply]
    exact hh
  ext ξ
  exact congrArg (fun t : H →ₗ[ℂ] H => t ξ) heq

end

/-! Polar decomposition inside the given concrete von Neumann algebra. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem rangeProjection_eq_closure_projection (x : M.toStarSubalgebra) :
    ((rangeProjection x).val : H →L[ℂ] H) = x.val.range.topologicalClosure.starProjection := by
  have he : (star x.val).kerᗮ = x.val.range.topologicalClosure := by
    simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint]
      using (star x.val).orthogonal_ker
  change 1-(star x.val).ker.starProjection = _
  have hh := (Submodule.starProjection_orthogonal (star x.val).ker).symm
  simp only [he] at hh
  exact hh

theorem mul_closure_range_projection_eq_zero (a b : H →L[ℂ] H) (h : b*a=0) :
    b*a.range.topologicalClosure.starProjection=0 := by
  have hr : a.range ≤ b.ker := by
    rintro _ ⟨ξ,rfl⟩
    exact congrArg (fun t : H →L[ℂ] H => t ξ) h
  have hc : a.range.topologicalClosure ≤ b.ker :=
    a.range.topologicalClosure_minimal hr b.isClosed_ker
  ext ξ
  exact hc (Submodule.starProjection_apply_mem _ ξ)

end

/-! Exact initial and final support projections of the constructed polar part. -/
open scoped CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralPinching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/
section
open scoped CStarAlgebra BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def cornerSpectralShift (p : AlgebraProjection M) (x : M.toStarSubalgebra) (t : ℝ) :
    M.toStarSubalgebra := p.val*x*p.val-(t : ℂ) • p.val

theorem cornerSpectralShift_support (p : AlgebraProjection M) (x : M.toStarSubalgebra) (t : ℝ) :
    cornerSpectralShift p x t*p.val=cornerSpectralShift p x t := by
  simp only [cornerSpectralShift,sub_mul,smul_mul_assoc,mul_assoc,p.property.isIdempotentElem.eq]

end

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/

/-! Interval bounds propagated through constructed spectral corner splits. -/

/-! Finite dyadic trees of actual spectral interval cuts. -/

/-! Constructed cuts preserve commutation with other operators. -/

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

def jointPiece (a : Fin Q.size × Fin R.size) : AlgebraProjection M :=
  ⟨(Q.piece a.1).val*(R.piece a.2).val,
    (Q.piece a.1).property.mul (R.piece a.2).property (hc a.1 a.2)⟩

theorem jointPiece_le_left (a : Fin Q.size × Fin R.size) : Q.jointPiece R hc a ≤ Q.piece a.1 := by
  change (Q.piece a.1).val*((Q.piece a.1).val*(R.piece a.2).val)=(Q.piece a.1).val*(R.piece a.2).val
  rw [← mul_assoc,(Q.piece a.1).property.isIdempotentElem.eq]

theorem jointPiece_le_right (a : Fin Q.size × Fin R.size) : Q.jointPiece R hc a ≤ R.piece a.2 := by
  change (R.piece a.2).val*((Q.piece a.1).val*(R.piece a.2).val)=(Q.piece a.1).val*(R.piece a.2).val
  rw [← mul_assoc,← (hc a.1 a.2).eq,mul_assoc,(R.piece a.2).property.isIdempotentElem.eq]

theorem jointPiece_orthogonal (a b : Fin Q.size × Fin R.size) (hab : a ≠ b) :
    (Q.jointPiece R hc a).val*(Q.jointPiece R hc b).val=0 := by
  by_cases h : a.1=b.1
  · have h₂ : a.2 ≠ b.2 := fun h₂ => hab (Prod.ext h h₂)
    exact orthogonal_subprojections (R.orthogonal a.2 b.2 h₂)
      (Q.jointPiece_le_right R hc a) (Q.jointPiece_le_right R hc b)
  · exact orthogonal_subprojections (Q.orthogonal a.1 b.1 h)
      (Q.jointPiece_le_left R hc a) (Q.jointPiece_le_left R hc b)

theorem jointPiece_total : (∑ a : Fin Q.size × Fin R.size, (Q.jointPiece R hc a).val)=p.val := by
  change (∑ a : Fin Q.size × Fin R.size, (Q.piece a.1).val*(R.piece a.2).val)=p.val
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum,R.total,projection_mul_of_le (Q.piece_le _)]
  exact Q.total

def joint : CornerPartition p := ofFamily (Q.jointPiece R hc)
  (Q.jointPiece_orthogonal R hc) (Q.jointPiece_total R hc)

end CornerPartition

/-! Simultaneous finite spectral approximation of two commuting self-adjoint
operators. The same actual partition is used for both. -/

end

/-! Finite spectral approximation for an actual normal operator. -/
section
open scoped BigOperators ComplexStarModule
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def identityProjection (M : VonNeumannAlgebra H) : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩

end

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem orthogonal_family_sum_projection {ι : Type*} [Fintype ι]
    (q : ι → AlgebraProjection M)
    (hq : ∀ i j, i ≠ j → (q i).val*(q j).val=0) :
    IsStarProjection (∑ i,(q i).val) := by
  classical
  constructor
  · show (∑ i,(q i).val)*(∑ i,(q i).val)=∑ i,(q i).val
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum,Finset.sum_eq_single i]
    · exact (q i).property.isIdempotentElem.eq
    · intro j _ hji
      exact hq i j hji.symm
    · simp
  · show star (∑ i,(q i).val)=∑ i,(q i).val
    simp only [star_sum, (q _).property.isSelfAdjoint.star_eq]

theorem exists_completed_orthogonal_family {ι : Type*} [Fintype ι]
    (q : ι → AlgebraProjection M)
    (hq : ∀ i j, i ≠ j → (q i).val*(q j).val=0) :
    ∃ Q : CornerPartition (identityProjection M),
      ∃ e : Option ι ≃ Fin Q.size,
        (∀ i,Q.piece (e (some i))=q i) ∧
        (Q.piece (e none)).val=1-∑ i,(q i).val := by
  classical
  let s := ∑ i,(q i).val
  have hs : IsStarProjection s := orthogonal_family_sum_projection q hq
  let a : Option ι → AlgebraProjection M := fun i =>
    i.elim ⟨1-s,hs.one_sub⟩ q
  have hleft (i : ι) : s*(q i).val=(q i).val := by
    dsimp [s]
    rw [Finset.sum_mul,Finset.sum_eq_single i]
    · exact (q i).property.isIdempotentElem.eq
    · intro j _ hji
      exact hq j i hji
    · simp
  have hright (i : ι) : (q i).val*s=(q i).val := by
    simpa only [star_mul,hs.isSelfAdjoint.star_eq,
      (q i).property.isSelfAdjoint.star_eq] using congrArg star (hleft i)
  have ha (i j : Option ι) (hij : i ≠ j) : (a i).val*(a j).val=0 := by
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => change (1-s)*(q j).val=0; rw [sub_mul,one_mul,hleft,sub_self]
    | some i =>
      cases j with
      | none => change (q i).val*(1-s)=0; rw [mul_sub,mul_one,hright,sub_self]
      | some j => exact hq i j (fun h => hij (congrArg some h))
  have ht : (∑ i,(a i).val)=(identityProjection M).val := by
    rw [Fintype.sum_option]
    change (1-s)+s=1
    abel
  let Q := CornerPartition.ofFamily a ha ht
  refine ⟨Q,Fintype.equivFin (Option ι),?_,?_⟩
  · intro i
    change a ((Fintype.equivFin (Option ι)).symm
      ((Fintype.equivFin (Option ι)) (some i)))=q i
    rw [Equiv.symm_apply_apply]
    rfl
  · change (a ((Fintype.equivFin (Option ι)).symm
      ((Fintype.equivFin (Option ι)) none))).val=1-s
    rw [Equiv.symm_apply_apply]
    rfl

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)
variable (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

def blockIndices (i : Fin Q.size) : Finset (Fin (Q.refineBlocks R).size) :=
  Finset.univ.filter fun j =>
    ((Fintype.equivFin ((k : Fin Q.size) × Fin (R k).size)).symm j).1=i

theorem blockIndices_disjoint {i j : Fin Q.size} (hij : i ≠ j) :
    Disjoint (Q.blockIndices R i) (Q.blockIndices R j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k hi hj
  exact hij ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

theorem sum_blockIndices (i : Fin Q.size) :
    (∑ j ∈ Q.blockIndices R i,((Q.refineBlocks R).piece j).val)=(Q.piece i).val := by
  classical
  rw [blockIndices,Finset.sum_filter]
  let e := (Fintype.equivFin ((k : Fin Q.size) × Fin (R k).size)).symm
  change (∑ j,if (e j).1=i then ((R (e j).1).piece (e j).2).val else 0)=_
  rw [Equiv.sum_comp e (fun a => if a.1=i then ((R a.1).piece a.2).val else 0),
    Fintype.sum_sigma]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,(R _).total]
  simp

end CornerPartition

end Generator.Tracial

end

end OAI
end


