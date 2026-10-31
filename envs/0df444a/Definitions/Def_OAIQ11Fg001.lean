-- Prove2me | Definitions.Def_OAIQ11Fg001
-- name    : OAIQ11Fg001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T09:29:14.313204+00:00
-- url     : https://prove2.me/theorems/499d3245-921b-4d66-b6e7-44e4c1698a2b
-- title:
--   Definitions bundle OAIQ11Fg001 of the split of OpenAI, Relative generation and the generator problem for finite factors
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Generator.single_generation_of_II1_separable_predual`, carved from OpenAI's openai/math development (OpenAI, *Relative generation and the generator problem for finite factors*, OpenAI Math Release, September 23, 2026, result family 296, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 123 declarations of OpenAI's Lean: 58 definitions, 3 inductive types or structures, 3 instances and 59 theorems. The definitions and types are `OAI.Generator.FreeConvolution.leftRegular`, `OAI.Generator.MatrixEncoding.E11`, `OAI.Generator.MatrixEncoding.E12`, `OAI.Generator.MatrixEncoding.E21`, `OAI.Generator.MatrixEncoding.E22`, `OAI.Generator.MatrixEncoding.corner`, `OAI.Generator.MatrixEncoding.encodeA`, `OAI.Generator.MatrixEncoding.encodeB`, `OAI.Generator.MatrixUnitSystem.fullProjectionMatrix`, `OAI.Generator.PrefixLabel`, `OAI.Generator.RelativePolynomial`, `OAI.Generator.SquareSpace`, `OAI.Generator.Tracial.AlgebraProjection`, `OAI.Generator.Tracial.AlgebraProjection.Equivalent`, `OAI.Generator.Tracial.AlgebraProjection.Subequivalent`, `OAI.Generator.Tracial.AlgebraProjection.vectorValue`, `OAI.Generator.Tracial.CornerPartition`, `OAI.Generator.Tracial.CornerPartition.pinch`, `OAI.Generator.Tracial.CornerPartition.single`, `OAI.Generator.Tracial.PartialIsometry`, `OAI.Generator.Tracial.PartialIsometry.Extends`, `OAI.Generator.Tracial.PartialIsometry.adjoint`, `OAI.Generator.Tracial.PartialIsometry.compose`, `OAI.Generator.Tracial.PartialIsometry.onProjection`, `OAI.Generator.Tracial.PartialIsometry.patch`, `OAI.Generator.Tracial.PartialIsometry.target`, `OAI.Generator.Tracial.PartialIsometry.zero`, `OAI.Generator.Tracial.identityProjection`, `OAI.Generator.Tracial.insideAlgebra`, `OAI.Generator.Tracial.instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions`, `OAI.Generator.Tracial.instLESubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions`, `OAI.Generator.Tracial.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions`, `OAI.Generator.Tracial.interiorCStar`, `OAI.Generator.Tracial.interiorLE`, `OAI.Generator.Tracial.interiorOrder`, `OAI.Generator.Tracial.interiorPreorder`, `OAI.Generator.Tracial.polarCStar`, `OAI.Generator.Tracial.polarOrder`, `OAI.Generator.Tracial.polarSupportsCStar`, `OAI.Generator.Tracial.projectionOrbitClosure` and 21 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FactorGeneration_Bicommutant`, `FactorGeneration_Convolution`, `FactorGeneration_CornerTrace`, `FactorGeneration_DyadicComparison`, `FactorGeneration_FiniteComparison`, `FactorGeneration_FreeWords`, `FactorGeneration_HilbertLimits`, `FactorGeneration_HilbertProjections`, `FactorGeneration_LongWords`, `FactorGeneration_MatrixEncoding`, `FactorGeneration_MatrixGenerators`, `FactorGeneration_NormalDimension`, `FactorGeneration_OperatorLimits`, `FactorGeneration_PartialIsometries`, `FactorGeneration_Pinching`, `FactorGeneration_ProjectionLimits`, `FactorGeneration_RelativeGeneration`, `FactorGeneration_SpectralApproximation`, `FactorGeneration_SpectralTruncation`, `FactorGeneration_Supports`, `FactorGeneration_Target`, `FactorGeneration_TracialInclusion`.
--
--   **Imports.** It imports the published bundle `Def_FactorGeneration`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ11Fg003`, `OAIQ11Fg004`, `OAIQ11Fg005` and `OAIQ11Fg006`; the statements `OAI_Generator_MatrixEncoding_E22_commute_encodeA`, `OAI_Generator_MatrixEncoding_E22_idempotent`, `OAI_Generator_MatrixEncoding_complement`, `OAI_Generator_MatrixEncoding_encodeA_scalar_shift`, `OAI_Generator_MatrixEncoding_encodeA_selfAdjoint`, `OAI_Generator_MatrixEncoding_encodeB_selfAdjoint`, `OAI_Generator_MatrixEncoding_encoded_corners_mem_scalar`, `OAI_Generator_MatrixEncoding_eq_top_of_corner_and_units`, `OAI_Generator_MatrixEncoding_matrix_units_mem`, `OAI_Generator_Tracial_exists_finite_partial_independence`, `OAI_Generator_Tracial_exists_irreducible_centered_partition`, `OAI_Generator_Tracial_exists_irreducible_corner_zero_trace_partition`, `OAI.Generator.Tracial.exists_matrixUnits_for_partition`, `OAI_Generator_Tracial_exists_scalar_pinching_for_matrixUnits` and `OAI_Generator_evaluated_prefixes`; the proofs of `OAI_Generator_MatrixEncoding_E22_commute_encodeA`, `OAI_Generator_MatrixEncoding_E22_idempotent`, `OAI_Generator_MatrixEncoding_complement`, `OAI_Generator_MatrixEncoding_encodeA_scalar_shift`, `OAI_Generator_MatrixEncoding_encodeA_selfAdjoint`, `OAI_Generator_MatrixEncoding_encodeB_selfAdjoint`, `OAI_Generator_MatrixEncoding_encoded_corners_mem_scalar`, `OAI_Generator_MatrixEncoding_eq_top_of_corner_and_units`, `OAI_Generator_MatrixEncoding_matrix_units_mem` and `OAI_Generator_evaluated_prefixes`.
-- source:
--   OpenAI, Relative generation and the generator problem for finite factors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 296; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_FactorGeneration

section
-- module Solutions.OAIQ11_FG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Target
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

theorem wstar_closed (s : Set (H →L[ℂ] H)) : WOTClosed (wstar s) := by
  unfold WOTClosed
  have heq : {T : H →WOT[ℂ] H | T.toCLM ∈ wstar s} =
      ⋂ (S : StarSubalgebra ℂ (H →L[ℂ] H)) (_ : WOTClosed S ∧ s ⊆ S),
        {T : H →WOT[ℂ] H | T.toCLM ∈ S} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, wstar, StarSubalgebra.mem_sInf]
  rw [heq]
  exact isClosed_iInter fun S => isClosed_iInter fun h => h.1

end

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Bicommutant
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
-- module Solutions.OAIQ11_FG.FactorGeneration_FreeWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Generator

/-! Distinct nonidentity off-diagonal prefix ratios, distinguished by abelian exponent coordinates. Labels start at zero. -/

def freePrefix : ℕ → FreeGroup ℕ
  | 0 => 1
  | n + 1 => freePrefix n * FreeGroup.of n

def prefixRatio (k j : ℕ) : FreeGroup ℕ := freePrefix k * (freePrefix j)⁻¹

/-! The exact multiplicity sum for prefix ratios, with labels g_(k+1) indexed by k : Fin n. -/
noncomputable section
open scoped BigOperators
local instance instDecidableEqFreeGroupNat_solutions : DecidableEq (FreeGroup ℕ) := Classical.decEq _

def pairRatio {n : ℕ} (ij : Fin n × Fin n) : FreeGroup ℕ :=
  prefixRatio (ij.1.val + 1) (ij.2.val + 1)

def ratioLabels (n : ℕ) : Finset (FreeGroup ℕ) := by
  classical
  exact insert 1 ((Finset.univ : Finset (Fin n)).offDiag.image pairRatio)

end

/-! Ordered prefix products. The element h denotes the unitary exponential of a self-adjoint operator, not its logarithm. The final letter is unperturbed. -/

end Generator

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Coordinate masks and permutations on the actual complex square-summable space.
These implement the Hilbert-space operations used in lem:length-one-convolution. -/
section
open scoped BigOperators InnerProductSpace ENNReal
attribute [local instance] Classical.propDecidable
abbrev SquareSpace (X : Type*) := lp (fun _ : X => ℂ) 2

variable {X I : Type*}

theorem squareSpace_norm_sq (f : SquareSpace X) :
    ‖f‖ ^ 2 = ∑' x, ‖f x‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f

def coordinateMask (s : Set X) (f : SquareSpace X) : SquareSpace X :=
  ⟨s.indicator f, f.property.mono' (fun x => by
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx])⟩

@[simp] theorem coordinateMask_apply (s : Set X) (f : SquareSpace X) (x : X) :
    coordinateMask s f x = if x ∈ s then f x else 0 := rfl

def coordinatePermute (e : X ≃ X) (f : SquareSpace X) : SquareSpace X :=
  ⟨fun x => f (e x), memℓp_gen ((e.summable_iff).2 (f.property.summable (by norm_num)))⟩

@[simp] theorem coordinatePermute_apply (e : X ≃ X) (f : SquareSpace X) (x : X) :
    coordinatePermute e f x = f (e x) := rfl

theorem coordinatePermute_norm (e : X ≃ X) (f : SquareSpace X) :
    ‖coordinatePermute e f‖ = ‖f‖ := by
  have h : ‖coordinatePermute e f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [squareSpace_norm_sq, squareSpace_norm_sq]
    exact e.tsum_eq (fun x => ‖f x‖ ^ 2)
  nlinarith [norm_nonneg (coordinatePermute e f), norm_nonneg f]

/-- Reindexing by a permutation, as a bounded complex linear operator. -/
def coordinatePermuteCLM (e : X ≃ X) : SquareSpace X →L[ℂ] SquareSpace X :=
  LinearMap.mkContinuous
    { toFun := coordinatePermute e
      map_add' := by intros; ext x; rfl
      map_smul' := by intros; ext x; rfl }
    1 (fun f => by simpa using (coordinatePermute_norm e f).le)

@[simp] theorem coordinatePermuteCLM_apply (e : X ≃ X) (f : SquareSpace X) (x : X) :
    coordinatePermuteCLM e f x = f (e x) := rfl

end

/-! Length-one convolution bounds for the left regular representation of a free group on an arbitrary basis. -/
section
open scoped BigOperators InnerProductSpace
attribute [local instance] Classical.propDecidable Classical.decEq
namespace FreeConvolution
variable {A : Type*}

/-- The actual left regular translation λ(g)η(x)=η(g⁻¹x). -/
def leftRegular (g : FreeGroup A) : SquareSpace (FreeGroup A) →L[ℂ] SquareSpace (FreeGroup A) :=
  coordinatePermuteCLM (Equiv.mulLeft g⁻¹)

end FreeConvolution

end

/-! Group-ring action on ℓ² and the coefficient-vector identity. -/

/-! The finite coefficient L² identity from orthonormality of reduced-word images. -/

/-! Multiplicity-weighted length-one convolution bounds. -/
open scoped BigOperators
open Generator.FreeConvolution

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_OperatorLimits
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
-- module Solutions.OAIQ11_FG.FactorGeneration_ProjectionLimits
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

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_TracialInclusion
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

/-- P, as a star subalgebra of M. Its completeness is derived, not assumed. -/
def insideAlgebra : StarSubalgebra ℂ M.toStarSubalgebra :=
  P.toStarSubalgebra.comap M.toStarSubalgebra.subtype

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_CornerTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Trace estimates in the actual ambient algebra. The corner scalar uses
its normalized trace. These estimates do not assume or assert the existence
of a local-quantizing projection. -/

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/
section
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : CStarAlgebra M.toStarSubalgebra := {}
local instance instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance instLESubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! A finite compression-energy estimate yields a nonzero corner projection with simultaneous L1 control. -/

/-! The scalar trace estimate for a term with two supported patch letters.
It reduces to the actual compressed middle coefficient and keeps trace(q),
not trace(p), as the scale of the error. -/

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HilbertLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorOrbitMap (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : S →ₗ[ℂ] H where
  toFun a := a.val ξ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def vectorOrbitClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H :=
  (vectorOrbitMap S ξ).range.topologicalClosure

theorem vectorOrbitClosure_invariant (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H)
    (a : S) {y : H} (hy : y ∈ vectorOrbitClosure S ξ) : a.val y ∈ vectorOrbitClosure S ξ := by
  have h : (vectorOrbitMap S ξ).range.topologicalClosure ≤
      (vectorOrbitClosure S ξ).comap a.val.toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨b,rfl⟩
      exact Submodule.le_topologicalClosure _ ⟨a*b,rfl⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage a.val.continuous
  exact h hy

end

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology

/-! On a uniformly operator-norm bounded family in a faithfully vector-traced
von Neumann algebra, L2 convergence implies strong and adjoint-strong convergence
in the original Hilbert space. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_PartialIsometries
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

theorem mul_support (v : PartialIsometry M) : v.val*v.support.val=v.val := by
  have htr : star v.val*(v.val*v.support.val)=v.support.val := by
    rw [← mul_assoc,v.initial,v.support.property.isIdempotentElem.eq]
  have he : star (v.val-v.val*v.support.val)*(v.val-v.val*v.support.val)=0 := by
    simp only [star_sub,star_mul,v.support.property.isSelfAdjoint.star_eq,sub_mul,mul_sub,
      mul_assoc,v.initial,htr,v.support.property.isIdempotentElem.eq,sub_self]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp he)).symm

def target (v : PartialIsometry M) : AlgebraProjection M :=
  ⟨v.val*star v.val,⟨by
    change (v.val*star v.val)*(v.val*star v.val)=v.val*star v.val
    calc _ = (v.val*(star v.val*v.val))*star v.val := by simp only [mul_assoc]
         _ = v.val*star v.val := by rw [v.initial,v.mul_support],
    IsSelfAdjoint.mul_star_self _⟩⟩

theorem target_mul (v : PartialIsometry M) : v.target.val*v.val=v.val := by
  change (v.val*star v.val)*v.val=v.val
  rw [mul_assoc,v.initial,v.mul_support]

def adjoint (v : PartialIsometry M) : PartialIsometry M :=
  ⟨v.target,star v.val,by simp only [star_star]; rfl⟩

theorem norm_le_one (v : PartialIsometry M) : ‖v.val‖ ≤ 1 := by
  have he : ‖v.val‖*‖v.val‖=‖v.support.val‖ := by
    rw [← CStarRing.norm_star_mul_self,v.initial]
  have hp := v.support.property.norm_le
  nlinarith [norm_nonneg v.val]

def Extends (v w : PartialIsometry M) : Prop := w.val*v.support.val=v.val

theorem support_le_of_extends {v w : PartialIsometry M} (h : Extends v w) :
    v.support ≤ w.support := by
  have hh := congrArg (fun z : M.toStarSubalgebra => star z*z) h
  have hcomp : v.support.val*w.support.val*v.support.val=v.support.val := by
    calc _ = v.support.val*(star w.val*w.val)*v.support.val := by rw [w.initial]
         _ = star (w.val*v.support.val)*(w.val*v.support.val) := by
           simp only [star_mul,v.support.property.isSelfAdjoint.star_eq,mul_assoc]
         _ = v.support.val := hh.trans v.initial
  have hdouble : v.support.val*w.support.val*w.support.val*v.support.val=v.support.val := by
    calc _ = v.support.val*(w.support.val*w.support.val)*v.support.val := by
           simp only [mul_assoc]
         _ = v.support.val := by rw [w.support.property.isIdempotentElem.eq,hcomp]
  have hz : star (v.support.val-w.support.val*v.support.val)*
      (v.support.val-w.support.val*v.support.val)=0 := by
    simp only [star_sub,star_mul,v.support.property.isSelfAdjoint.star_eq,
      w.support.property.isSelfAdjoint.star_eq,sub_mul,mul_sub]
    simp only [← mul_assoc,v.support.property.isIdempotentElem.eq,hcomp,hdouble,
      sub_self]
  exact (sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hz)).symm

theorem cross_initial {v w : PartialIsometry M} (h : Extends v w) :
    star w.val*v.val=v.support.val := by
  calc star w.val*v.val = star w.val*(w.val*v.support.val) := by rw [h]
       _ = v.support.val := by rw [← mul_assoc,w.initial]; exact support_le_of_extends h

theorem cross_initial_rev {v w : PartialIsometry M} (h : Extends v w) :
    star v.val*w.val=v.support.val := by
  simpa only [star_mul,star_star,v.support.property.isSelfAdjoint.star_eq]
    using congrArg star (cross_initial h)

theorem extends_refl (v : PartialIsometry M) : Extends v v := v.mul_support

theorem extends_trans {u v w : PartialIsometry M} (huv : Extends u v) (hvw : Extends v w) :
    Extends u w := by
  change w.val*u.support.val=u.val
  calc w.val*u.support.val = w.val*(v.support.val*u.support.val) := by
         rw [show v.support.val*u.support.val=u.support.val from support_le_of_extends huv]
       _ = u.val := by rw [← mul_assoc,hvw,huv]

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

instance instPartialOrder : PartialOrder (PartialIsometry M) where
  le := Extends
  le_refl := extends_refl
  le_trans _ _ _ := extends_trans
  le_antisymm v w hvw hwv := by
    apply ext
    have hs := le_antisymm (support_le_of_extends hvw) (support_le_of_extends hwv)
    change w.val*v.support.val=v.val at hvw
    rw [hs,w.mul_support] at hvw
    exact hvw.symm

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

theorem support_le_iff_mul (v : PartialIsometry M) (p : AlgebraProjection M) :
    v.support ≤ p ↔ v.val*p.val=v.val := by
  constructor
  · intro h
    calc _ = (v.val*v.support.val)*p.val := by rw [v.mul_support]
         _ = v.val := by rw [mul_assoc,projection_mul_of_le h,v.mul_support]
  · intro h
    have he : v.support.val*p.val=v.support.val := by
      rw [← v.initial,mul_assoc,h]
    change p.val*v.support.val=v.support.val
    simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
      v.support.property.isSelfAdjoint.star_eq] using congrArg star he

theorem target_le_iff_mul (v : PartialIsometry M) (q : AlgebraProjection M) :
    v.target ≤ q ↔ q.val*v.val=v.val := by
  constructor
  · intro h
    calc _ = q.val*(v.target.val*v.val) := by rw [v.target_mul]
         _ = v.val := by rw [← mul_assoc,h,v.target_mul]
  · intro h
    change q.val*(v.val*star v.val)=v.val*star v.val
    rw [← mul_assoc,h]

theorem mul_eq_zero (v w : PartialIsometry M) (h : v.support.val*w.target.val=0) :
    v.val*w.val=0 := by
  calc _ = (v.val*v.support.val)*(w.target.val*w.val) := by
         rw [v.mul_support,w.target_mul]
       _ = v.val*(v.support.val*w.target.val)*w.val := by simp only [mul_assoc]
       _ = 0 := by rw [h,mul_zero,zero_mul]

theorem orthogonal_reverse (p q : AlgebraProjection M) (h : p.val*q.val=0) :
    q.val*p.val=0 := by
  simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
    q.property.isSelfAdjoint.star_eq,star_zero] using congrArg star h

def patch (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0) :
    PartialIsometry M where
  support := ⟨v.support.val+w.support.val,v.support.property.add w.support.property hp⟩
  val := v.val+w.val
  initial := by
    have h₁ : star v.val*w.val=0 := v.adjoint.mul_eq_zero w hq
    have h₂ : star w.val*v.val=0 :=
      w.adjoint.mul_eq_zero v (orthogonal_reverse _ _ hq)
    simp only [star_add,add_mul,mul_add,v.initial,w.initial,h₁,h₂,add_zero,zero_add]

theorem patch_target (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0) :
    (patch v w hp hq).target.val=v.target.val+w.target.val := by
  have hwt : w.adjoint.target=w.support := Subtype.ext (by
    change star w.val*star (star w.val)=w.support.val
    rw [star_star,w.initial])
  have hvt : v.adjoint.target=v.support := Subtype.ext (by
    change star v.val*star (star v.val)=v.support.val
    rw [star_star,v.initial])
  have h₁ : v.val*star w.val=0 := v.mul_eq_zero w.adjoint (by rw [hwt]; exact hp)
  have h₂ : w.val*star v.val=0 := w.mul_eq_zero v.adjoint (by
    rw [hvt]; exact orthogonal_reverse _ _ hp)
  change (v.val+w.val)*star (v.val+w.val)=v.val*star v.val+w.val*star w.val
  simp only [star_add,add_mul,mul_add,h₁,h₂,add_zero,zero_add]

theorem le_patch (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0) :
    v ≤ patch v w hp hq := by
  have hw : w.val*v.support.val=0 := by
    calc _ = (w.val*w.support.val)*v.support.val := by rw [w.mul_support]
         _ = 0 := by rw [mul_assoc,orthogonal_reverse _ _ hp,mul_zero]
  change (v.val+w.val)*v.support.val=v.val
  rw [add_mul,v.mul_support,hw,add_zero]

theorem patch_ne (v w : PartialIsometry M)
    (hp : v.support.val*w.support.val=0) (hq : v.target.val*w.target.val=0)
    (hw : w.support.val≠0) : patch v w hp hq ≠ v := by
  intro he
  have hh := congrArg (fun z : PartialIsometry M => z.support.val) he
  change v.support.val+w.support.val=v.support.val at hh
  exact hw (add_left_cancel (hh.trans (add_zero _).symm))

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
-- module Solutions.OAIQ11_FG.FactorGeneration_Supports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Kernel and range projections constructed in the actual von Neumann algebra.
Membership follows from commutant invariance, with no spectral theorem assumed. -/

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
local instance polarCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance polarOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance polarStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance polarSupportsCStar : CStarAlgebra M.toStarSubalgebra := {}

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_FiniteComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! The closed span of algebra translates of a projection range gives its
central support. All operators act on the original Hilbert space; no trace,
cyclic vector, separability, finiteness, or comparison theorem is assumed. -/
namespace Tracial

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def projectionOrbitVectors (p : AlgebraProjection M) : Set H :=
  {y | ∃ a : M.toStarSubalgebra, ∃ x : H, y=a.val (p.val.val x)}

def projectionOrbitClosure (p : AlgebraProjection M) : Submodule ℂ H :=
  (Submodule.span ℂ (projectionOrbitVectors p)).topologicalClosure

end

/-! Trace-free upper bounds of arbitrary directed nets of partial isometries.
A weak operator ultralimit suffices: extension identities with each fixed net
member force the limit to satisfy b b* b = b. No trace or countability is used. -/
section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- Left multiplication by a fixed operator preserves matrix-coefficient limits. -/
theorem wot_limit_mul_left {ι : Type*} {l : Filter ι}
    (a : ι → M.toStarSubalgebra) (b c : M.toStarSubalgebra)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x)))) :
    ∀ x y : H, Tendsto (fun i => inner ℂ y ((c*a i).val x)) l
      (𝓝 (inner ℂ y ((c*b).val x))) := by
  intro x y
  change Tendsto (fun i => inner ℂ y (c.val ((a i).val x))) l
    (𝓝 (inner ℂ y (c.val (b.val x))))
  simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    using ht x (star c.val y)

/-- Right multiplication by a fixed operator preserves matrix-coefficient limits. -/
theorem wot_limit_mul_right {ι : Type*} {l : Filter ι}
    (a : ι → M.toStarSubalgebra) (b c : M.toStarSubalgebra)
    (ht : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x)))) :
    ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i*c).val x)) l
      (𝓝 (inner ℂ y ((b*c).val x))) := fun x y => ht (c.val x) y

/-- Matrix coefficients determine an element of the concrete algebra. -/
theorem wot_limit_unique {ι : Type*} {l : Filter ι} [l.NeBot]
    (a : ι → M.toStarSubalgebra) (b c : M.toStarSubalgebra)
    (hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (b.val x))))
    (hc : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val x)) l
      (𝓝 (inner ℂ y (c.val x)))) : b=c := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact ext_inner_left ℂ (fun y => tendsto_nhds_unique (hb x y) (hc x y))

namespace PartialIsometry

/-- Every monotone directed net has a partial-isometry upper bound, retaining
any prescribed bounds on its initial and final projections. -/
theorem traceFree_monotone_upper_bound
    {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (a : ι → PartialIsometry M) (ha : Monotone a)
    (p q : AlgebraProjection M) (hp : ∀ i, (a i).support ≤ p)
    (hq : ∀ i, (a i).target ≤ q) :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧ v.support ≤ p ∧ v.target ≤ q := by
  let ω : Ultrafilter ι := Ultrafilter.of atTop
  obtain ⟨T, _, ht⟩ := exists_weak_operator_ultralimit ω
    (fun i => (a i).val.val) 1 (by norm_num) (fun i => (a i).norm_le_one)
  let b : M.toStarSubalgebra := ⟨T, weak_operator_limit_mem M (fun i => (a i).val) T ht⟩
  have hb : ∀ x y : H, Tendsto (fun i => inner ℂ y ((a i).val.val x)) (ω : Filter ι)
      (𝓝 (inner ℂ y (b.val x))) := ht
  have hbp (i : ι) : b*(a i).support.val=(a i).val := by
    apply wot_limit_unique (fun j => (a j).val*(a i).support.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x)) (ha hj)).symm
  have hab (i : ι) : star (a i).val*b=(a i).support.val := by
    apply wot_limit_unique (fun j => star (a i).val*(a j).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    intro x y
    apply tendsto_const_nhds.congr'
    filter_upwards [(eventually_ge_atTop i).filter_mono (Ultrafilter.of_le atTop)] with j hj
    exact (congrArg (fun z : M.toStarSubalgebra => inner ℂ y (z.val x))
      (cross_initial_rev (ha hj))).symm
  have hba (i : ι) : star b*(a i).val=(a i).support.val := by
    simpa only [star_mul, star_star, (a i).support.property.isSelfAdjoint.star_eq]
      using congrArg star (hab i)
  have hfix (i : ι) : (b*star b)*(a i).val=(a i).val := by
    rw [mul_assoc, hba i, hbp i]
  have hpartial : (b*star b)*b=b := by
    apply wot_limit_unique (fun i => (b*star b)*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [hfix] using hb
  have hid : (star b*b)*(star b*b)=star b*b := by
    calc _ = star b*((b*star b)*b) := by simp only [mul_assoc]
         _ = star b*b := by rw [hpartial]
  let v : PartialIsometry M := ⟨⟨star b*b, ⟨hid, IsSelfAdjoint.star_mul_self b⟩⟩, b, rfl⟩
  refine ⟨v, hbp, ?_, ?_⟩
  · apply (v.support_le_iff_mul p).mpr
    apply wot_limit_unique (fun i => (a i).val*p.val) _ _
      (wot_limit_mul_right _ _ _ hb)
    simpa only [fun i => ((a i).support_le_iff_mul p).mp (hp i)] using hb
  · apply (v.target_le_iff_mul q).mpr
    apply wot_limit_unique (fun i => q.val*(a i).val) _ _
      (wot_limit_mul_left _ _ _ hb)
    simpa only [fun i => ((a i).target_le_iff_mul q).mp (hq i)] using hb

end PartialIsometry
end

/-! Trace-free chain upper bounds and maximal partial isometries, with prescribed
initial and final projection bounds. The index set may be uncountable. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem traceFree_chain_upper_bound (c : Set (PartialIsometry M))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (p q : AlgebraProjection M) (hp : ∀ v ∈ c, v.support ≤ p)
    (hq : ∀ v ∈ c, v.target ≤ q) :
    ∃ v : PartialIsometry M, (∀ w ∈ c, w ≤ v) ∧ v.support ≤ p ∧ v.target ≤ q := by
  let : Nonempty c := hne.to_subtype
  let : IsDirected c (· ≤ ·) := ⟨by
    intro u v
    rcases hc.total u.property v.property with h | h
    · exact ⟨v, h, le_rfl⟩
    · exact ⟨u, le_rfl, h⟩⟩
  obtain ⟨v, hv, hvp, hvq⟩ := traceFree_monotone_upper_bound
    (fun w : c => w.val) (fun _ _ h => h) p q
    (fun w => hp w.val w.property) (fun w => hq w.val w.property)
  exact ⟨v, fun w hw => hv ⟨w,hw⟩, hvp, hvq⟩

theorem traceFree_exists_maximal_between (p q : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support ≤ p ∧ v.target ≤ q ∧
      ∀ w : PartialIsometry M, w.support ≤ p → w.target ≤ q → v ≤ w → w ≤ v := by
  let S : Set (PartialIsometry M) := {v | v.support ≤ p ∧ v.target ≤ q}
  obtain ⟨v,hv⟩ := zorn_le₀ S (by
    intro c hc hchain
    by_cases hne : c.Nonempty
    · obtain ⟨v, hcv, hvp, hvq⟩ := traceFree_chain_upper_bound c hchain hne p q
        (fun w hw => (hc hw).1) (fun w hw => (hc hw).2)
      exact ⟨v, ⟨hvp, hvq⟩, hcv⟩
    · refine ⟨zero, ⟨?_, ?_⟩, ?_⟩
      · change p.val*0=0
        exact mul_zero _
      · apply (zero.target_le_iff_mul q).mpr
        exact mul_zero _
      · intro w hw
        exact (hne ⟨w,hw⟩).elim)
  exact ⟨v,hv.1.1,hv.1.2,fun w hp hq h => hv.2 ⟨hp,hq⟩ h⟩

end PartialIsometry
end

/-! Projection comparison from scalar center, without a supplied trace.
The maximal partial isometry, central support and polar linking are constructed. -/

end Tracial

/-! The original finiteness predicate excludes proper self-equivalence of a
projection. Projection comparison is connected to the unchanged IsII1Factor
predicate, with no representation, trace, or separability premise. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

/-- The identity partial isometry on a projection. -/
def onProjection (p : AlgebraProjection M) : PartialIsometry M :=
  ⟨p, p.val, by rw [p.property.isSelfAdjoint.star_eq, p.property.isIdempotentElem.eq]⟩

theorem onProjection_target (p : AlgebraProjection M) : (onProjection p).target=p := by
  apply Subtype.ext
  change p.val*star p.val=p.val
  rw [p.property.isSelfAdjoint.star_eq, p.property.isIdempotentElem.eq]

/-- A finite algebra has no partial isometry from a projection onto a proper
subprojection of itself. Finiteness is used on v + (1 - p). -/
theorem target_eq_support_of_finite
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (v : PartialIsometry M) (hv : v.target ≤ v.support) : v.target=v.support := by
  let r : AlgebraProjection M := ⟨1-v.support.val,v.support.property.one_sub⟩
  let w := onProjection r
  have hp : v.support.val*w.support.val=0 := by
    change v.support.val*(1-v.support.val)=0
    rw [mul_sub,mul_one,v.support.property.isIdempotentElem.eq,sub_self]
  have hq : v.target.val*w.target.val=0 := by
    rw [show w.target=r from onProjection_target r]
    change v.target.val*(1-v.support.val)=0
    rw [mul_sub,mul_one,projection_mul_of_le hv,sub_self]
  let u := patch v w hp hq
  have hu : star u.val*u.val=1 := by
    rw [u.initial]
    change v.support.val+(1-v.support.val)=1
    abel
  have huf := hfinite u.val hu
  change u.target.val=1 at huf
  rw [patch_target,show w.target=r from onProjection_target r] at huf
  apply Subtype.ext
  change v.target.val+(1-v.support.val)=1 at huf
  have he : v.target.val+(1-v.support.val)=v.support.val+(1-v.support.val) := by
    rw [huf]
    abel
  exact add_right_cancel he

/-- Finiteness also excludes a proper enlargement equivalent to a projection. -/
theorem target_eq_support_of_finite_of_le
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (v : PartialIsometry M) (hv : v.support ≤ v.target) : v.target=v.support := by
  have he : v.adjoint.target=v.support := by
    apply Subtype.ext
    change star v.val*star (star v.val)=v.support.val
    rw [star_star,v.initial]
  have h := target_eq_support_of_finite hfinite v.adjoint (by
    change v.adjoint.target ≤ v.target
    rw [he]
    exact hv)
  change v.adjoint.target=v.target at h
  rw [he] at h
  exact h.symm

end PartialIsometry
end Tracial

end

/-! Arbitrary-chain bounds with moving orthogonal initial and final supports, obtained from successive fixed-multiplier weak operator limits without a trace. -/

/-! Complete actual partial isometries to unitaries in a finite factor.
The construction uses projection comparison and finiteness, without a trace. -/
open scoped CStarAlgebra

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_DyadicComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Halving every projection in a diffuse factor without a trace.
Maximality leaves no residual corner: a diffuse residual splits into two
nonzero orthogonal projections, and a polar link gives a strict extension. -/

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/
section
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

/-- Composition with range contained in the initial projection. -/
def compose (v w : PartialIsometry M) (h : w.target ≤ v.support) : PartialIsometry M where
  support := w.support
  val := v.val*w.val
  initial := by
    calc star (v.val*w.val)*(v.val*w.val) = star w.val*(star v.val*v.val)*w.val := by
           simp only [star_mul,mul_assoc]
         _ = star w.val*w.val := by
           rw [v.initial,mul_assoc,(w.target_le_iff_mul v.support).mp h]
         _ = w.support.val := w.initial

theorem compose_target_le (v w : PartialIsometry M) (h : w.target ≤ v.support) :
    (compose v w h).target ≤ v.target := by
  apply ((compose v w h).target_le_iff_mul v.target).mpr
  change v.target.val*(v.val*w.val)=v.val*w.val
  rw [← mul_assoc,v.target_mul]

end PartialIsometry

end Tracial

/-! Coherent dyadic equivalent partitions and matrix units, constructed from
scalar center and diffuseness without a trace. DyadicIndex is reused as a
finite binary index type; no tracial partition construction is used. -/
open scoped BigOperators

end

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/
namespace Tracial

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem adjoint_target (v : PartialIsometry M) : v.adjoint.target=v.support := by
  apply Subtype.ext
  change star v.val*star (star v.val)=v.support.val
  rw [star_star,v.initial]

end PartialIsometry
namespace AlgebraProjection

def Subequivalent (p q : AlgebraProjection M) : Prop :=
  ∃ v : PartialIsometry M, v.support=p ∧ v.target ≤ q

def Equivalent (p q : AlgebraProjection M) : Prop :=
  ∃ v : PartialIsometry M, v.support=p ∧ v.target=q

theorem equivalent_symm {p q : AlgebraProjection M} (h : p.Equivalent q) : q.Equivalent p := by
  obtain ⟨v,hv,hvq⟩ := h
  exact ⟨v.adjoint,hvq,v.adjoint_target.trans hv⟩

theorem Equivalent.subequivalent {p q : AlgebraProjection M} (h : p.Equivalent q) :
    p.Subequivalent q := by
  obtain ⟨v,hv,hvq⟩ := h
  exact ⟨v,hv,le_of_eq hvq⟩

end AlgebraProjection

/-! Finiteness excludes an infinite family of nonzero equivalent orthogonal
projections. The shift and both of its least supports are constructed. -/

/-! Finite comparison and cancellation with actual partial isometries.
No trace, dimension, or representation is assumed. -/
namespace AlgebraProjection

variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Mutual subequivalence is equivalence in a finite algebra. -/
theorem equivalent_of_mutual_subequivalent {p q : AlgebraProjection M}
    (hpq : p.Subequivalent q) (hqp : q.Subequivalent p) : p.Equivalent q := by
  obtain ⟨v,hv,hvq⟩ := hpq
  obtain ⟨w,hw,hwp⟩ := hqp
  have hc : v.target ≤ w.support := by rw [hw]; exact hvq
  let u := w.compose v hc
  have hu : u.target ≤ u.support := by
    change u.target ≤ v.support
    rw [hv]
    exact (w.compose_target_le v hc).trans hwp
  have he : u.target=p := (u.target_eq_support_of_finite hfinite hu).trans hv
  have hw' : w.target=p := le_antisymm hwp (by
    rw [← he]; exact w.compose_target_le v hc)
  exact ⟨w.adjoint,hw',w.adjoint_target.trans hw⟩

include hfinite in
/-- Equivalent comparable projections in a finite algebra coincide. -/
theorem eq_of_equivalent_of_le {p q : AlgebraProjection M}
    (he : p.Equivalent q) (hle : p ≤ q) : p=q := by
  obtain ⟨v,hv,ht⟩ := he
  exact ht.symm.trans ((v.target_eq_support_of_finite_of_le hfinite (by
    rw [hv,ht]; exact hle)).trans hv) |>.symm

end AlgebraProjection
end Tracial

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_HilbertProjections
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Baire continuity points from rational sublevel boundaries, without a global boundedness assumption. -/

/-! Hilbert-space projection and correlation identities. The inner product is conjugate-linear in its first argument, so `inner ℂ ξ W` represents τ(ξ* W). -/
section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (K : Submodule ℂ E) [K.HasOrthogonalProjection]

def projectionNorm (ξ : E) : ℝ := ‖K.starProjection ξ‖

def residual (z : E) : E := z - K.starProjection z

end

/-! Lower semicontinuity from a continuous family dense in each projected subspace. -/
open Set Filter Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_LongWords
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Factorial coefficient majorization in every homogeneous degree. -/

/-! The nonlinear remainder of the actual ordered convolution-operator
exponentials, evaluated at δ₁, without assumed degree estimates. -/

/-! Signed rows B_k and positive rows A_k with free basis indexed by prefix ratios in FreeGroup Nat. -/

/-! Transfer of the nonlinear estimate to an algebra with a continuous Hilbert
realization and orthonormal reduced-word images, without an independence hypothesis. -/

/-! The exact finite free basis and its injective realization in a countable free basis. -/
section
open scoped BigOperators
open Generator.FreeConvolution
local notation "G" => FreeGroup ℕ

local instance instDecidableEqFreeGroupNat_solutions_3_r398015_1 : DecidableEq G := Classical.decEq _
/-- The manuscript's finite set S, including the identity prefix ratio as a label. -/
def PrefixLabel (n : ℕ) := {p : G // p ∈ ratioLabels n}

end

/-! Exact finite-basis version of the source's nonlinear estimate. Unlike the
ambient transport lemma, only reduced words in F_S occur in the hypothesis. -/
open scoped BigOperators InnerProductSpace

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixEncoding
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Generator.MatrixEncoding

/-! Algebraic encoding of four corner operators by two self-adjoint matrices. -/
section
variable {R : Type*} [Ring R] [StarRing R]
local notation "Mat" => Matrix (Fin 2) (Fin 2) R

def E11 : Mat := !![1, 0; 0, 0]
def E12 : Mat := !![0, 1; 0, 0]
def E21 : Mat := !![0, 0; 1, 0]
def E22 : Mat := !![0, 0; 0, 1]
def corner (a : R) : Mat := !![a, 0; 0, 0]
def encodeA (a₁ a₂ C : R) : Mat := !![a₁, 0; 0, a₂ + C]
def encodeB (a₃ a₄ : R) : Mat := !![a₃, 1; 1, a₄]

end

/-! Algebraic diagonal identities used by the analytic gap recovery. -/

end Generator.MatrixEncoding

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_Pinching
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

/-- The partition with its corner as its only piece. -/
def single (p : AlgebraProjection M) : CornerPartition p where
  size := 1
  piece _ := p
  orthogonal i j hij := (hij (Subsingleton.elim _ _)).elim
  total := by simp

@[simp] theorem single_pinch (p : AlgebraProjection M) (x : M.toStarSubalgebra) :
    (single p).pinch x = p.val*x*p.val := by
  change (∑ _ : Fin 1, p.val*x*p.val) = _
  simp

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
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/

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

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_SpectralTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Positivity of the tracial pairing does not require the two positive
operators to commute. These estimates will control spectral truncation. -/
section
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance tracePairingCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance tracePairingOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance tracePairingPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance tracePairingLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance tracePairingStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/
section
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance truncationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance truncationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance truncationLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance truncationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

def upperTruncate (a : M.toStarSubalgebra) (C : ℝ) : M.toStarSubalgebra :=
  a-(a-algebraMap ℝ M.toStarSubalgebra C)⁺

theorem upperTruncate_cfc (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    upperTruncate a C = cfc (fun t : ℝ => min t C) a := by
  have hf : (fun t : ℝ => min t C) = fun t => t-(t-C)⁺ := by
    funext t
    simp only [_root_.posPart_def]
    by_cases h : t ≤ C
    · rw [min_eq_left h,max_eq_right (sub_nonpos.mpr h),sub_zero]
    · rw [min_eq_right (le_of_not_ge h),max_eq_left (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  rw [hf,cfc_sub (fun t : ℝ => t) (fun t => (t-C)⁺) a,cfc_id' ℝ a]
  unfold upperTruncate
  congr 1
  rw [CFC.posPart_def,cfcₙ_eq_cfc]
  have hs : cfc (fun t : ℝ => t-C) a = a-algebraMap ℝ M.toStarSubalgebra C := by
    rw [cfc_sub (fun t : ℝ => t) (fun _ => C) a,cfc_id' ℝ a,cfc_const C a ha]
  rw [← hs,← cfc_comp (fun t : ℝ => t⁺) (fun t => t-C) a]
  rfl

theorem upperTruncate_selfAdjoint (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    IsSelfAdjoint (upperTruncate a C) :=
  ha.sub (CFC.posPart_nonneg _).isSelfAdjoint

theorem upperTruncate_norm_le (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a)
    (C R : ℝ) (hC : 0 ≤ C) (hR : ‖a‖ ≤ R) : ‖upperTruncate a C‖ ≤ R := by
  obtain (hH | hH) := subsingleton_or_nontrivial H
  · have ha0 : a=0 := Subtype.ext (Subsingleton.elim _ _)
    have hz : upperTruncate a C=0 := Subtype.ext (Subsingleton.elim _ _)
    simpa only [hz,norm_zero] using (norm_nonneg a).trans hR
  rw [upperTruncate_cfc a ha C]
  apply norm_cfc_le ((norm_nonneg a).trans hR)
  intro t ht
  have htR := (spectrum.norm_le_norm_of_mem ht).trans hR
  rw [Real.norm_eq_abs,abs_le] at htR ⊢
  exact ⟨le_min htR.1 (by linarith), (min_le_left _ _).trans htR.2⟩

theorem upperTruncate_discard_mul (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (C : ℝ) :
    (a-algebraMap ℝ M.toStarSubalgebra C)⁺ * upperTruncate a C =
      C • (a-algebraMap ℝ M.toStarSubalgebra C)⁺ := by
  let b := a-algebraMap ℝ M.toStarSubalgebra C
  have hb : IsSelfAdjoint b := ha.sub (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all C))
  have he : upperTruncate a C = algebraMap ℝ M.toStarSubalgebra C-b⁻ := by
    have hh := CFC.posPart_sub_negPart b hb
    have heq : a=b+algebraMap ℝ M.toStarSubalgebra C := by dsimp [b]; abel
    change a-b⁺=algebraMap ℝ M.toStarSubalgebra C-b⁻
    nth_rw 1 [heq]
    nth_rw 1 [← hh]
    abel
  rw [he,mul_sub,CFC.posPart_mul_negPart,sub_zero,
    Algebra.algebraMap_eq_smul_one,mul_smul_comm,mul_one]

end

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/
section
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
local instance interiorCStar (A : VonNeumannAlgebra H) : CStarAlgebra A.toStarSubalgebra := {}
local instance interiorOrder (A : VonNeumannAlgebra H) : PartialOrder A.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance interiorPreorder (A : VonNeumannAlgebra H) : Preorder A.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance interiorLE (A : VonNeumannAlgebra H) : LE A.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toLE
local instance interiorStarOrder (A : VonNeumannAlgebra H) : StarOrderedRing A.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem selfAdjoint_norm_le_of_bounds (a : M.toStarSubalgebra) (ha : IsSelfAdjoint a)
    (C : ℝ) (hC : 0 ≤ C) (hu : a ≤ algebraMap ℝ M.toStarSubalgebra C)
    (hl : -a ≤ algebraMap ℝ M.toStarSubalgebra C) : ‖a‖ ≤ C := by
  obtain (hA | hA) := subsingleton_or_nontrivial M.toStarSubalgebra
  · simpa only [Subsingleton.elim a 0,norm_zero] using hC
  have hpos : ∀ t ∈ spectrum ℝ a,t ≤ C := by
    apply (cfc_le_iff (fun t : ℝ => t) (fun _ => C) a).mp
    rw [cfc_id' ℝ a ha,cfc_const C a ha]
    exact hu
  have hneg : ∀ t ∈ spectrum ℝ a,-t ≤ C := by
    apply (cfc_le_iff (fun t : ℝ => -t) (fun _ => C) a).mp
    rw [cfc_neg (fun t : ℝ => t) a,cfc_id' ℝ a ha,cfc_const C a ha]
    exact hl
  rcases CStarAlgebra.norm_or_neg_norm_mem_spectrum ha with h | h
  · exact hpos _ h
  · simpa using hneg _ h

end

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_MatrixGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Diagonal projections and one full-support rank-one projection generate
every finite full matrix algebra, including matrices larger than size two. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def fullProjectionMatrix : Matrix ι ι ℂ := fun _ _ => (Fintype.card ι : ℂ)⁻¹

end MatrixUnitSystem

/-! Two actual self-adjoint generators for the weak closure of countably
many pairwise commuting finite full matrix factors. -/

/-! The retained tensor extensions supply commuting factors generating
exactly the original matrix-union weak closure. -/

/-! The represented irreducible matrix subfactor can be constructed together
with two self-adjoint generators, without hyperfinite uniqueness. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_NormalDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Increasing projection suprema and compatible sequential comparison.
The witnesses live in the original algebra; no trace or dimension is used. -/

/-! Original-factor wrapper for normalized faithful order-continuous projection
dimension. This does not assert the existence of a linear trace functional. -/

/-! Exact prescribed dimensions are attained by actual subprojections.
Chain bounds use the proved arbitrary-net continuity of dimension. -/

/-! Actual vector functionals and their continuity on directed projection
suprema. No factor, trace, separability, or dimension hypothesis is used. -/
open Filter
open scoped Topology BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace AlgebraProjection

/-- The original Hilbert-space vector functional on actual projections. -/
def vectorValue (ξ : H) (p : AlgebraProjection M) : ℝ :=
  (inner ℂ ξ (p.val.val ξ)).re

end AlgebraProjection
end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ11_FG.FactorGeneration_RelativeGeneration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite star polynomials in one unitary variable and coefficients in
an included von Neumann algebra. Both uniform operator bounds and continuity
of trace-vector evaluation are proved by recursion on the expression. -/
open Filter
open scoped Topology

inductive RelativePolynomial (A : Type*) where
  | coeff : A → RelativePolynomial A
  | indeterminate : RelativePolynomial A
  | add : RelativePolynomial A → RelativePolynomial A → RelativePolynomial A
  | mul : RelativePolynomial A → RelativePolynomial A → RelativePolynomial A
  | smul : ℂ → RelativePolynomial A → RelativePolynomial A
  | adjoint : RelativePolynomial A → RelativePolynomial A

/-! The literal algebra W*(N,u), its trace Hilbert subspace, and density of
actual N-coefficient star-polynomial values in that subspace. -/
open Filter
open scoped Topology

/-! The literal interleaved word belongs to W*(N,u), is unitary, and has
trace norm one. The printed perturbation-size bound tends to zero. -/
open Filter
open scoped Topology

/-! Projection continuity for generated algebras, using the complete trace-unitary metric, dense polynomial sections, and trace-vector separability. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end


