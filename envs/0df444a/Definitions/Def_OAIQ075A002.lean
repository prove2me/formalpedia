-- Prove2me | Definitions.Def_OAIQ075A002
-- name    : OAIQ075A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T07:54:11.638471+00:00
-- url     : https://prove2.me/theorems/bb9f487b-9cee-4d8d-b4ae-ab0e7b845730
-- title:
--   Definitions bundle OAIQ075A002 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 40 definitions, 3 inductive types or structures, 3 instances and 50 theorems. The definitions and types are `OAI.BoundedHochschild.KadisonRingrose.flipMatrixNesting`, `OAI.BoundedHochschild.KadisonRingrose.matrixFunctionalEmbedding`, `OAI.BoundedHochschild.KadisonRingrose.matrixFunctionalVector`, `OAI.BoundedHochschild.KadisonRingrose.matrixScalarHom`, `OAI.BoundedHochschild.KadisonRingrose.operatorSystemAmplification`, `OAI.BoundedHochschild.KadisonRingrose.operatorSystemMatrices`, `OAI.BoundedHochschild.KadisonRingrose.operatorSystemRealFunctional`, `OAI.BoundedHochschild.KadisonRingrose.operatorSystemRealInclusion`, `OAI.BoundedHochschild.KadisonRingrose.operatorSystemRealPart`, `OAI.BoundedHochschild.KadisonRingrose.operatorSystemSingle`, `OAI.BoundedHochschild.KadisonRingrose.scalarMatrixHom`, `OAI.BoundedHochschild.KadisonRingrose.singleCStarMatrix`, `OAI.BoundedHochschild.KadisonRingrose.starConjugateLinear`, `OAI.BoundedHochschild.KadisonRingrose.stinespringLeftLabel`, `OAI.FreeGroupFactorMain.GroupHilbert`, `OAI.FreeGroupFactorMain.GroupOperator`, `OAI.FreeGroupFactorMain.hilbertReindex`, `OAI.FreeGroupFactorMain.leftRegular`, `OAI.FreeGroupFactorMain.ultraweakOperatorTopology`, `OAI.Generator.FiniteHilbert`, `OAI.Generator.FiniteMatrixStage`, `OAI.Generator.MatrixUnitSystem`, `OAI.Generator.MatrixUnitSystem.commutant`, `OAI.Generator.MatrixUnitSystem.hom`, `OAI.Generator.MatrixUnitSystem.linearMap`, `OAI.Generator.MatrixUnitSystem.map`, `OAI.HochschildFinitePhase.OffDiagonal`, `OAI.NaimarkZFC.gnsVector`, `OAI.UltrapowerBridge.Bounded`, `OAI.UltrapowerBridge.Ell2`, `OAI.UltrapowerBridge.TraceRel`, `OAI.UltrapowerBridge.TracialQuotient`, `OAI.UltrapowerBridge.TracialRepresentation`, `OAI.UltrapowerBridge.TracialRepresentation.Algebra`, `OAI.UltrapowerBridge.TracialRepresentation.norm₂`, `OAI.UltrapowerBridge.TracialRepresentation.trace`, `OAI.UltrapowerBridge.boundedSequences`, `OAI.UltrapowerBridge.leftRegular`, `OAI.UltrapowerBridge.quotientMap`, `OAI.UltrapowerBridge.reindex` and 3 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_FinitePhases`, `BoundedHochschild_FinitePositiveExtension`, `BoundedHochschild_FlipMatrixNesting`, `BoundedHochschild_MatrixFunctionalDilation`, `BoundedHochschild_MatrixScalarColumns`, `BoundedHochschild_MaximalInfiniteProjection`, `BoundedHochschild_NormalModulus`, `BoundedHochschild_OperatorSystemFunctionals`, `BoundedHochschild_OperatorSystemMatrices`, `BoundedHochschild_PaulsenSystem`, `BoundedHochschild_ProperlyInfiniteColumns`, `BoundedHochschild_ScalarMatrixActions`, `BoundedHochschild_StinespringLeftAction`, `BoundedHochschild_WeakAlgebras`, `FactorGeneration_Bicommutant`, `FactorGeneration_GroupTrace`, `FactorGeneration_MatrixSequence`, `FactorGeneration_MatrixUnits`, `FactorGeneration_Ultrapower`, `FreeGroupFactor_Model`, `FreeGroupFactor_Operators`, `Naimark_Basic`, `TracialCohomology_CornerComparison`, `TracialCohomology_TypeII`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A008`, `OAIQ075A009`, `OAIQ075A010` and `OAIQ075A012`.
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

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
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

abbrev OffDiagonal (I : Type*) := {p : I × I // p.1 ≠ p.2}

end HochschildFinitePhase
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalModulus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal cochains, bounded-ball continuity and primitive construction. -/

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
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma preGNS_sq_le_trace (a : M) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖τ.toPreGNS a‖^2 ≤ (τ a).re := by
  have hs := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS a))
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS,
    (IsSelfAdjoint.of_nonneg ha).star_eq,← Complex.ofReal_pow,Complex.ofReal_re] at hs
  rw [hs]
  apply Complex.re_le_re
  apply τ.monotone
  simpa only [pow_two,pow_one] using CStarAlgebra.pow_antitone (ha₀ := ha) (ha₁ := ha1) (show 1 ≤ 2 by omega)

lemma monotone_contractions_preGNS_cauchy (a : ℕ → M) (h0 : ∀ n, 0 ≤ a n)
    (h1 : ∀ n, a n ≤ 1) (hm : Monotone a) : CauchySeq (fun n => τ.toPreGNS (a n)) := by
  have hmono : Monotone (fun n => (τ (a n)).re) := fun n m hnm =>
    Complex.re_le_re (τ.monotone (hm hnm))
  have hbdd : BddAbove (Set.range (fun n => (τ (a n)).re)) :=
    ⟨(τ 1).re,fun _ ⟨n,hn⟩ => hn ▸ Complex.re_le_re (τ.monotone (h1 n))⟩
  have hc := (tendsto_atTop_ciSup hmono hbdd).cauchySeq
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp hc (ε^2) (sq_pos_of_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have hd0 : 0 ≤ a n-a N := sub_nonneg.mpr (hm hn)
  have hd1 : a n-a N ≤ 1 := (sub_le_self _ (h0 N)).trans (h1 n)
  have hsq := preGNS_sq_le_trace τ (a n-a N) hd0 hd1
  have hdiff := hN n hn
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hmono hn))] at hdiff
  simp only [map_sub,Complex.sub_re] at hsq
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (τ.toPreGNS (a n)-τ.toPreGNS (a N))]

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder



open Filter Topology
open scoped ComplexOrder



open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_WeakAlgebras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weak-star algebra closures, inherited traces and generated finite-path primitives. -/

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
open Filter Topology



open Filter Topology
open scoped ComplexOrder



open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
namespace WeakAlgebra
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
 

instance closedSubalgebra_starOrderedRing (B : StarSubalgebra ℂ M)
    [IsClosed (B : Set M)] [StarOrderedRing M] : StarOrderedRing B := by
  apply StarOrderedRing.of_nonneg_iff'
  · intro x y h z
    change (z:M)+(x:M) ≤ (z:M)+(y:M)
    simpa only [add_comm] using add_le_add_left (show (x:M) ≤ (y:M) from h) (z:M)
  · intro a
    constructor
    · intro ha
      have hmem : CFC.sqrt (a:M) ∈ B := by
        rw [CFC.sqrt_eq_real_sqrt (a:M) (show 0 ≤ (a:M) from ha)]
        exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt a.property
      refine ⟨⟨CFC.sqrt (a:M),hmem⟩,Subtype.ext ?_⟩
      change (a:M)=star (CFC.sqrt (a:M))*CFC.sqrt (a:M)
      rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (a:M))).star_eq]
      exact (CFC.sqrt_mul_sqrt_self (a:M) ha).symm
    · rintro ⟨b,rfl⟩
      exact star_mul_self_nonneg (b:M)

end WeakAlgebra
end BoundedHochschild
 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_CornerComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner comparison for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder
namespace PopaCorners
open BoundedHochschild
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace CornerIso
variable {p q : M}

lemma projection_mul_zero_of_le_sub {p r t : M} (hp : IsStarProjection p)
    (hr : IsStarProjection r) (ht : IsStarProjection t) (hrp : r ≤ p) (htr : t ≤ p-r) :
    r*t=0 := by
  have hpr : IsStarProjection (p-r) := (hr.le_iff_sub hp).mp hrp
  have hh := (ht.le_iff_mul_eq_right hpr).mp htr
  calc
    r*t = r*((p-r)*t) := by rw [hh]
    _ = (r*p-r*r)*t := by noncomm_ring
    _ = 0 := by rw [(hr.le_iff_mul_eq_left hp).mp hrp,hr.isIdempotentElem.eq,
      sub_self,zero_mul]

end CornerIso
end PopaCorners

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_TypeII
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Type ii for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [PartialOrder M] [StarOrderedRing M] in
lemma off_diagonal_nonzero {q a : M} (hq : IsStarProjection q) (hqa : ¬ Commute q a) :
    (1-q)*a*q ≠ 0 ∨ (1-q)*star a*q ≠ 0 := by
  by_contra h
  push Not at h
  have hstar := congrArg star h.2
  simp only [star_mul,star_sub,star_one,star_star,hq.isSelfAdjoint.star_eq,star_zero] at hstar
  have hright : a*q=q*a*q := by
    have hh := h.1
    rw [sub_mul,one_mul,sub_mul,sub_eq_zero] at hh
    exact hh
  have hleft : q*a=q*a*q := by
    simpa only [mul_sub,mul_one,sub_eq_zero,mul_assoc] using hstar
  exact hqa (show q*a=a*q from hleft.trans hright.symm)

end PopaTypeII

open Filter Topology
open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProperlyInfiniteColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Properly infinite projections from orthogonal columns

Countably many equivalent orthogonal projections split into even and odd
columns. The resulting operators are actual partial isometries in the algebra.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma projection_le_complement_of_mul_zero {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) : p ≤ 1 - q := by
  apply (hp.le_iff_mul_eq_left hq.one_sub).mpr
  rw [mul_sub, mul_one, hpq, sub_zero]

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MaximalInfiniteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A maximal properly infinite projection has finite complement. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma projection_mul_zero_of_bounds {p q r s : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hr : IsStarProjection r) (hs : IsStarProjection s)
    (hpq : p * q = 0) (hrp : r ≤ p) (hsq : s ≤ q) : r * s = 0 := by
  calc
    r * s = (r * p) * (q * s) := by
      rw [(hr.le_iff_mul_eq_left hp).mp hrp, (hs.le_iff_mul_eq_right hq).mp hsq]
    _ = r * (p * q) * s := by simp only [mul_assoc]
    _ = 0 := by rw [hpq, mul_zero, zero_mul]

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixScalarColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Diagonal copies of the proved isometry columns inside finite matrix
algebras. These supply the row estimates at every matrix level. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M : Type*} [CStarAlgebra M]

/-- The unital diagonal embedding into a finite matrix algebra. -/
def matrixScalarHom (k : ℕ) : M →⋆ₐ[ℂ] CStarMatrix (Fin k) (Fin k) M where
  toFun a := CStarMatrix.ofMatrix (Matrix.scalar (Fin k) a)
  map_zero' := (Matrix.scalar (Fin k)).map_zero
  map_one' := (Matrix.scalar (Fin k)).map_one
  map_add' a b := (Matrix.scalar (Fin k)).map_add a b
  map_mul' a b := (Matrix.scalar (Fin k)).map_mul a b
  commutes' _ := rfl
  map_star' a := by
    ext i j
    change (if i = j then star a else 0) = star (if j = i then a else 0)
    by_cases h : i = j
    · simp only [h, ite_true]
    · simp only [h, Ne.symm h, ite_false, star_zero]

@[simp] lemma matrixScalarHom_apply (k : ℕ) (a : M) (i j : Fin k) :
    matrixScalarHom k a i j = if i = j then a else 0 := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.Naimark_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def gnsVector (f : A →ₚ[ℂ] ℂ) : f.GNS := (f.toPreGNS 1 : f.GNS)

@[simp] theorem gns_apply_vector (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a (gnsVector f) = (f.toPreGNS a : f.GNS) := by
  simp [gnsVector]

@[simp] theorem gnsVector_coefficient (f : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪gnsVector f, f.gnsStarAlgHom a (gnsVector f)⟫_ℂ = f a := by
  simp [gnsVector, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]

@[simp] theorem gnsVector_norm_sq (f : A →ₚ[ℂ] ℂ) :
    ‖gnsVector f‖ ^ 2 = (f 1).re := by
  simp only [gnsVector, Completion.norm_coe,
    PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    star_one, one_mul]
  exact Real.sq_sqrt (f.map_nonneg (show (0 : A) ≤ 1 from zero_le_one)).1

end GNS

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixFunctionalDilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive functional on a matrix algebra gives a completely positive
map into the corresponding finite-dimensional operator algebra. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def singleCStarMatrix {n : ℕ} (i j : Fin n) (a : A) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

def matrixFunctionalVector {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ)
    (i₀ i : Fin n) : F.GNS :=
  F.gnsStarAlgHom (singleCStarMatrix i₀ i 1) (NaimarkZFC.gnsVector F)

def matrixFunctionalEmbedding {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ)
    (i₀ : Fin n) : EuclideanSpace ℂ (Fin n) →L[ℂ] F.GNS :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ => ∑ i, ξ i • matrixFunctionalVector F i₀ i
      map_add' := fun ξ η => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun z ξ => by simp [Finset.smul_sum, mul_smul] }

@[simp] lemma matrixFunctionalEmbedding_single {n : ℕ}
    (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ) (i₀ i : Fin n) :
    matrixFunctionalEmbedding F i₀ (EuclideanSpace.single i 1) =
      matrixFunctionalVector F i₀ i := by
  change (∑ j, (EuclideanSpace.single i (1 : ℂ)) j • matrixFunctionalVector F i₀ j) = _
  simp [PiLp.single_apply]

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_OperatorSystemFunctionals
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive scalar functionals on unital self-adjoint linear subspaces.
The extension uses real Hahn–Banach on the self-adjoint part. -/

noncomputable section

open scoped ComplexOrder ComplexStarModule

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def operatorSystemRealPart (S : Submodule ℂ A) : Submodule ℝ A :=
  S.restrictScalars ℝ ⊓ selfAdjoint.submodule ℝ A

def operatorSystemRealInclusion (S : Submodule ℂ A) :
    operatorSystemRealPart S →ₗ[ℝ] S where
  toFun x := ⟨x.val, x.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma positive_subspace_real_bound (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (f : S →ₗ[ℂ] ℂ) (hf : ∀ a : S, 0 ≤ (a : A) → 0 ≤ f a)
    (a : S) (ha : IsSelfAdjoint (a : A)) :
    |(f a).re| ≤ (f ⟨1, h1⟩).re * ‖a‖ := by
  let e : S := ⟨1, h1⟩
  have hup : 0 ≤ ‖a‖ • (1 : A) - (a : A) := by
    apply sub_nonneg.mpr
    change (a : A) ≤ ‖(a : A)‖ • (1 : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using ha.le_algebraMap_norm_self
  have hlo : 0 ≤ ‖a‖ • (1 : A) + (a : A) := by
    change 0 ≤ ‖(a : A)‖ • (1 : A) + (a : A)
    simpa only [Algebra.algebraMap_eq_smul_one, neg_le_iff_add_nonneg, add_comm]
      using ha.neg_algebraMap_norm_le_self
  have hp := (hf ((‖a‖ : ℂ) • e - a) (by
    change 0 ≤ (‖a‖ : ℂ) • (1 : A) - (a : A)
    rw [Complex.coe_smul]
    exact hup)).1
  have hm := (hf ((‖a‖ : ℂ) • e + a) (by
    change 0 ≤ (‖a‖ : ℂ) • (1 : A) + (a : A)
    rw [Complex.coe_smul]
    exact hlo)).1
  simp only [map_sub, map_add, map_smul, smul_eq_mul, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.zero_re] at hp hm
  change 0 ≤ ‖a‖ * (f ⟨1, h1⟩).re - (f a).re at hp
  change 0 ≤ ‖a‖ * (f ⟨1, h1⟩).re + (f a).re at hm
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

def operatorSystemRealFunctional (S : Submodule ℂ A) (h1 : (1 : A) ∈ S)
    (f : S →ₗ[ℂ] ℂ) (hf : ∀ a : S, 0 ≤ (a : A) → 0 ≤ f a) :
    operatorSystemRealPart S →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    (Complex.reLm.comp ((f.restrictScalars ℝ).comp (operatorSystemRealInclusion S)))
    (f ⟨1, h1⟩).re (fun a =>
      positive_subspace_real_bound S h1 f hf (operatorSystemRealInclusion S a) a.property.2)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_OperatorSystemMatrices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar matrix functional used in finite-dimensional positive extension. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def operatorSystemMatrices (S : Submodule ℂ A) (n : ℕ) :
    Submodule ℂ (CStarMatrix (Fin n) (Fin n) A) where
  carrier := {X | ∀ i j, X i j ∈ S}
  zero_mem' := fun _ _ => S.zero_mem
  add_mem' hX hY := fun i j => S.add_mem (hX i j) (hY i j)
  smul_mem' z _X hX := fun i j => S.smul_mem z (hX i j)

def operatorSystemAmplification {B : Type*} [CStarAlgebra B]
    (S : Submodule ℂ A) (φ : S →ₗ[ℂ] B) (n : ℕ) :
    operatorSystemMatrices S n →ₗ[ℂ] CStarMatrix (Fin n) (Fin n) B where
  toFun X := CStarMatrix.ofMatrix (fun i j => φ ⟨X.val i j, X.property i j⟩)
  map_add' X Y := by
    apply CStarMatrix.ext
    intro i j
    exact map_add φ ⟨X.val i j, X.property i j⟩ ⟨Y.val i j, Y.property i j⟩
  map_smul' z X := by
    apply CStarMatrix.ext
    intro i j
    exact map_smul φ z ⟨X.val i j, X.property i j⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FinitePositiveExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional operator-valued positive extension theorem.
Only positivity at the target matrix size is needed. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def operatorSystemSingle (S : Submodule ℂ A) {n : ℕ} (i j : Fin n) (a : S) :
    operatorSystemMatrices S n :=
  ⟨singleCStarMatrix i j (a : A), fun p q => by
    change (if i = p ∧ j = q then (a : A) else 0) ∈ S
    split_ifs
    · exact a.property
    · exact S.zero_mem⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ScalarMatrixActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Entrywise scalar matrices and their action on matrix amplifications. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def scalarMatrixHom (A : Type*) [CStarAlgebra A] (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A where
  toFun Q := Q.map (algebraMap ℂ A)
  map_zero' := by ext i j; exact map_zero (algebraMap ℂ A)
  map_add' Q R := by ext i j; exact map_add (algebraMap ℂ A) (Q i j) (R i j)
  map_one' := by
    ext i j
    change algebraMap ℂ A (if i = j then 1 else 0) = if i = j then 1 else 0
    split_ifs <;> simp
  map_mul' Q R := by
    ext i j
    change algebraMap ℂ A (∑ k, Q i k * R k j) =
      ∑ k, algebraMap ℂ A (Q i k) * algebraMap ℂ A (R k j)
    simp
  commutes' z := by
    ext i j
    change algebraMap ℂ A (if i = j then z else 0) =
      if i = j then algebraMap ℂ A z else 0
    split_ifs <;> simp
  map_star' Q := by
    ext i j
    exact map_star (StarAlgHom.ofId ℂ A) (Q j i)

@[simp] lemma scalarMatrixHom_apply (n : ℕ)
    (Q : CStarMatrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    scalarMatrixHom A n Q i j = algebraMap ℂ A (Q i j) := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FlipMatrixNesting
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exchange the finite matrix indices in a two-by-two amplification. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A]

def flipMatrixNesting (n k : ℕ) :
    CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin k) (Fin k) A) ≃⋆ₐ[ℂ]
      CStarMatrix (Fin k) (Fin k) (CStarMatrix (Fin n) (Fin n) A) where
  toFun X i j p q := X p q i j
  invFun X i j p q := X p q i j
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl
  map_mul' X Y := by
    ext i j p q
    change (∑ s : Fin n, (fun r t => ∑ l : Fin k, X p s r l * Y s q l t)) i j =
      (∑ l : Fin k, (fun r t => ∑ s : Fin n, X r s i l * Y s t l j)) p q
    simp only [Finset.sum_apply]
    exact Finset.sum_comm

@[simp] lemma flipMatrixNesting_apply (n k : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin k) (Fin k) A))
    (i j : Fin k) (p q : Fin n) : flipMatrixNesting n k X i j p q = X p q i j := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PaulsenSystem
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unital two-by-two operator system associated to a linear map. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def starConjugateLinear (T : A →ₗ[ℂ] B) : A →ₗ[ℂ] B where
  toFun a := star (T (star a))
  map_add' a b := by simp
  map_smul' z a := by simp

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_StinespringLeftAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Left multiplication on the auxiliary positive-kernel Hilbert space. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def stinespringLeftLabel (b : M) (p : M × H) : M × H := (b * p.1, p.2)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Bicommutant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
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

abbrev FiniteHilbert (ι : Type*) (H : Type*) := PiLp 2 (fun _ : ι => H)

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
-- module Solutions.OAIQ075_KS.FreeGroupFactor_Model
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u uG

open scoped ENNReal

abbrev GroupHilbert (G : Type u) := lp (fun _ : G => ℂ) 2
abbrev GroupOperator (G : Type u) := GroupHilbert G →L[ℂ] GroupHilbert G

@[instance_reducible] def ultraweakOperatorTopology (G : Type u) : TopologicalSpace (GroupOperator G) :=
  ⨅ (ξ : lp (fun _ : ℕ => GroupHilbert G) 2)
    (η : lp (fun _ : ℕ => GroupHilbert G) 2),
    TopologicalSpace.induced
      (fun T : GroupOperator G => ∑' k : ℕ, inner ℂ (η k) (T (ξ k)))
      inferInstance

end FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_42 u_43

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FreeGroupFactor_Operators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain

open scoped ENNReal

def hilbertReindex {G : Type uG} {H : Type uH} (e : G ≃ H) :
    GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H where
  toFun ξ := ⟨fun h => ξ (e.symm h), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp ξ).summable (by norm_num))⟩
  invFun η := ⟨fun g => η (e g), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp η).summable (by norm_num))⟩
  left_inv ξ := by ext g; simp
  right_inv η := by ext h; simp
  map_add' ξ η := by rfl
  map_smul' c ξ := by rfl
  norm_map' ξ := by
    simp only [lp.norm_eq_tsum_rpow (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    change (∑' h : H, ‖ξ (e.symm h)‖ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal) =
      (∑' g : G, ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal) ^ (1 / (2 : ℝ≥0∞).toReal)
    exact congrArg (fun t : ℝ => t ^ (1 / (2 : ℝ≥0∞).toReal))
      (e.symm.tsum_eq (fun g => ‖ξ g‖ ^ (2 : ℝ≥0∞).toReal))

@[simp] theorem hilbertReindex_apply {G : Type uG} {H : Type uH} (e : G ≃ H)
    (ξ : GroupHilbert G) (h : H) : hilbertReindex e ξ h = ξ (e.symm h) := rfl

def leftRegular {G : Type uG} [Group G] (g : G) : GroupOperator G :=
  (hilbertReindex (Equiv.mulLeft g)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem leftRegular_apply {G : Type uG} [Group G] (g : G)
    (ξ : GroupHilbert G) (h : G) : leftRegular g ξ h = ξ (g⁻¹ * h) := rfl

@[simp] theorem leftRegular_one {G : Type uG} [Group G] :
    leftRegular (1 : G) = 1 := by
  ext ξ h
  simp

@[simp] theorem leftRegular_mul {G : Type uG} [Group G] (g h : G) :
    leftRegular (g * h) = leftRegular g * leftRegular h := by
  ext ξ b
  simp [mul_assoc]

@[simp] theorem leftRegular_star {G : Type uG} [Group G] (g : G) :
    star (leftRegular g) = leftRegular g⁻¹ := by
  change star ((hilbertReindex (Equiv.mulLeft g)) : GroupOperator G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext ξ b
  change ξ (g * b) = ξ ((g⁻¹)⁻¹ * b)
  simp

end FreeGroupFactorMain

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_GroupTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open scoped ENNReal Pointwise
abbrev Ell2 (G : Type*) := FreeGroupFactorMain.GroupHilbert G
local instance groupAlgebraDecEq_r7baa28_1 (G : Type*) : DecidableEq G := Classical.decEq _
/-- Reindex a square-summable vector by a permutation. -/
abbrev reindexVector {G : Type*} (e : G ≃ G) (f : Ell2 G) : Ell2 G :=
  FreeGroupFactorMain.hilbertReindex e f

@[simp] theorem reindexVector_apply {G : Type*} (e : G ≃ G) (f : Ell2 G) (g : G) :
    reindexVector e f g = f (e.symm g) := rfl

/-- The bounded unitary implementation of a permutation on ell2. -/
abbrev reindex {G : Type*} (e : G ≃ G) : Ell2 G ≃ₗᵢ[ℂ] Ell2 G :=
  FreeGroupFactorMain.hilbertReindex e

/-- The left regular operator, constructed on every square-summable vector. -/
abbrev leftRegular {G : Type*} [Group G] (g : G) : Ell2 G →L[ℂ] Ell2 G :=
  FreeGroupFactorMain.leftRegular g

@[simp] theorem leftRegular_apply {G : Type*} [Group G] (g b : G) (f : Ell2 G) :
    leftRegular g f b = f (g⁻¹ * b) := rfl

variable (G : Type*) [Group G]

variable {G}
@[simp] theorem leftRegular_star {G : Type*} [Group G] (g : G) :
    star (leftRegular g) = leftRegular g⁻¹ := by
  change star ((reindex (Equiv.mulLeft g)) : Ell2 G →L[ℂ] Ell2 G) = _
  rw [LinearIsometryEquiv.star_eq_symm]
  ext f b
  change f (g * b) = f ((g⁻¹)⁻¹ * b)
  simp

/-- Right translations, needed to prove that the identity vector is separating. -/
def rightRegular {G : Type*} [Group G] (g : G) : Ell2 G →L[ℂ] Ell2 G :=
  (reindex (Equiv.mulRight g)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem rightRegular_apply {G : Type*} [Group G] (g b : G) (f : Ell2 G) :
    rightRegular g f b = f (b * g⁻¹) := rfl

end

section
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete finite tracial von Neumann algebra in a faithful vector-trace
representation. These are operator-algebra data, without approximation assumptions. -/
structure TracialRepresentation (M : VonNeumannAlgebra H) where
  vector : H
  norm_vector : ‖vector‖ = 1
  cyclic : ∀ S T : M.toStarSubalgebra,
    inner ℂ vector ((S : H →L[ℂ] H) ((T : H →L[ℂ] H) vector)) =
    inner ℂ vector ((T : H →L[ℂ] H) ((S : H →L[ℂ] H) vector))
  separating : ∀ T : M.toStarSubalgebra, (T : H →L[ℂ] H) vector = 0 → T = 0

namespace TracialRepresentation
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
abbrev Algebra := M.toStarSubalgebra

def trace (T : Algebra (M := M)) : ℂ := inner ℂ τ.vector ((T : H →L[ℂ] H) τ.vector)
def norm₂ (T : Algebra (M := M)) : ℝ := ‖(T : H →L[ℂ] H) τ.vector‖

@[simp] theorem trace_one : τ.trace 1 = 1 := by
  simp [trace, inner_self_eq_norm_sq_to_K, τ.norm_vector]

theorem trace_mul_comm (S T : Algebra (M := M)) : τ.trace (S*T) = τ.trace (T*S) :=
  τ.cyclic S T

theorem trace_star_mul (T : Algebra (M := M)) :
    τ.trace (star T*T) = (τ.norm₂ T : ℂ)^2 := by
  unfold trace norm₂
  change inner ℂ τ.vector ((star (T : H →L[ℂ] H)) ((T : H →L[ℂ] H) τ.vector)) = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem norm₂_star (T : Algebra (M := M)) : τ.norm₂ (star T) = τ.norm₂ T := by
  have h := τ.trace_mul_comm (star T) T
  have h2 := τ.trace_star_mul (star T)
  simp only [star_star] at h2
  rw [τ.trace_star_mul, h2] at h
  have hr := congrArg Complex.re h
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at hr
  have hn : 0 ≤ τ.norm₂ T := norm_nonneg _
  have hs : 0 ≤ τ.norm₂ (star T) := norm_nonneg _
  nlinarith

@[simp] theorem norm₂_zero : τ.norm₂ 0 = 0 := by simp [norm₂]
@[simp] theorem norm₂_sub (S T : Algebra (M := M)) :
    τ.norm₂ (S-T) = ‖(S : H →L[ℂ] H) τ.vector - (T : H →L[ℂ] H) τ.vector‖ := rfl

theorem norm₂_add_le (S T : Algebra (M := M)) : τ.norm₂ (S+T) ≤ τ.norm₂ S+τ.norm₂ T :=
  norm_add_le _ _

theorem norm₂_mul_le (S T : Algebra (M := M)) : τ.norm₂ (S*T) ≤ ‖S‖ * τ.norm₂ T :=
  (S : H →L[ℂ] H).le_opNorm ((T : H →L[ℂ] H) τ.vector)

theorem norm₂_mul_le_right (S T : Algebra (M := M)) : τ.norm₂ (S*T) ≤ τ.norm₂ S * ‖T‖ := by
  rw [← τ.norm₂_star (S*T), star_mul]
  have h := τ.norm₂_mul_le (star T) (star S)
  simpa [τ.norm₂_star, mul_comm, ContinuousLinearMap.star_eq_adjoint] using h

end TracialRepresentation

end

end UltrapowerBridge

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Ultrapower
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UltrapowerBridge

section
open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem operator_norm_one_le : ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro x; simp)

/-- Operator-norm bounded sequences, as an actual star subalgebra of pointwise sequences. -/
def boundedSequences (M : VonNeumannAlgebra H) : StarSubalgebra ℂ (ℕ → M.toStarSubalgebra) where
  carrier := {a | ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖a n‖ ≤ C}
  zero_mem' := ⟨0, le_rfl, by simp⟩
  one_mem' := ⟨1, by norm_num, fun n => operator_norm_one_le⟩
  add_mem' := by
    rintro a b ⟨C,hC,ha⟩ ⟨D,hD,hb⟩
    exact ⟨C+D, add_nonneg hC hD, fun n =>
      (norm_add_le _ _).trans (add_le_add (ha n) (hb n))⟩
  mul_mem' := by
    rintro a b ⟨C,hC,ha⟩ ⟨D,hD,hb⟩
    exact ⟨C*D, mul_nonneg hC hD, fun n =>
      (norm_mul_le _ _).trans (mul_le_mul (ha n) (hb n) (norm_nonneg _) hC)⟩
  algebraMap_mem' c := by
    refine ⟨‖c‖, norm_nonneg _, fun n => ?_⟩
    change ‖algebraMap ℂ M.toStarSubalgebra c‖ ≤ ‖c‖
    rw [Algebra.algebraMap_eq_smul_one, norm_smul]
    exact (mul_le_mul_of_nonneg_left operator_norm_one_le (norm_nonneg c)).trans_eq (mul_one _)
  star_mem' := by
    rintro a ⟨C,hC,ha⟩
    refine ⟨C,hC,fun n => ?_⟩
    change ‖star (a n : H →L[ℂ] H)‖ ≤ C
    simpa [ContinuousLinearMap.star_eq_adjoint] using ha n

abbrev Bounded (M : VonNeumannAlgebra H) := boundedSequences M

variable (τ : TracialRepresentation M) (l : Filter ℕ)
/-- The trace-null equivalence relation, before descending algebra operations. -/
def TraceRel (a b : Bounded M) : Prop :=
  Tendsto (fun n => τ.norm₂ (a.val n-b.val n)) l (𝓝 0)

theorem traceRel_refl (a : Bounded M) : TraceRel τ l a a := by
  simp only [TraceRel, sub_self, τ.norm₂_zero]
  exact tendsto_const_nhds

theorem traceRel_symm {a b : Bounded M} (h : TraceRel τ l a b) : TraceRel τ l b a := by
  simpa only [TraceRel, τ.norm₂_sub, norm_sub_rev] using h

theorem traceRel_trans {a b c : Bounded M}
    (hab : TraceRel τ l a b) (hbc : TraceRel τ l b c) : TraceRel τ l a c := by
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using hab.add hbc)
  have he : a.val n-c.val n = (a.val n-b.val n)+(b.val n-c.val n) := by abel
  rw [he]
  exact τ.norm₂_add_le _ _

theorem traceRel_add {a b c d : Bounded M}
    (hab : TraceRel τ l a b) (hcd : TraceRel τ l c d) : TraceRel τ l (a+c) (b+d) := by
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using hab.add hcd)
  change τ.norm₂ ((a.val n+c.val n)-(b.val n+d.val n)) ≤ _
  have he : (a.val n+c.val n)-(b.val n+d.val n) =
      (a.val n-b.val n)+(c.val n-d.val n) := by abel
  rw [he]
  exact τ.norm₂_add_le _ _

theorem traceRel_mul {a b c d : Bounded M}
    (hab : TraceRel τ l a b) (hcd : TraceRel τ l c d) : TraceRel τ l (a*c) (b*d) := by
  obtain ⟨C,hC,hc⟩ := c.property
  obtain ⟨B,hB,hb⟩ := b.property
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa using (hab.mul_const C).add (hcd.const_mul B))
  change τ.norm₂ (a.val n*c.val n-b.val n*d.val n) ≤ _
  have he : a.val n*c.val n-b.val n*d.val n =
      (a.val n-b.val n)*c.val n+b.val n*(c.val n-d.val n) := by noncomm_ring
  rw [he]
  exact (τ.norm₂_add_le _ _).trans (add_le_add
    ((τ.norm₂_mul_le_right _ _).trans (mul_le_mul_of_nonneg_left (hc n) (norm_nonneg _)))
    ((τ.norm₂_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))))

theorem traceRel_star {a b : Bounded M} (hab : TraceRel τ l a b) :
    TraceRel τ l (star a) (star b) := by
  change Tendsto (fun n => τ.norm₂ (star (a.val n)-star (b.val n))) l (𝓝 0)
  simpa only [TraceRel, ← star_sub, τ.norm₂_star] using hab

/-- Algebra congruence proved from actual trace-norm estimates. -/
def traceCongruence : RingCon (Bounded M) where
  r := TraceRel τ l
  iseqv := ⟨traceRel_refl τ l, traceRel_symm τ l, traceRel_trans τ l⟩
  add' := traceRel_add τ l
  mul' := traceRel_mul τ l

/-- Underlying ring of the tracial ultrapower when l is a free ultrafilter. -/
abbrev TracialQuotient := (traceCongruence τ l).Quotient

def quotientMap : Bounded M →+* TracialQuotient τ l := (traceCongruence τ l).mk'

end

section
open Filter
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (l : Filter ℕ)

instance instStarTracialQuotient : Star (TracialQuotient τ l) :=
  ⟨Quotient.map' star (fun _ _ h => traceRel_star τ l h)⟩

@[simp] theorem quotientMap_star (a : Bounded M) :
    quotientMap τ l (star a) = star (quotientMap τ l a) := rfl

@[simp] theorem quotientMap_smul (c : ℂ) (a : Bounded M) :
    quotientMap τ l (c • a) = c • quotientMap τ l a := rfl

end

open Filter
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M) (ω : Ultrafilter ℕ)

@[simp] theorem TracialRepresentation.trace_sub (a b : M.toStarSubalgebra) :
    τ.trace (a-b) = τ.trace a-τ.trace b := inner_sub_right _ _ _

@[simp] theorem TracialRepresentation.trace_add (a b : M.toStarSubalgebra) :
    τ.trace (a+b) = τ.trace a+τ.trace b := inner_add_right _ _ _

end UltrapowerBridge

/-! Commutation with every bounded subalgebra sequence implies uniform coordinate commutator decay. -/
open Filter
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixUnits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Actual finite matrix algebras from matrix-unit laws. No factor or trace
hypothesis is needed for the algebraic construction. -/
open scoped BigOperators

structure MatrixUnitSystem (ι A : Type*) [Fintype ι] [DecidableEq ι]
    [Ring A] [StarRing A] [Algebra ℂ A] where
  entry : ι → ι → A
  star_entry : ∀ i j, star (entry i j) = entry j i
  mul_entry : ∀ i j k l, entry i j * entry k l = if j = k then entry i l else 0
  total : ∑ i, entry i i = 1

namespace MatrixUnitSystem
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable (E : MatrixUnitSystem ι A)

def linearMap : Matrix ι ι ℂ →ₗ[ℂ] A where
  toFun a := ∑ i, ∑ j, a i j • E.entry i j
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, smul_smul]

theorem linearMap_apply (a : Matrix ι ι ℂ) :
    E.linearMap a = ∑ i, ∑ j, a i j • E.entry i j := rfl

@[simp] theorem linearMap_single (i j : ι) (c : ℂ) :
    E.linearMap (Matrix.single i j c) = c • E.entry i j := by
  simp [linearMap_apply, Matrix.single, ite_smul, ite_and]

theorem linearMap_one : E.linearMap 1 = 1 := by
  simpa [linearMap_apply, Matrix.one_apply, ite_smul] using E.total

theorem linearMap_mul (a b : Matrix ι ι ℂ) :
    E.linearMap (a*b) = E.linearMap a * E.linearMap b := by
  simp only [linearMap_apply, Matrix.mul_apply, Finset.sum_smul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_smul, E.mul_entry]
  simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  conv_rhs =>
    arg 2
    intro k
    rw [Finset.sum_comm]
  rw [Finset.sum_comm (f := fun k i => ∑ l, (a i k * b k l) • E.entry i l)]
  apply Finset.sum_congr rfl
  intro i hi
  exact Finset.sum_comm

variable [StarModule ℂ A]

theorem linearMap_star (a : Matrix ι ι ℂ) :
    E.linearMap (star a) = star (E.linearMap a) := by
  simp only [linearMap_apply, star_sum, star_smul, E.star_entry]
  rw [Finset.sum_comm]
  rfl

def hom : Matrix ι ι ℂ →⋆ₐ[ℂ] A where
  toFun := E.linearMap
  map_one' := E.linearMap_one
  map_mul' := E.linearMap_mul
  map_zero' := E.linearMap.map_zero
  map_add' := E.linearMap.map_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, E.linearMap.map_smul, E.linearMap_one,
      Algebra.algebraMap_eq_smul_one]
  map_star' := E.linearMap_star

@[simp] theorem hom_apply (a : Matrix ι ι ℂ) :
    E.hom a = ∑ i, ∑ j, a i j • E.entry i j := rfl

@[simp] theorem hom_single (i j : ι) (c : ℂ) :
    E.hom (Matrix.single i j c) = c • E.entry i j := E.linearMap_single i j c

/-! Commuting unital systems multiply to a larger full matrix algebra.
This proves compatibility algebraically; it does not construct a system in
a relative commutant or establish irreducibility of an infinite union. -/
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

variable (F : MatrixUnitSystem κ A)
variable (hc : ∀ i j k l, Commute (E.entry i j) (F.entry k l))

/-! Corner amplification inside the actual matrix-unit commutant. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

def commutant : StarSubalgebra ℂ A where
  carrier := {x | ∀ i j, Commute (E.entry i j) x}
  zero_mem' := by intro i j; exact Commute.zero_right _
  one_mem' := by intro i j; exact Commute.one_right _
  add_mem' hx hy := fun i j => (hx i j).add_right (hy i j)
  mul_mem' hx hy := fun i j => (hx i j).mul_right (hy i j)
  algebraMap_mem' c := fun i j => (Algebra.commutes c _).symm
  star_mem' hx := by
    intro i j
    show E.entry i j*star _=star _*E.entry i j
    simpa only [star_mul,E.star_entry] using (congrArg star (hx j i).eq).symm

/-! Diffuseness passes to the full matrix-unit commutant by splitting a
compressed projection and amplifying the split. -/
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

open scoped BigOperators
variable {ι κ A B : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A]
variable [Ring B] [StarRing B] [Algebra ℂ B]
variable (E : MatrixUnitSystem ι A)

def map (f : A →⋆ₐ[ℂ] B) : MatrixUnitSystem ι B where
  entry i j := f (E.entry i j)
  star_entry i j := by rw [← map_star,E.star_entry]
  mul_entry i j k l := by
    rw [← map_mul,E.mul_entry]
    split <;> simp_all
  total := by rw [← map_sum,E.total,map_one]

/-! Actual matrix amplification by coefficients in the full matrix-unit
commutant. The evaluation homomorphism is proved surjective algebraically. -/
open scoped BigOperators

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure FiniteMatrixStage (N : VonNeumannAlgebra H) where
  size : ℕ
  positive : 0 < size
  units : MatrixUnitSystem (Fin size) N.toStarSubalgebra

end

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/

end Generator

end

end OAI
end


