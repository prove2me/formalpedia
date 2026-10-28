-- Prove2me | Definitions.Def_OAIQ039C028
-- name    : OAIQ039C028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:17:43.603113+00:00
-- url     : https://prove2.me/theorems/0ec8b16c-ea9a-434f-9473-47e5a15f1571
-- title:
--   Definitions bundle OAIQ039C028 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 9 definitions, 1 instance and 27 theorems. The definitions and types are `OAI.Kadison.InfiniteAmplification.single0`, `OAI.Kadison.MatrixCornerExtension.columns`, `OAI.Kadison.MatrixCornerExtension.cornerMap`, `OAI.Kadison.MatrixCornerExtension.entry`, `OAI.Kadison.MatrixCornerHilbert.matrixInsert`, `OAI.Kadison.MatrixGNS.flatBalancedUnitary`, `OAI.Kadison.MatrixGNS.flattenCopies`, `OAI.Kadison.MatrixModules.basisCopies`, `OAI.Kadison.MatrixModules.recombine`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_InfiniteBoundTransfer`, `Commutator_MatrixCornerExtension`, `Commutator_MatrixCornerHilbert`, `Commutator_MatrixExpectation`, `Commutator_MatrixExpectationNested`, `Commutator_MatrixFlatten`, `Commutator_MatrixFlattenRepresentation`, `Commutator_MatrixModules`, `Commutator_ProjectionPartition`.
--
--   **Imports.** It imports the bundles `OAIQ039C000`, `OAIQ039C002`, `OAIQ039C003`, `OAIQ039C004`, `OAIQ039C006`, `OAIQ039C012` and `OAIQ039C013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C038` and `OAIQ039C039`; the statements `OAI.Kadison.MatrixCornerImplementation.corner_derivation_bound`, `OAI.Kadison.MatrixGNS.flatBalancedUnitary_sq` and `OAI.Kadison.MatrixGNS.flatBalanced_commutator_dominates`; the proofs of `OAI.Kadison.LocalQuantization.exists_small_projection`, `OAI.Kadison.MatrixCornerImplementation.corner_derivation_bound`, `OAI.Kadison.MatrixGNS.flatBalancedUnitary_sq`, `OAI.Kadison.MatrixGNS.flatBalanced_commutator_dominates` and `OAI.Kadison.MatrixGNS.flattenCopies_commutator_norm`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C000
import Definitions.Def_OAIQ039C002
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C004
import Definitions.Def_OAIQ039C006
import Definitions.Def_OAIQ039C012
import Definitions.Def_OAIQ039C013

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCornerHilbert
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixCornerHilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance instIsClosedCoeSubmoduleComplexFixedSpace (p : H →L[ℂ] H) : IsClosed ((fixedSpace p : Submodule ℂ H) : Set H) :=
  (p-1).isClosed_ker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (p : H →L[ℂ] H) (v : ι → H →L[ℂ] H)
  (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
  (hinit : ∀ i, p*star (v i)=star (v i))
  (htotal : ∑ i, v i*star (v i)=1)

def matrixInsert (i : ι) : fixedSpace p →ₗᵢ[ℂ] H :=
  insert p (v i) (by simpa using hcol i i)

include hinit in
omit [Fintype ι] [DecidableEq ι] in
lemma adjoint_mem_fixed (i : ι) (x : H) : (star (v i)) x∈fixedSpace p := by
  rw [mem_fixedSpace]
  exact congrArg (fun T : H →L[ℂ] H => T x) (hinit i)

include hcol in
omit [Fintype ι] in
lemma matrixInsert_orthogonal : OrthogonalFamily ℂ (fun _ : ι => fixedSpace p)
    (matrixInsert p v hcol) := by
  intro i j hij x y
  change inner ℂ (v i x) (v j y)=0
  rw [←adjoint_inner_right]
  have he : (v i).adjoint (v j y)=0 := by
    simpa only [ite_eq_right hij,zero_apply,mul_apply_eq_comp,star_eq_adjoint] using congrArg (fun T : H →L[ℂ] H => T y) (hcol i j)
  rw [he,inner_zero_right]

include hinit htotal in
lemma matrixInsert_isHilbertSum : IsHilbertSum ℂ (fun _ : ι => fixedSpace p)
    (matrixInsert p v hcol) := by
  apply IsHilbertSum.mk (matrixInsert_orthogonal p v hcol)
  intro x _
  have hx : ∑ i, v i ((star (v i)) x)=x := by
    simpa only [sum_apply,mul_apply_eq_comp,one_apply_eq_self] using
      congrArg (fun T : H →L[ℂ] H => T x) htotal
  rw [←hx]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.le_topologicalClosure
  apply Submodule.mem_iSup_of_mem i
  exact ⟨⟨(star (v i)) x,adjoint_mem_fixed p v hinit i x⟩,rfl⟩

end Kadison.MatrixCornerHilbert

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixFlatten
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.MatrixGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance instDecidableEq_solutions_1_r2c797d_1 : DecidableEq ι := Classical.decEq ι
attribute [local instance] OAI.Kadison.MatrixGNS.instDecidableEq_solutions_2
attribute [local instance] OAI.Kadison.MatrixGNS.instDecidableEqProd_solutions
def flatBalancedUnitary (X : CStarMatrix ι ι A) (hX : ‖X‖≤1) :
    _root_.unitary (CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A) :=
  ⟨flatten ι (Fin 2) (BalancedDilation.symmetry X),
    by
      rw [Unitary.mem_iff]
      have h := (Unitary.mem_iff.mp (BalancedDilation.symmetry_unitary X hX))
      constructor
      · rw [←map_star,←map_mul,h.1,map_one]
      · rw [←map_star,←map_mul,h.2,map_one]⟩

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixExpectation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixExpectation

open Matrix TracialGNS

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

lemma expectation_apply (a : A) : expectation φ a=
    (Fintype.card I:ℂ)⁻¹ • ∑ i,∑ j,φ (single i j 1)*a*φ (single j i 1) := by
  simp only [expectation,LinearMap.smul_apply,LinearMap.sum_apply,LinearMap.comp_apply,
    LinearMap.mulLeft_apply,LinearMap.mulRight_apply,mul_assoc]

lemma star_expectation (a : A) : star (expectation φ a)=expectation φ (star a) := by
  rw [expectation_apply,expectation_apply]
  simp only [star_smul,star_sum,star_mul,←map_star,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_single,star_one,star_inv₀,star_natCast,mul_assoc]

lemma selfAdjoint {a : A} (ha : IsSelfAdjoint a) : IsSelfAdjoint (expectation φ a) := by
  change star (expectation φ a)=expectation φ a
  rw [star_expectation,ha.star_eq]

lemma single_left (a : A) (k l : I) :
    φ (single k l 1)*expectation φ a=
      (Fintype.card I:ℂ)⁻¹ • ∑ j,φ (single k j 1)*a*φ (single j l 1) := by
  rw [expectation_apply,mul_smul_comm,Finset.mul_sum]
  simp only [Finset.mul_sum,←mul_assoc,←map_mul]
  rw [Finset.sum_eq_single l]
  · simp only [single_mul_single_same,one_mul]
  · intro i hi hil
    apply Finset.sum_eq_zero
    intro j hj
    rw [single_mul_single_of_ne 1 k l i hil.symm 1,map_zero,zero_mul,zero_mul]
  · simp

lemma single_right (a : A) (k l : I) :
    expectation φ a*φ (single k l 1)=
      (Fintype.card I:ℂ)⁻¹ • ∑ j,φ (single k j 1)*a*φ (single j l 1) := by
  rw [expectation_apply,smul_mul_assoc,Finset.sum_mul]
  simp only [Finset.sum_mul,mul_assoc,←map_mul]
  rw [Finset.sum_eq_single k]
  · simp only [single_mul_single_same,one_mul]
  · intro i hi hik
    apply Finset.sum_eq_zero
    intro j hj
    rw [single_mul_single_of_ne 1 j i k hik 1,map_zero,mul_zero,mul_zero]
  · simp

lemma commutes (a : A) (x : Matrix I I ℂ) : φ x*expectation φ a=expectation φ a*φ x := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single x]
  conv_rhs => rw [Matrix.matrix_eq_sum_single x]
  simp only [map_sum,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have hs : single k l (x k l)=(x k l) • single k l (1:ℂ) := by simp
  rw [hs,map_smul,smul_mul_assoc,mul_smul_comm,single_left,single_right]

lemma on_matrix (x : Matrix I I ℂ) :
    expectation φ (φ x)=((Fintype.card I:ℂ)⁻¹*x.trace) • (1:A) := by
  rw [expectation_apply]
  simp only [←map_mul,←map_sum]
  rw [matrixSum,map_smul,map_one,smul_smul]

variable [Nonempty I]

lemma fixes (a : A) (ha : ∀ x : Matrix I I ℂ,φ x*a=a*φ x) : expectation φ a=a := by
  rw [expectation_apply]
  have he (i j : I) : φ (single i j 1)*a*φ (single j i 1)=a*φ (single i i 1) := by
    rw [ha,mul_assoc,←map_mul,single_mul_single_same,one_mul]
  have hsum : (∑ i,a*φ (single i i 1))=a := by
    rw [←Finset.mul_sum,←map_sum,Matrix.sum_single_one,map_one,mul_one]
  simp only [he,Finset.sum_const,Finset.card_univ]
  rw [←Finset.smul_sum,hsum,←Nat.cast_smul_eq_nsmul ℂ,smul_smul,
    inv_mul_cancel₀ (card_ne (I:=I)),one_smul]

lemma idempotent (a : A) : expectation φ (expectation φ a)=expectation φ a :=
  fixes φ _ (commutes φ a)

variable [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

omit [Nonempty I] in
include hτ in
lemma inner_symm (a b : A) :
    inner ℂ (algebraVector τ (expectation φ a)) (algebraVector τ b)=
      inner ℂ (algebraVector τ a) (algebraVector τ (expectation φ b)) := by
  rw [inner_algebraVector,inner_algebraVector,expectation_apply,expectation_apply]
  simp only [star_smul,star_sum,star_mul,←map_star,Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_single,star_one,smul_mul_assoc,mul_smul_comm,
    Finset.sum_mul,Finset.mul_sum,map_smul,map_sum]
  congr 1
  · simp
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [mul_assoc] using
      hτ (φ (single j i 1)) (star a*φ (single i j 1)*b)

include hτ in
lemma norm_vector_le (a : A) : ‖algebraVector τ (expectation φ a)‖≤‖algebraVector τ a‖ := by
  have hi := inner_symm φ τ hτ a (expectation φ a)
  rw [idempotent] at hi
  have hr := congrArg (RCLike.re : ℂ → ℝ) hi
  rw [←norm_sq_eq_re_inner (𝕜:=ℂ)] at hr
  have hb := re_inner_le_norm (𝕜:=ℂ) (algebraVector τ a) (algebraVector τ (expectation φ a))
  have h0 := norm_nonneg (algebraVector τ (expectation φ a))
  nlinarith [norm_nonneg (algebraVector τ a)]

include hτ in
lemma trace_preserving (a : A) : τ (expectation φ a)=τ a := by
  have he := fixes φ (1:A) (fun x => by rw [mul_one,one_mul])
  have hi := inner_symm φ τ hτ 1 a
  rw [he] at hi
  simpa only [inner_algebraVector,star_one,one_mul] using hi.symm

include hτ in
lemma on_matrix_trace (hone : τ 1=1) (x : Matrix I I ℂ) :
    expectation φ (φ x)=τ (φ x) • (1:A) := by
  have ht := trace_preserving φ τ hτ (φ x)
  rw [on_matrix,map_smul,hone,smul_eq_mul,mul_one] at ht
  rw [on_matrix,ht]

end Kadison.MatrixExpectation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixExpectationNested
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.MatrixExpectation

open TracialGNS

variable {A I J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J] [Nonempty J]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (ψ : Matrix J J ℂ →⋆ₐ[ℂ] A)
  (hsub : φ.range≤ψ.range)

omit [PartialOrder A] [StarOrderedRing A] [Nonempty J] in
include hsub in
lemma nested_fixed (a : A) : expectation φ (expectation ψ a)=expectation ψ a := by
  apply fixes
  intro x
  obtain ⟨y,hy⟩ := hsub (show φ x∈φ.range from ⟨x,rfl⟩)
  change ψ y=φ x at hy
  rw [←hy]
  exact commutes ψ a y

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

omit [PartialOrder A] [StarOrderedRing A] in
lemma fixes_scalar (z : ℂ) : expectation φ (z • (1:A))=z • (1:A) := by
  rw [map_smul,fixes φ 1 (fun x => by rw [mul_one,one_mul])]

end Kadison.MatrixExpectation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionPartition
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.SpectralPartition

variable {R : Type*} [Ring R] [StarRing R]

lemma splitPiece_orthogonal {p : R} (hp : IsStarProjection p) {b c : Bool} (h : b≠c) :
    splitPiece p b*splitPiece p c=0 := by
  cases b <;> cases c <;> simp_all [splitPiece,mul_sub,sub_mul,hp.isIdempotentElem.eq]

end Kadison.SpectralPartition

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_InfiniteBoundTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.InfiniteAmplification

open IntertwinerCompression

local instance infiniteBoundTransferDecidableEq_r2c797d_1 {α : Sort*} : DecidableEq α := Classical.decEq α
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def single0 : H →ₗᵢ[ℂ] Space ℕ H :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 0).toLinearMap.isometryOfInner
    (fun x y => by
      change inner ℂ (lp.single (E:=fun _ : ℕ => H) 2 0 x)
        (lp.single (E:=fun _ : ℕ => H) 2 0 y)=inner ℂ x y
      rw [lp.inner_single_left,lp.single_apply,Pi.single_eq_same])

end Kadison.InfiniteAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCornerExtension
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixCornerExtension

open MatrixCornerHilbert

variable {A K H ι : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

variable (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

variable {p : A} (hp : IsStarProjection p) (v : ι → A)
  (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
  (hinit : ∀ i, p*star (v i)=star (v i))
  (htotal : ∑ i, v i*star (v i)=1)

def columns (i : ι) : fixedSpace (σ p) →ₗᵢ[ℂ] K :=
  matrixInsert (σ p) (fun i => σ (v i)) (mapped_col σ v hcol) i

include hinit htotal in
lemma columns_total : IsHilbertSum ℂ (fun _ : ι => fixedSpace (σ p)) (columns σ v hcol) :=
  matrixInsert_isHilbertSum (σ p) (fun i => σ (v i)) (mapped_col σ v hcol)
    (mapped_init σ v hinit) (mapped_total σ v htotal)

def entry (i j : ι) (a : A) : Corner hp :=
  ⟨star (v i)*a*v j,by rw [←mul_assoc,←mul_assoc,hinit i],
    by rw [mul_assoc,final_support hp v hinit j]⟩

variable (G : K →L[ℂ] H) (hGp : ∀ x, G (σ p x)=ρ p (G x))

def cornerMap : fixedSpace (σ p) →L[ℂ] fixedSpace (ρ p) :=
  G.restrict (by
    intro x hx
    rw [mem_fixedSpace] at hx ⊢
    rw [←hGp x,hx])

end Kadison.MatrixCornerExtension

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixFlattenRepresentation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixGNS

open OperatorAmplification CyclicColumns

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance matrixFlattenRepresentationIndexDecidableEq_r2c797d_1 : DecidableEq ι := Classical.decEq ι
attribute [local instance] OAI.Kadison.MatrixGNS.matrixFlattenRepresentationCopiesDecidableEq
def flattenCopies : SumSpace (H:=SumSpace (H:=H) ι) κ ≃ₗᵢ[ℂ] SumSpace (H:=H) (κ×ι) where
  toFun v := WithLp.toLp 2 (fun p => v p.1 p.2)
  invFun v := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => v (i,j)))
  left_inv v := rfl
  right_inv v := rfl
  map_add' v w := by ext p; rfl
  map_smul' z v := by ext p; rfl
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type]

omit [CompleteSpace H] in
@[simp] lemma flattenCopies_apply (v : SumSpace (H:=SumSpace (H:=H) ι) κ) (p : κ×ι) :
    flattenCopies ι κ v p=v p.1 p.2 := rfl

omit [CompleteSpace H] in
@[simp] lemma flattenCopies_symm_apply (v : SumSpace (H:=H) (κ×ι)) (i : κ) (j : ι) :
    (flattenCopies (H:=H) ι κ).symm v i j=v (i,j) := rfl

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixModules
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.MatrixModules

open Matrix

variable {𝕜 I E : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup E] [Module 𝕜 E]

variable (ρ : Matrix I I 𝕜 →ₐ[𝕜] Module.End 𝕜 E) (o : I)

lemma corner_fixed (x : corner ρ o) : ρ (single o o 1) (x : E) = x := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  change (ρ (single o o 1) * ρ (single o o 1)) y = _
  rw [← map_mul, Matrix.single_mul_single_same, one_mul]

noncomputable def recombine : (I → corner ρ o) →ₗ[𝕜] E :=
  ∑ i : I, (ρ (single i o 1)).comp
    ((corner ρ o).subtype.comp (LinearMap.proj i))

@[simp] lemma coordinates_apply (i : I) (x : E) :
    (coordinates ρ o i x : E) = ρ (single o i 1) x := rfl

@[simp] lemma recombine_apply (x : I → corner ρ o) :
    recombine ρ o x = ∑ i : I, ρ (single i o 1) (x i : E) := by
  simp [recombine]

lemma recombine_coordinates (x : E) :
    recombine ρ o (fun i => coordinates ρ o i x) = x := by
  rw [recombine_apply]
  simp only [coordinates_apply]
  have h (i : I) : ρ (single i o 1) (ρ (single o i 1) x) = ρ (single i i 1) x := by
    change (ρ (single i o 1) * ρ (single o i 1)) x = _
    rw [← map_mul, Matrix.single_mul_single_same, one_mul]
  simp only [h]
  rw [← LinearMap.sum_apply, ← map_sum, Matrix.sum_single_one, map_one]
  rfl

section Coordinates

variable {R : Type*} [Fintype R]

noncomputable def basisCopies (b : Module.Basis R 𝕜 (corner ρ o)) :
    (I × R → 𝕜) ≃ₗ[𝕜] (I → corner ρ o) :=
  (LinearEquiv.curry 𝕜 𝕜 I R).trans
    (LinearEquiv.piCongrRight fun _ => b.equivFun.symm)

@[simp] lemma basisCopies_apply (b : Module.Basis R 𝕜 (corner ρ o)) (v : I × R → 𝕜)
    (i : I) : basisCopies ρ o b v i = b.equivFun.symm (fun r => v (i, r)) := rfl

end Coordinates

end Kadison.MatrixModules
end

end OAI
end


