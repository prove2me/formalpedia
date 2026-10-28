-- Prove2me | Definitions.Def_OAIQ039C013
-- name    : OAIQ039C013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:13:26.214008+00:00
-- url     : https://prove2.me/theorems/af5d8bac-e492-4423-99f8-da10bc6b6b31
-- title:
--   Definitions bundle OAIQ039C013 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 24 definitions and 24 theorems. The definitions and types are `OAI.Kadison.MatrixCorners.cutBlock`, `OAI.Kadison.MatrixCorners.cutEmbedding`, `OAI.Kadison.MatrixCorners.normalizedStageAlphabet`, `OAI.Kadison.MatrixCorners.projectionAlphabet`, `OAI.Kadison.MatrixCorners.projectionEmbedding`, `OAI.Kadison.MatrixCorners.projectionIndices`, `OAI.Kadison.MatrixCorners.reindexStarAlgEquiv`, `OAI.Kadison.MatrixCorners.shiftMatrix`, `OAI.Kadison.MatrixCorners.stageAlphabet`, `OAI.Kadison.MatrixDiagonal.diagonal`, `OAI.Kadison.MatrixGNS.ArraySpace`, `OAI.Kadison.MatrixGNS.flatten`, `OAI.Kadison.MatrixGNS.flattenHom`, `OAI.Kadison.MatrixGNS.instDecidableEqProd_solutions`, `OAI.Kadison.MatrixGNS.instDecidableEq_solutions`, `OAI.Kadison.MatrixGNS.instDecidableEq_solutions_2`, `OAI.Kadison.MatrixGNS.matrixFlattenRepresentationCopiesDecidableEq`, `OAI.Kadison.MatrixGNS.matrixGNSUnitaryDecidableEq`, `OAI.Kadison.MatrixGNS.matrixRowCornerDecidableEq`, `OAI.Kadison.MatrixGNS.matrixVectorTraceDecidableEq`, `OAI.Kadison.MatrixGNS.rowMatrix`, `OAI.Kadison.MatrixGNS.scale`, `OAI.Kadison.MatrixModules.coordinates`, `OAI.Kadison.MatrixModules.corner`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_CornerAlphabetGNS`, `Commutator_MatrixCornerExtension`, `Commutator_MatrixCutEmbedding`, `Commutator_MatrixDiagonal`, `Commutator_MatrixExpectation`, `Commutator_MatrixFlatten`, `Commutator_MatrixFlattenRepresentation`, `Commutator_MatrixGNSUnitary`, `Commutator_MatrixModules`, `Commutator_MatrixProjectionDiagonal`, `Commutator_MatrixRowCorner`, `Commutator_MatrixTraceFaithful`, `Commutator_MatrixUnitaryAlphabet`, `Commutator_MatrixVectorTrace`, `Commutator_ProjectionPartition`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ039C028`; the statements `OAI.Kadison.MatrixCorners.normalizedStageAlphabet_centered`, `OAI.Kadison.MatrixCorners.normalizedStageAlphabet_orthonormal`, `OAI.Kadison.MatrixCorners.projection_rank`, `OAI.Kadison.MatrixGNS.flattenCopies_commutator_norm` and `OAI.Kadison.MatrixGNS.row_corner_commutator_bound`; the proofs of `OAI.Kadison.MatrixCorners.normalizedStageAlphabet_centered`, `OAI.Kadison.MatrixCorners.normalizedStageAlphabet_orthonormal`, `OAI.Kadison.MatrixCorners.projection_rank`, `OAI.Kadison.MatrixGNS.row_corner_commutator_bound` and `OAI.Kadison.TracialGNS.corner_arbitrarily_large_alphabet`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixProjectionDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace Kadison.MatrixCorners

variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] Classical.propDecidable

omit [DecidableEq I] in
lemma projection_hermitian (p : Matrix I I ℂ) (hp : IsStarProjection p) : p.IsHermitian := hp.isSelfAdjoint

def projectionIndices (p : Matrix I I ℂ) (hp : IsStarProjection p) : Set I :=
  {i | (projection_hermitian p hp).eigenvalues i = 1}

end Kadison.MatrixCorners

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCutEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace Kadison.MatrixCorners

variable {I J K : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

attribute [local instance] Classical.propDecidable

def cutBlock : Matrix J J ℂ →⋆ₙₐ[ℂ] Matrix (J⊕K) (J⊕K) ℂ where
  toFun a := Matrix.fromBlocks a 0 0 0
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_add' a b := by ext i j; cases i <;> cases j <;> simp
  map_smul' c a := by ext i j; cases i <;> cases j <;> simp
  map_mul' a b := by simp [Matrix.fromBlocks_multiply]
  map_star' a := by
    change _= (Matrix.fromBlocks a (0:Matrix J K ℂ) 0 0).conjTranspose
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero]
    rfl

def reindexStarAlgEquiv (e : J ≃ I) : Matrix J J ℂ ≃⋆ₐ[ℂ] Matrix I I ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_smul' := fun c a => by ext i j; rfl
    map_star' := fun a => by exact (Matrix.conjTranspose_reindex e e a).symm }

def cutEmbedding (s : Set I) : Matrix s s ℂ →⋆ₙₐ[ℂ] Matrix I I ℂ :=
  (reindexStarAlgEquiv (Equiv.Set.sumCompl s)).toNonUnitalStarAlgHom.comp
    (cutBlock (K := (sᶜ:Set I)))

def projectionEmbedding (p : Matrix I I ℂ) (hp : IsStarProjection p) :
    Matrix (projectionIndices p hp) (projectionIndices p hp) ℂ →⋆ₙₐ[ℂ] Matrix I I ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix I I ℂ)
    (projection_hermitian p hp).eigenvectorUnitary).toNonUnitalStarAlgHom.comp
      (cutEmbedding (projectionIndices p hp))

end Kadison.MatrixCorners

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixUnitaryAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder Matrix

namespace Kadison.MatrixCorners

attribute [local instance] Classical.propDecidable

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

def shiftMatrix (g : G) : Matrix G G ℂ := (Equiv.addLeft g).permMatrix ℂ

def projectionAlphabet (p : Matrix I I ℂ) (hp : IsStarProjection p)
    (e : G ≃ projectionIndices p hp) (g : G) : Matrix I I ℂ :=
  projectionEmbedding p hp (reindexStarAlgEquiv e (shiftMatrix g))

end Kadison.MatrixCorners

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerAlphabetGNS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace Kadison.MatrixCorners

attribute [local instance] Classical.propDecidable

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b)=τ (b*a)) (h1 : τ 1=1)
  {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (p : Matrix I I ℂ) (hp : IsStarProjection p)
  {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
  (e : G ≃ projectionIndices p hp)

def stageAlphabet (g : G) : A := φ (projectionAlphabet p hp e g)

variable (α : ℝ) (hα : 0<α) (hατ : τ (φ p)=(α:ℂ))

def normalizedStageAlphabet (g : G) : A := (((Real.sqrt α)⁻¹:ℝ):ℂ) • stageAlphabet φ p hp e g

end Kadison.MatrixCorners

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCornerExtension
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

variable {A K H ι : Type*} [CStarAlgebra A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

variable (σ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

variable {p : A} (hp : IsStarProjection p) (v : ι → A)
  (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
  (hinit : ∀ i, p*star (v i)=star (v i))
  (htotal : ∑ i, v i*star (v i)=1)

include hcol in
omit [Fintype ι] in
lemma mapped_col (i j : ι) : star (σ (v i))*σ (v j)=if i=j then σ p else 0 := by
  simpa only [map_mul,map_star,apply_ite,map_zero] using congrArg σ (hcol i j)

include hinit in
omit [Fintype ι] [DecidableEq ι] in
lemma mapped_init (i : ι) : σ p*star (σ (v i))=star (σ (v i)) := by
  simpa only [map_mul,map_star] using congrArg σ (hinit i)

include htotal in
omit [DecidableEq ι] in
lemma mapped_total : ∑ i, σ (v i)*star (σ (v i))=1 := by
  simpa only [map_sum,map_mul,map_star,map_one] using congrArg σ htotal

include hp hinit in
omit [Fintype ι] [DecidableEq ι] in
lemma final_support (i : ι) : v i*p=v i := by
  simpa only [star_mul,star_star,hp.isSelfAdjoint.star_eq] using congrArg star (hinit i)

end Kadison.MatrixCornerExtension

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.MatrixDiagonal

open Matrix

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (o : I)

def diagonal : A →ₗ[ℂ] A :=
  ∑ i,(LinearMap.mulLeft ℂ (φ (single i o 1))).comp (LinearMap.mulRight ℂ (φ (single o i 1)))

lemma diagonal_apply (a : A) : diagonal φ o a=∑ i,φ (single i o 1)*a*φ (single o i 1) := by
  simp only [diagonal,LinearMap.sum_apply,LinearMap.comp_apply,
    LinearMap.mulLeft_apply,LinearMap.mulRight_apply,mul_assoc]

lemma single_left (a : A) (k l : I) :
    φ (single k l 1)*diagonal φ o a=φ (single k o 1)*a*φ (single o l 1) := by
  rw [diagonal_apply,Finset.mul_sum,Finset.sum_eq_single l]
  · rw [←mul_assoc,←mul_assoc,←map_mul,single_mul_single_same,one_mul]
  · intro i hi hil
    rw [←mul_assoc,←mul_assoc,←map_mul,single_mul_single_of_ne 1 k l i hil.symm 1,
      map_zero,zero_mul,zero_mul]
  · simp

lemma single_right (a : A) (k l : I) :
    diagonal φ o a*φ (single k l 1)=φ (single k o 1)*a*φ (single o l 1) := by
  rw [diagonal_apply,Finset.sum_mul,Finset.sum_eq_single k]
  · rw [mul_assoc,mul_assoc,←map_mul,single_mul_single_same,one_mul,mul_assoc]
  · intro i hi hik
    rw [mul_assoc,mul_assoc,←map_mul,single_mul_single_of_ne 1 o i k hik 1,
      map_zero,mul_zero,mul_zero]
  · simp

lemma commutes (a : A) (x : Matrix I I ℂ) :
    φ x*diagonal φ o a=diagonal φ o a*φ x := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single x]
  conv_rhs => rw [Matrix.matrix_eq_sum_single x]
  simp only [map_sum,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have hs : single k l (x k l)=(x k l) • single k l (1:ℂ) := by simp
  rw [hs,map_smul,smul_mul_assoc,mul_smul_comm,single_left,single_right]

lemma cut (a : A) :
    φ (single o o 1)*diagonal φ o a*φ (single o o 1)=
      φ (single o o 1)*a*φ (single o o 1) := by
  rw [single_left,mul_assoc,←map_mul,single_mul_single_same,one_mul]

lemma star_diagonal (a : A) : star (diagonal φ o a)=diagonal φ o (star a) := by
  simp only [diagonal_apply,star_sum,star_mul,←map_star,Matrix.star_eq_conjTranspose,
    conjTranspose_single,star_one,mul_assoc]

lemma mul_diagonal (a b : A) (ha : a*φ (single o o 1)=a) :
    diagonal φ o a*diagonal φ o b=diagonal φ o (a*b) := by
  conv_lhs => lhs; rw [diagonal_apply]
  rw [Finset.sum_mul]
  conv_rhs => rw [diagonal_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc,single_left]
  simp only [mul_assoc]
  rw [←mul_assoc a,ha]

lemma projection {p : A} (hp : IsStarProjection p) (hpr : p*φ (single o o 1)=p) :
    IsStarProjection (diagonal φ o p) := by
  constructor
  · change diagonal φ o p*diagonal φ o p=diagonal φ o p
    rw [mul_diagonal φ o p p hpr,hp.isIdempotentElem.eq]
  · change star (diagonal φ o p)=diagonal φ o p
    rw [star_diagonal,hp.isSelfAdjoint.star_eq]

lemma fixed (a : A) (ha : ∀ x : Matrix I I ℂ,φ x*a=a*φ x) :
    diagonal φ o (φ (single o o 1)*a*φ (single o o 1))=a := by
  rw [diagonal_apply]
  have hpoint (i : I) :
      φ (single i o 1)*(φ (single o o 1)*a*φ (single o o 1))*φ (single o i 1)=
        φ (single i i 1)*a := by
    calc
      _=(φ (single i o 1)*φ (single o o 1))*a*(φ (single o o 1)*φ (single o i 1)) := by simp only [mul_assoc]
      _=φ (single i o 1)*a*φ (single o i 1) := by simp only [←map_mul,single_mul_single_same,one_mul]
      _=a*φ (single i i 1) := by rw [ha,mul_assoc,←map_mul,single_mul_single_same,one_mul]
      _=φ (single i i 1)*a := (ha _).symm
  simp only [hpoint,←Finset.sum_mul,←map_sum,sum_single_one,map_one,one_mul]

lemma matrix_block (a : A) (i j : I) :
    φ (single i o 1)*(φ (single o o 1)*(φ (single o i 1)*a*φ (single j o 1))*
      φ (single o o 1))*φ (single o j 1)=φ (single i i 1)*a*φ (single j j 1) := by
  calc
    _=(φ (single i o 1)*φ (single o o 1)*φ (single o i 1))*a*
        (φ (single j o 1)*φ (single o o 1)*φ (single o j 1)) := by simp only [mul_assoc]
    _=_ := by simp only [←map_mul,single_mul_single_same,one_mul]

lemma central_of_commutes_diagonal (c : A)
    (hc : ∀ x : Matrix I I ℂ,Commute (φ x) c)
    (hd : ∀ a : A,Commute (diagonal φ o a) c) (a : A) : Commute a c := by
  have hcorner (b : A) : Commute (φ (single o o 1)*b*φ (single o o 1)) c := by
    have he := ((hc (single o o 1)).mul_left (hd b)).mul_left (hc (single o o 1))
    rwa [cut] at he
  have hblock (i j : I) : Commute (φ (single i i 1)*a*φ (single j j 1)) c := by
    have he := ((hc (single i o 1)).mul_left
      (hcorner (φ (single o i 1)*a*φ (single j o 1)))).mul_left (hc (single o j 1))
    rwa [matrix_block] at he
  have hs := Commute.sum_left Finset.univ
    (fun i => ∑ j,φ (single i i 1)*a*φ (single j j 1)) c
    (fun i _ => Commute.sum_left Finset.univ _ c (fun j _ => hblock i j))
  simpa only [←Finset.mul_sum,←Finset.sum_mul,←map_sum,sum_single_one,map_one,
    mul_one,one_mul] using hs

end Kadison.MatrixDiagonal

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixExpectation
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

open Matrix

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

lemma matrixSandwich (x : Matrix I I ℂ) (i j : I) :
    single i j 1*x*single j i 1=x j j • single i i 1 := by
  ext k l
  by_cases hik : i=k
  · subst k
    by_cases hil : i=l
    · subst l; simp [Matrix.mul_apply,Matrix.single,smul_eq_mul]
    · simp [Matrix.mul_apply,Matrix.single,smul_eq_mul,hil]
  · simp [Matrix.mul_apply,Matrix.single,smul_eq_mul,hik]

lemma matrixSum (x : Matrix I I ℂ) :
    (∑ i,∑ j,single i j 1*x*single j i 1)=x.trace • (1:Matrix I I ℂ) := by
  simp only [matrixSandwich,←Finset.sum_smul]
  simp only [Matrix.trace,Matrix.diag,←Finset.smul_sum,Matrix.sum_single_one]

variable [Nonempty I]

omit [DecidableEq I] in
lemma card_ne : (Fintype.card I:ℂ)≠0 := by exact_mod_cast Fintype.card_ne_zero

end Kadison.MatrixExpectation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixVectorTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

local instance matrixVectorTraceDecidableEq : DecidableEq ι := Classical.decEq ι

variable (τ : A →ₚ[ℂ] ℂ)

abbrev ArraySpace := PiLp 2 (fun _ : ι => PiLp 2 (fun _ : ι => τ.GNS))

def scale (ι : Type*) [Fintype ι] : ℂ := ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ)

lemma scale_ne_zero [Nonempty ι] : scale ι≠0 := by
  simp only [scale,ne_eq,Complex.ofReal_eq_zero,inv_eq_zero]
  exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast (Fintype.card_pos (α:=ι)))

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTraceFaithful
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

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

local instance instDecidableEq_solutions : DecidableEq ι := Classical.decEq ι

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixFlatten
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

local instance instDecidableEq_solutions_2 : DecidableEq κ := Classical.decEq κ

local instance instDecidableEqProd_solutions : DecidableEq (κ×ι) := Classical.decEq (κ×ι)

local instance instDecidableEq_solutions_1_r939659_1 : DecidableEq ι := Classical.decEq ι
def flattenHom : CStarMatrix κ κ (CStarMatrix ι ι A) →⋆ₐ[ℂ] CStarMatrix (κ×ι) (κ×ι) A where
  toFun X := CStarMatrix.ofMatrix (fun p q => X p.1 q.1 p.2 q.2)
  map_zero' := rfl
  map_add' X Y := rfl
  map_mul' X Y := by
    ext p q
    change (X*Y) p.1 q.1 p.2 q.2=∑ r : κ×ι,X p.1 r.1 p.2 r.2*Y r.1 q.1 r.2 q.2
    rw [CStarMatrix.mul_apply]
    change (∑ j, (X p.1 j * Y j q.1 : CStarMatrix ι ι A)) p.2 q.2=_
    have heval (Z : κ → CStarMatrix ι ι A) :
        (∑ j,Z j) p.2 q.2=∑ j,Z j p.2 q.2 := by
      suffices ∀ s : Finset κ,(∑ j ∈ s,Z j) p.2 q.2=∑ j∈s,Z j p.2 q.2 from
        this Finset.univ
      intro s
      induction s using Finset.induction_on with
      | empty => rfl
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha,Finset.sum_insert ha]
        change Z a p.2 q.2+(∑ j∈s,Z j) p.2 q.2=Z a p.2 q.2+_
        rw [ih]
    rw [heval]
    simp only [CStarMatrix.mul_apply,Fintype.sum_prod_type]
  map_one' := by
    ext p q
    change (1:CStarMatrix κ κ (CStarMatrix ι ι A)) p.1 q.1 p.2 q.2=
      (1:CStarMatrix (κ×ι) (κ×ι) A) p q
    by_cases hp : p.1=q.1 <;> by_cases hq : p.2=q.2 <;>
      simp [CStarMatrix.one_apply,hp,hq,Prod.ext_iff]
  commutes' z := by
    ext p q
    change (algebraMap ℂ (CStarMatrix κ κ (CStarMatrix ι ι A)) z) p.1 q.1 p.2 q.2=
      (algebraMap ℂ (CStarMatrix (κ×ι) (κ×ι) A) z) p q
    by_cases hp : p.1=q.1 <;> by_cases hq : p.2=q.2 <;>
      simp [CStarMatrix.algebraMap_apply,hp,hq,Prod.ext_iff]
  map_star' X := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma flattenHom_bijective : Function.Bijective (flattenHom (A:=A) ι κ) := by
  constructor
  · intro X Y h
    ext i j k l
    exact congrArg (fun Z : CStarMatrix (κ×ι) (κ×ι) A => Z (i,k) (j,l)) h
  · intro X
    refine ⟨CStarMatrix.ofMatrix (fun i j => CStarMatrix.ofMatrix (fun k l => X (i,k) (j,l))),?_⟩
    rfl

def flatten : CStarMatrix κ κ (CStarMatrix ι ι A) ≃⋆ₐ[ℂ] CStarMatrix (κ×ι) (κ×ι) A :=
  StarAlgEquiv.ofBijective (flattenHom ι κ) (flattenHom_bijective ι κ)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma flatten_apply (X : CStarMatrix κ κ (CStarMatrix ι ι A)) (p q : κ×ι) :
    flatten ι κ X p q=X p.1 q.1 p.2 q.2 := rfl

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixFlattenRepresentation
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

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance matrixFlattenRepresentationCopiesDecidableEq : DecidableEq κ := Classical.decEq κ

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNSUnitary
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

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

local instance matrixGNSUnitaryDecidableEq : DecidableEq ι := Classical.decEq ι

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixModules
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

abbrev corner : Submodule 𝕜 E := LinearMap.range (ρ (single o o 1))

noncomputable def coordinates (i : I) : E →ₗ[𝕜] corner ρ o :=
  (ρ (single o i 1)).codRestrict _ (fun x => by
    refine ⟨ρ (single o i 1) x, ?_⟩
    change (ρ (single o o 1) * ρ (single o i 1)) x = _
    rw [← map_mul, Matrix.single_mul_single_same, one_mul])

end Kadison.MatrixModules
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixRowCorner
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

variable {A ι : Type*} [CStarAlgebra A] [Fintype ι]

local instance matrixRowCornerDecidableEq : DecidableEq ι := Classical.decEq ι

def rowMatrix (i : ι) (a : A) : CStarMatrix ι ι A :=
  CStarMatrix.ofMatrix (fun j k => if j=i ∧ k=i then a else 0)

omit [Fintype ι] in
@[simp] lemma rowMatrix_apply (i : ι) (a : A) (j k : ι) :
    rowMatrix i a j k=if j=i ∧ k=i then a else 0 := rfl

end Kadison.MatrixGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionPartition
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

omit [StarRing R] in
lemma swap_middle (a b c d : R) (hc : Commute b c) :
    (a*b)*(c*d)=(a*c)*(b*d) := by
  calc
    (a*b)*(c*d)=a*((b*c)*d) := by simp only [mul_assoc]
    _=a*((c*b)*d) := by rw [hc.eq]
    _=(a*c)*(b*d) := by simp only [mul_assoc]

end Kadison.SpectralPartition

end

end
end

end OAI
end


