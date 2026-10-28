-- Prove2me | Definitions.Def_OAIQ039C010
-- name    : OAIQ039C010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:12:52.172991+00:00
-- url     : https://prove2.me/theorems/f74c3b7b-4bc2-43ad-84cd-ad60efdf9799
-- title:
--   Definitions bundle OAIQ039C010 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 96 declarations of OpenAI's Lean: 51 definitions, 4 inductive types or structures, 3 instances and 38 theorems. The definitions and types are `OAI.Kadison.FinitePatching.ConjugatedWords.front`, `OAI.Kadison.FinitePatching.ConjugatedWords.leftUnitary`, `OAI.Kadison.FinitePatching.ConjugatedWords.pair`, `OAI.Kadison.FinitePatching.ConjugatedWords.signPower`, `OAI.Kadison.FinitePatching.NonzeroInteger`, `OAI.Kadison.FinitePatching.SmallList`, `OAI.Kadison.FinitePatching.budgetSlope`, `OAI.Kadison.FinitePatching.cornerCenter`, `OAI.Kadison.FinitePatching.cornerScalar`, `OAI.Kadison.FinitePatching.integerEnumeration`, `OAI.Kadison.FinitePatching.listPool`, `OAI.Kadison.FinitePatching.momentBudget`, `OAI.Kadison.FinitePatching.smallList`, `OAI.Kadison.FinitePatching.wordProduct`, `OAI.Kadison.FiniteTest.familyHom`, `OAI.Kadison.FiniteTest.familyVector`, `OAI.Kadison.FiniteTest.traceSquare`, `OAI.Kadison.FiniteTest.vector`, `OAI.Kadison.FreeCorner.compress`, `OAI.Kadison.FreeMoments.Free`, `OAI.Kadison.FreeMoments.Letter`, `OAI.Kadison.FreeMoments.Letter.conj`, `OAI.Kadison.FreeMoments.Reduced`, `OAI.Kadison.FreeMoments.centerLetter`, `OAI.Kadison.FreeMoments.centeredPair`, `OAI.Kadison.FreeMoments.gram`, `OAI.Kadison.FreeMoments.paired`, `OAI.Kadison.FreeMoments.reverseStar`, `OAI.Kadison.FreeMoments.word`, `OAI.Kadison.FreeMoments.wordSpan`, `OAI.Kadison.FreeWordTensor.ColorSeq`, `OAI.Kadison.FreeWordTensor.FaithfulState`, `OAI.Kadison.FreeWordTensor.Params`, `OAI.Kadison.FreeWordTensor.Space`, `OAI.Kadison.FreeWordTensor.asLetter`, `OAI.Kadison.FreeWordTensor.letterSpace`, `OAI.Kadison.FreeWordTensor.letterValue`, `OAI.Kadison.FreeWordTensor.letters`, `OAI.Kadison.FreeWordTensor.preSpace`, `OAI.Kadison.FreeWordTensor.pure` and 15 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_AllUnitaryTests`, `Commutator_BoundedWordPool`, `Commutator_CoefficientForm`, `Commutator_ConjugatedFreeness`, `Commutator_ConjugatedWordAlgebra`, `Commutator_CornerCenteredEstimates`, `Commutator_ExponentialMomentBudget`, `Commutator_FiniteHankel`, `Commutator_FiniteTestPatching`, `Commutator_FiniteWordTelescoping`, `Commutator_FreeMoments`, `Commutator_FreeWordTensor`, `Commutator_HankelAlgebra`, `Commutator_HilbertTensors`, `Commutator_TensorCompletion`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C025`, `OAIQ039C026`, `OAIQ039C029` and `OAIQ039C030`; the statements `OAI.Kadison.FinitePatching.trace_centered_compression_bound`, `OAI.Kadison.FinitePatching.trace_word_second_order_bound`, `OAI.Kadison.FreeMoments.Free.mono`, `OAI.Kadison.PreHilbert.operator_ext_dense_stages`, `OAI.Kadison.finite_pairing_source_bound` and `OAI.Kadison.finite_pairing_test_bound`; the proofs of `OAI.Kadison.FinitePatching.trace_word_second_order_bound`, `OAI.Kadison.FreeMoments.Free.mono`, `OAI.Kadison.HilbertPadding.matrix_padding_commutator_norm`, `OAI.Kadison.HilbertPadding.norm_extend_commutator`, `OAI.Kadison.MatrixModule.endpoint_unit_bound`, `OAI_Kadison_OrbitStateHull_exists_faithful_normal_trace` and `OAI_Kadison_TracialGNS_actual_block_classification`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerCenteredEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

def cornerScalar (p b : A) : ℂ := τ (p*b)/τ p

def cornerCenter (p b : A) : A := p*b*p-cornerScalar τ p b • p

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteWordTelescoping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators

namespace Kadison.FinitePatching

variable {A I : Type*} [NormedRing A]

def wordProduct (a : I → A) (l : List I) : A := (l.map a).prod

@[simp] lemma wordProduct_nil (a : I → A) : wordProduct a []=1 := rfl

@[simp] lemma wordProduct_cons (a : I → A) (i : I) (l : List I) :
    wordProduct a (i::l)=a i*wordProduct a l := rfl

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ExponentialMomentBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FinitePatching

def momentBudget (ε K t : ℝ) : ℝ := ε*Real.exp (K*t)

def budgetSlope (N : ℕ) (η : ℝ) : ℝ := ((N:ℝ)+1)^2*(1+2/η)

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_BoundedWordPool
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FinitePatching

variable (I : Type*) [Fintype I]

def listPool (N : ℕ) : Finset (List I) := by
  classical
  exact Finset.univ.biUnion (fun n : Fin (N+1) =>
    Finset.univ.image (fun f : Fin n → I => List.ofFn f))

lemma mem_listPool (N : ℕ) (l : List I) : l∈listPool I N ↔ l.length ≤ N := by
  classical
  constructor
  · intro h
    simp only [listPool,Finset.mem_biUnion,Finset.mem_univ,Finset.mem_image,true_and] at h
    obtain ⟨n,f,rfl⟩ := h
    simpa only [List.length_ofFn] using Nat.le_of_lt_succ n.isLt
  · intro h
    simp only [listPool,Finset.mem_biUnion,Finset.mem_univ,Finset.mem_image,true_and]
    exact ⟨⟨l.length,Nat.lt_succ_of_le h⟩,l.get,List.ofFn_get l⟩

abbrev SmallList (N : ℕ) := ↥(listPool I N)

def smallList {N : ℕ} (l : List I) (h : l.length ≤ N) : SmallList I N :=
  ⟨l,(mem_listPool I N l).mpr h⟩

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteTestPatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Kadison.FiniteTest

section MatrixAlgebra

open Matrix

variable {A I : Type*} [CStarAlgebra A] [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

def traceSquare (τ : A →ₗ[ℝ] ℝ) (x : A) : ℝ := τ (star x * x)

end MatrixAlgebra

section FiniteFamily

open Matrix

variable {A I J H : Type*} [CStarAlgebra A] [Fintype I] [LinearOrder I]
  [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A) (τ : A →ₗ[ℝ] ℝ)
  (hτ : ∀ a b : A, τ (a*b) = τ (b*a))
  (v : A →ₗ[ℝ] H) (hv : ∀ a, ‖v a‖^2 = traceSquare τ a)

def familyVector : (J → A) →ₗ[ℝ] PiLp 2 (fun _ : J => H) :=
  (WithLp.linearEquiv 2 ℝ (J → H)).symm.toLinearMap.comp
    (LinearMap.pi (fun j => v.comp (LinearMap.proj j)))

omit [Fintype J] in
@[simp] lemma familyVector_apply (x : J → A) (j : J) :
    (familyVector v x).ofLp j = v (x j) := rfl

def familyHom : Matrix I I ℂ →⋆ₐ[ℂ] (J → A) :=
  ({ Pi.constAlgHom ℂ J A with map_star' := fun _ => rfl } : A →⋆ₐ[ℂ] (J → A)).comp φ

omit [Fintype J] in
@[simp] lemma familyHom_apply (a : Matrix I I ℂ) (j : J) : familyHom φ a j = φ a := rfl

end FiniteFamily

section ActualGNS

open scoped ComplexOrder

open UniformSpace

variable {A I J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype I] [LinearOrder I] [Fintype J]

variable (τ : A →ₚ[ℂ] ℂ)

def vector : A →ₗ[ℝ] τ.GNS :=
  ((Completion.toComplL : τ.PreGNS →L[ℂ] τ.GNS).toLinearMap.comp
    τ.toPreGNS.toLinearMap).restrictScalars ℝ

@[simp] lemma vector_apply (a : A) : vector τ a = (τ.toPreGNS a : τ.GNS) := rfl

end ActualGNS

end Kadison.FiniteTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_AllUnitaryTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Topology

open Filter

namespace Kadison.FinitePatching

abbrev NonzeroInteger := {k : ℤ // k≠0}

def integerEnumeration : ℕ → NonzeroInteger :=
  letI := Encodable.ofCountable NonzeroInteger
  fun n => (Encodable.decode (α:=NonzeroInteger) n).getD ⟨1,by norm_num⟩

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HilbertTensors
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

namespace Kadison

structure PreHilbert where
  carrier : Type
  [normed : NormedAddCommGroup carrier]
  [ipSpace : InnerProductSpace ℂ carrier]

attribute [instance] PreHilbert.normed PreHilbert.ipSpace

instance instCoeSortPreHilbertType : CoeSort PreHilbert Type := ⟨PreHilbert.carrier⟩

namespace PreHilbert

abbrev scalar : PreHilbert := ⟨ℂ⟩

abbrev tensor (E F : PreHilbert) : PreHilbert := ⟨E ⊗[ℂ] F⟩

@[reducible] def power (E : PreHilbert) : ℕ → PreHilbert
  | 0 => scalar
  | n + 1 => tensor E (power E n)

def pure (E : PreHilbert) : ∀ n, (Fin n → E) → power E n
  | 0, _ => (1 : ℂ)
  | n + 1, v => v 0 ⊗ₜ[ℂ] pure E n (Fin.tail v)

@[simp] theorem pure_zero (E : PreHilbert) (v : Fin 0 → E) :
    pure E 0 v = (1 : ℂ) := rfl

@[simp] theorem pure_succ (E : PreHilbert) (n : ℕ) (v : Fin (n+1) → E) :
    pure E (n+1) v = v 0 ⊗ₜ[ℂ] pure E n (Fin.tail v) := rfl

@[simp] theorem norm_pure (E : PreHilbert) (n : ℕ) (v : Fin n → E) :
    ‖pure E n v‖ = ∏ i, ‖v i‖ := by
  induction n with
  | zero => simp [pure, power, scalar]
  | succ n ih =>
    rw [pure_succ, TensorProduct.norm_tmul, ih, Fin.prod_univ_succ]
    rfl

@[simp] theorem inner_pure (E : PreHilbert) (n : ℕ) (v w : Fin n → E) :
    inner ℂ (pure E n v) (pure E n w) = ∏ i, inner ℂ (v i) (w i) := by
  induction n with
  | zero => simp [pure, power, scalar]
  | succ n ih =>
    rw [pure_succ, pure_succ, TensorProduct.inner_tmul, ih, Fin.prod_univ_succ]
    rfl

end PreHilbert

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CoefficientForm
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

namespace Kadison.PreHilbert

open UniformSpace Function

abbrev wordSpace (E F : PreHilbert) (n : ℕ) := Completion (E ⊗[ℂ] power F n)

def word (E F : PreHilbert) (n : ℕ) (d : E) (x : Fin n → F) : wordSpace E F n :=
  (d ⊗ₜ[ℂ] pure F n x : E ⊗[ℂ] power F n)

end Kadison.PreHilbert
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ConjugatedWordAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.ConjugatedWords

variable {B J : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def signPower (c : Bool) : ℤ := if c then 1 else -1

def leftUnitary (u : unitary B) (c : Bool) : unitary B := if c then 1 else u

def front (color : J → Bool) (σ : Bool) : List J → Bool
  | [] => σ
  | a::_ => color a

end Kadison.FinitePatching.ConjugatedWords

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeMoments
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
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.FreeMoments

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

structure Letter where
  color : ι
  val : A
  mem : val ∈ S color
  centered : τ val = 0

variable {S τ}

def word (w : List (Letter S τ)) : A := (w.map Letter.val).prod

def Reduced (w : List (Letter S τ)) : Prop :=
  w.IsChain (fun a b => a.color ≠ b.color)

def Free (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ) : Prop :=
  ∀ w : List (Letter S τ), Reduced w → w ≠ [] → τ (word w) = 0

@[simp] lemma word_nil : word ([] : List (Letter S τ)) = 1 := rfl

@[simp] lemma word_cons (a : Letter S τ) (w : List (Letter S τ)) :
    word (a :: w) = a.val * word w := rfl

@[simp] lemma word_append (w z : List (Letter S τ)) :
    word (w ++ z) = word w * word z := by simp [word, List.prod_append]

@[simp] lemma reduced_nil : Reduced ([] : List (Letter S τ)) := List.isChain_nil

@[simp] lemma reduced_singleton (a : Letter S τ) : Reduced [a] := List.IsChain.singleton a

lemma Reduced.tail {a : Letter S τ} {w : List (Letter S τ)}
    (h : Reduced (a :: w)) : Reduced w := List.IsChain.tail h

variable (hstar : ∀ a : A, τ (star a) = star (τ a))

def Letter.conj (a : Letter S τ) : Letter S τ where
  color := a.color
  val := star a.val
  mem := star_mem a.mem
  centered := by rw [hstar, a.centered, star_zero]

@[simp] lemma star_color (a : Letter S τ) : (a.conj hstar).color = a.color := rfl

@[simp] lemma star_val (a : Letter S τ) : (a.conj hstar).val = star a.val := rfl

def reverseStar (w : List (Letter S τ)) : List (Letter S τ) :=
  (w.map (Letter.conj hstar)).reverse

@[simp] lemma word_reverseStar (w : List (Letter S τ)) :
    word (reverseStar hstar w) = star (word w) := by
  induction w with
  | nil => simp [reverseStar]
  | cons a w ih =>
    rw [show reverseStar hstar (a :: w) = reverseStar hstar w ++ [a.conj hstar] by
      simp only [reverseStar, List.map_cons, List.reverse_cons]]
    simp [ih, star_mul]

lemma Reduced.reverseStar {w : List (Letter S τ)} (h : Reduced w) :
    Reduced (reverseStar hstar w) := by
  apply List.isChain_reverse.mpr
  apply (List.isChain_map _).mpr
  exact h.imp (fun _ _ hab => hab.symm)

lemma reduced_join {a b : Letter S τ} {w z : List (Letter S τ)}
    (hw : Reduced (a :: w)) (hz : Reduced (b :: z)) (hab : a.color ≠ b.color) :
    Reduced (reverseStar hstar (a :: w) ++ b :: z) := by
  apply (Reduced.reverseStar hstar hw).append hz
  intro x hx y hy
  simp only [List.head?_cons, Option.mem_some_iff] at hy
  subst y
  have hx' : x = a.conj hstar := by
    exact (by simpa [reverseStar, List.getLast?_reverse] using hx : _ = x).symm
  subst x
  exact hab

include hstar in
lemma gram_different_head (hfree : Free S τ) {a b : Letter S τ}
    {w z : List (Letter S τ)} (hw : Reduced (a :: w)) (hz : Reduced (b :: z))
    (hab : a.color ≠ b.color) :
    τ (star (word (a :: w)) * word (b :: z)) = 0 := by
  have h := hfree (reverseStar hstar (a :: w) ++ b :: z)
    (reduced_join hstar hw hz hab) (by simp)
  simpa using h

variable (h1 : τ 1 = 1)

def centeredPair (a b : Letter S τ) (hab : a.color = b.color) : Letter S τ where
  color := a.color
  val := star a.val * b.val - τ (star a.val * b.val) • (1 : A)
  mem := sub_mem
    (mul_mem (star_mem a.mem) (by simpa [hab] using b.mem))
    (SMulMemClass.smul_mem _ (one_mem (S a.color)))
  centered := by simp [map_sub, map_smul, h1]

lemma reduced_pair_join {a b : Letter S τ} {w z : List (Letter S τ)}
    (hw : Reduced (a :: w)) (hz : Reduced (b :: z)) (hab : a.color = b.color) :
    Reduced (reverseStar hstar w ++ centeredPair h1 a b hab :: z) := by
  have hz' : Reduced (centeredPair h1 a b hab :: z) := by
    apply hz.imp_head
    intro c hc
    exact hab ▸ hc
  apply (Reduced.reverseStar hstar hw.tail).append hz'
  intro x hx y hy
  simp only [List.head?_cons, Option.mem_some_iff] at hy
  subst y
  cases w with
  | nil => simp [reverseStar] at hx
  | cons c w =>
    have hx' : x = c.conj hstar := by
      exact (by simpa [reverseStar, List.getLast?_reverse] using hx : _ = x).symm
    subst x
    exact hw.rel.symm

include hstar h1 in
lemma gram_same_head (hfree : Free S τ) {a b : Letter S τ}
    {w z : List (Letter S τ)} (hw : Reduced (a :: w)) (hz : Reduced (b :: z))
    (hab : a.color = b.color) :
    τ (star (word (a :: w)) * word (b :: z)) =
      τ (star a.val * b.val) * τ (star (word w) * word z) := by
  have h := hfree (reverseStar hstar w ++ centeredPair h1 a b hab :: z)
    (reduced_pair_join hstar h1 hw hz hab) (by simp)
  have hid : star (word w) * (star a.val * b.val - τ (star a.val * b.val) • (1 : A)) * word z =
      star (word (a :: w)) * word (b :: z) -
        τ (star a.val * b.val) • (star (word w) * word z) := by
    simp only [word_cons, star_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      mul_one, mul_assoc]
  simp only [word_append, word_reverseStar, word_cons, centeredPair] at h
  rw [← mul_assoc, hid, map_sub, map_smul] at h
  exact sub_eq_zero.mp h

def gram : List (Letter S τ) → List (Letter S τ) → ℂ
  | [], [] => 1
  | [], _ :: _ => 0
  | _ :: _, [] => 0
  | a :: w, b :: z => if a.color = b.color then τ (star a.val * b.val) * gram w z else 0

def centerLetter (i : ι) (a : A) (ha : a ∈ S i) : Letter S τ where
  color := i
  val := a - τ a • (1 : A)
  mem := sub_mem ha (SMulMemClass.smul_mem _ (one_mem (S i)))
  centered := by simp [map_sub, map_smul, h1]

def wordSpan (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ) : Submodule ℂ A :=
  Submodule.span ℂ {a | ∃ w : List (Letter S τ), Reduced w ∧ word w = a}

lemma word_mem_span {w : List (Letter S τ)} (hw : Reduced w) :
    word w ∈ wordSpan S τ := Submodule.subset_span ⟨w, hw, rfl⟩

lemma one_mem_wordSpan : (1 : A) ∈ wordSpan S τ :=
  word_mem_span (w := []) reduced_nil

end Kadison.FreeMoments
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ConjugatedFreeness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.ConjugatedWords

variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (φ : A →⋆ₐ[ℂ] B) (u : unitary B)

def pair (c : Bool) : StarSubalgebra ℂ B :=
  if c then φ.range else ((Unitary.conjStarAlgAut ℂ B u).toStarAlgHom.comp φ).range

end Kadison.FinitePatching.ConjugatedWords

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteHankel
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

namespace Kadison.FreeCorner

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def compress (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) : K →L[ℂ] K :=
  (V.toContinuousLinearMap.adjoint.comp T).comp V.toContinuousLinearMap

end Kadison.FreeCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeWordTensor
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
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace

namespace Kadison.FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

structure FaithfulState (A : Type) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  functional : A →ₚ[ℂ] ℂ
  normalized : functional 1 = 1
  faithful : ∀ a : A, functional (star a * a) = 0 → a = 0

variable (t : FaithfulState A)

abbrev preSpace := t.functional.PreGNS

noncomputable instance faithfulNormed : NormedAddCommGroup (preSpace t) :=
  NormedAddCommGroup.ofSeparation fun x hx => by
    apply t.functional.ofPreGNS.injective
    change t.functional.ofPreGNS x = 0
    apply t.faithful
    have hs := t.functional.preGNS_norm_sq x
    rw [hx] at hs
    simpa using hs.symm

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A)

def letterSpace (i : ι) : Submodule ℂ (preSpace t) where
  carrier := {x | t.functional.ofPreGNS x ∈ S i ∧ t.functional (t.functional.ofPreGNS x) = 0}
  zero_mem' := by simp
  add_mem' := by rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩; simp [map_add, add_mem hx hy, hx0, hy0]
  smul_mem' := by
    rintro c x ⟨hx, hx0⟩
    exact ⟨by simpa using SMulMemClass.smul_mem c hx, by simp [hx0]⟩

def letterValue (i : ι) : letterSpace t S i →ₗ[ℂ] A :=
  t.functional.ofPreGNS.toLinearMap.comp (letterSpace t S i).subtype

def asLetter (i : ι) (x : letterSpace t S i) : FreeMoments.Letter S t.functional.toLinearMap where
  color := i
  val := letterValue t S i x
  mem := x.property.1
  centered := x.property.2

structure Space where
  carrier : Type
  [normed : NormedAddCommGroup carrier]
  [inner : InnerProductSpace ℂ carrier]

attribute [instance] Space.normed Space.inner

instance instCoeSortSpaceType : CoeSort Space Type := ⟨Space.carrier⟩

@[reducible] noncomputable def tensor : List ι → Space
  | [] => ⟨ℂ⟩
  | i :: is => ⟨letterSpace t S i ⊗[ℂ] tensor is⟩

@[reducible] def Params : List ι → Type
  | [] => PUnit
  | i :: is => letterSpace t S i × Params is

noncomputable def pure : ∀ is, Params t S is → tensor t S is
  | [], _ => (1 : ℂ)
  | _ :: is, x => x.1 ⊗ₜ[ℂ] pure is x.2

def letters : ∀ is, Params t S is → List (FreeMoments.Letter S t.functional.toLinearMap)
  | [], _ => []
  | i :: is, x => asLetter t S i x.1 :: letters is x.2

@[simp] lemma letters_colors : ∀ is (x : Params t S is),
    (letters t S is x).map FreeMoments.Letter.color = is
  | [], _ => rfl
  | _ :: is, x => by simp [letters, asLetter, letters_colors is x.2]

lemma letters_reduced (is : List ι) (x : Params t S is) (his : is.IsChain (· ≠ ·)) :
    FreeMoments.Reduced (letters t S is x) := by
  rw [← letters_colors t S is x] at his
  exact (List.isChain_map _).mp his

noncomputable def read : ∀ is, tensor t S is →ₗ[ℂ] A
  | [] => Algebra.linearMap ℂ A
  | i :: is => (TensorProduct.lift (LinearMap.mul ℂ A)).comp
      (TensorProduct.map (letterValue t S i) (read is))

@[simp] lemma read_pure : ∀ is (x : Params t S is),
    read t S is (pure t S is x) = FreeMoments.word (letters t S is x)
  | [], _ => by
    change algebraMap ℂ A 1 = 1
    exact map_one _
  | i :: is, x => by
    change letterValue t S i x.1 * read t S is (pure t S is x.2) =
      letterValue t S i x.1 * FreeMoments.word (letters t S is x.2)
    rw [read_pure is x.2]

lemma span_pure (is : List ι) :
    Submodule.span ℂ (Set.range (pure t S is)) = ⊤ := by
  induction is with
  | nil =>
    apply Submodule.eq_top_iff'.mpr
    intro z
    have h : (1 : ℂ) ∈ Submodule.span ℂ (Set.range (pure t S [])) :=
      Submodule.subset_span ⟨PUnit.unit, rfl⟩
    simpa using (Submodule.span ℂ (Set.range (pure t S []))).smul_mem z h
  | cons i is ih =>
    apply Submodule.eq_top_iff'.mpr
    intro z
    induction z using OAI.tensorInductionOn with
    | add x y hx hy => exact Submodule.add_mem _ hx hy
    | tmul x y =>
      have hy : y ∈ Submodule.span ℂ (Set.range (pure t S is)) := by rw [ih]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, rfl⟩ := hy
        exact Submodule.subset_span ⟨(x,v), rfl⟩
      | zero => simp only [TensorProduct.tmul_zero, Submodule.zero_mem]
      | add y z _ _ hy hz =>
        simpa only [TensorProduct.tmul_add] using
          (Submodule.span ℂ (Set.range (pure t S (i::is)))).add_mem hy hz
      | smul c y _ hy =>
        simpa only [TensorProduct.tmul_smul] using
          (Submodule.span ℂ (Set.range (pure t S (i::is)))).smul_mem c hy

lemma inner_letter (i : ι) (x y : letterSpace t S i) :
    inner ℂ x y = t.functional (star (letterValue t S i x) * letterValue t S i y) := by
  rfl

lemma inner_pure : ∀ is (x y : Params t S is),
    inner ℂ (pure t S is x) (pure t S is y) =
      FreeMoments.gram (letters t S is x) (letters t S is y)
  | [], _, _ => by simp [pure, letters, FreeMoments.gram]
  | i :: is, x, y => by
    change inner ℂ (x.1 ⊗ₜ[ℂ] pure t S is x.2) (y.1 ⊗ₜ[ℂ] pure t S is y.2) = _
    rw [TensorProduct.inner_tmul, inner_pure is x.2 y.2, inner_letter]
    simp [FreeMoments.gram, letters, asLetter]

noncomputable def readPre (is : List ι) : tensor t S is →ₗ[ℂ] preSpace t :=
  t.functional.toPreGNS.toLinearMap.comp (read t S is)

@[simp] lemma readPre_pure (is : List ι) (x : Params t S is) :
    readPre t S is (pure t S is x) =
      t.functional.toPreGNS (FreeMoments.word (letters t S is x)) := by
  change t.functional.toPreGNS (read t S is (pure t S is x)) = _
  rw [read_pure]

variable (hfree : FreeMoments.Free S t.functional.toLinearMap)

include hfree

def ColorSeq (ι : Type*) := {is : List ι // is.IsChain (· ≠ ·)}

end Kadison.FreeWordTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

def paired (s : Letter S τ) (v : List (Letter S τ)) : List (Letter S τ) :=
  v.flatMap (fun a => [a,s])

end Kadison.FreeMoments

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TensorCompletion
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
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.HilbertCompletion

variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def coeIsometry (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    E →ₗᵢ[ℂ] Completion E where
  toLinearMap := (Completion.toComplL : E →L[ℂ] Completion E).toLinearMap
  norm_map' := Completion.norm_coe

def map (U : E →ₗᵢ[ℂ] F) : Completion E →ₗᵢ[ℂ] Completion F where
  toLinearMap := U.toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp

@[simp] lemma map_coe (U : E →ₗᵢ[ℂ] F) (x : E) : map U (x : Completion E) = (U x : Completion F) := by
  simp [map]

def congr (U : E ≃ₗᵢ[ℂ] F) : Completion E ≃ₗᵢ[ℂ] Completion F :=
  LinearIsometryEquiv.ofSurjective (map U.toLinearIsometry) (by
    intro y
    refine ⟨map U.symm.toLinearIsometry y, ?_⟩
    induction y using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih y => simp)

@[simp] lemma congr_coe (U : E ≃ₗᵢ[ℂ] F) (x : E) : congr U (x : Completion E) = (U x : Completion F) :=
  map_coe U.toLinearIsometry x

def tensorMap : Completion (E ⊗[ℂ] F) →ₗᵢ[ℂ] Completion (Completion E ⊗[ℂ] Completion F) :=
  map (TensorProduct.mapIsometry (coeIsometry E) (coeIsometry F))

@[simp] lemma tensorMap_coe_tmul (x : E) (y : F) :
    tensorMap (E := E) (F := F) ((x ⊗ₜ[ℂ] y) : Completion (E ⊗[ℂ] F)) =
      (((x : Completion E) ⊗ₜ[ℂ] (y : Completion F)) : Completion (Completion E ⊗[ℂ] Completion F)) := by
  simp [tensorMap, coeIsometry]

def leftSwap : E ⊗[ℂ] (F ⊗[ℂ] G) ≃ₗᵢ[ℂ] F ⊗[ℂ] (E ⊗[ℂ] G) :=
  (TensorProduct.assocIsometry ℂ E F G).symm |>.trans
    (TensorProduct.congrIsometry (TensorProduct.commIsometry ℂ E F) (.refl ℂ G)) |>.trans
      (TensorProduct.assocIsometry ℂ F E G)

@[simp] lemma leftSwap_tmul (x : E) (y : F) (z : G) :
    leftSwap (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z)) = y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] z) := by
  simp [leftSwap]

end Kadison.HilbertCompletion
end

end OAI
end


