-- Prove2me | Definitions.Def_OAIQ368Chrom018
-- name    : OAIQ368Chrom018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T18:05:40.13243+00:00
-- url     : https://prove2.me/theorems/829c6c0a-4610-4500-9bfb-f2e264b0ee93
-- title:
--   Definitions bundle OAIQ368Chrom018 of the split of OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 37 declarations of OpenAI's Lean: 24 definitions, 1 inductive type or structure, 3 instances and 9 theorems. The definitions and types are `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.inverseExponent`, `OAI.ElementaryPositivity.RawShuffle.SplitTree`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.dim`, `OAI.ElementaryPositivity.RawShuffle.SplitTree.extendPolynomial`, `OAI.ElementaryPositivity.RawShuffle.crossInteraction`, `OAI.ElementaryPositivity.RawShuffle.elementaryDiagonal`, `OAI.ElementaryPositivity.RawShuffle.geometricQuiver`, `OAI.ElementaryPositivity.RawShuffle.literalAxis`, `OAI.ElementaryPositivity.RawShuffle.literalAxisScalar`, `OAI.ElementaryPositivity.RawShuffle.literalInputCoefficient`, `OAI.ElementaryPositivity.RawShuffle.packEmbedding`, `OAI.ElementaryPositivity.RawShuffle.polynomialCoeffLinear`, `OAI.ElementaryPositivity.RawShuffle.relativeRaw`, `OAI.ElementaryPositivity.RawShuffle.rootSum`, `OAI.ElementaryPositivity.RootTruncation.patchTop`, `OAI.ElementaryPositivity.WeightedTorusSeries.Slice`, `OAI.ElementaryPositivity.WeightedTorusSeries.Supported`, `OAI.ElementaryPositivity.WeightedTorusSeries.instRingTorus`, `OAI.ElementaryPositivity.WeightedTorusSeries.pairSliceEquiv`, `OAI.ElementaryPositivity.WeightedTorusSeries.partialCoefficient`, `OAI.ElementaryPositivity.WeightedTorusSeries.push`, `OAI.ElementaryPositivity.WeightedTorusSeries.pushCoeff`, `OAI.ElementaryPositivity.WeightedTorusSeries.restrictDim`, `OAI.ElementaryPositivity.WeightedTorusSeries.supportedCoefficient`, `OAI.ElementaryPositivity.WeightedTorusSeries.weight`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `Chromatic_GradedAlgebra_HNSeries`, `Chromatic_GradedAlgebra_InputOrderedProduct`, `Chromatic_GradedAlgebra_SupportedConvolution`, `Chromatic_GradedAlgebra_WeightedTorusSeries`, `Chromatic_Shuffle_CrossDifference`, `Chromatic_Shuffle_ExtendPolynomial`, `Chromatic_Shuffle_HNSlope`, `Chromatic_Shuffle_InputProduct`, `Chromatic_Shuffle_InputTorusEnergy`, `Chromatic_Shuffle_LabeledPolynomial`, `Chromatic_Shuffle_LaurentKernel`, `Chromatic_Shuffle_PrimitiveUnitRows`, `Chromatic_Shuffle_QuotientAlg`, `Chromatic_Shuffle_RestrictionB`, `Chromatic_Walls_DegreeIsolatedReordering`, `Chromatic_Walls_Mass`, `Chromatic_Walls_PolynomialCoeffLinear`.
--
--   **Imports.** It imports the bundle `OAIQ368Chrom001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ368Chrom019`, `OAIQ368Chrom020`, `OAIQ368Chrom021` and `OAIQ368Chrom073`.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit 7ef5c0c

import Mathlib
import Definitions.Def_OAIQ368Chrom001

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_WeightedTorusSeries
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

def weight : (I → ℕ) →+ ℕ where
  toFun d:=∑i,d i*w i
  map_zero':=by simp
  map_add' d e:=by simp [add_mul,Finset.sum_add_distrib]

omit [DecidableEq I] in
include hw in
lemma coord_le_weight (d : I → ℕ) (i : I) : d i≤weight w d :=
  (Nat.le_mul_of_pos_right _ (hw.out i)).trans
    (Finset.single_le_sum (fun j _=>Nat.zero_le (d j*w j)) (Finset.mem_univ i))

abbrev Slice (n : ℕ) := {d : I → ℕ // weight w d=n}
instance sliceFinite (n : ℕ) : Finite (Slice w n) :=
  Finite.of_injective (fun d : Slice w n=>fun i=>(⟨d.val i,by
    have H:=coord_le_weight w d.val i
    rw [d.property] at H
    omega⟩ : Fin (n+1))) (fun x y h=>Subtype.ext (funext (fun i=>congrArg Fin.val (congrArg (fun f=>f i) h))))

noncomputable instance sliceFintype (n : ℕ) : Fintype (Slice w n) := Fintype.ofFinite _

def pairSliceEquiv (n : ℕ) :
    (Σ k : Fin (n+1),Slice w k.val × Slice w (n-k.val)) ≃
      {p : (I→ℕ)×(I→ℕ) // weight w p.1+weight w p.2=n} where
  toFun x:=⟨(x.2.1.val,x.2.2.val),by rw [x.2.1.property,x.2.2.property]; omega⟩
  invFun p:=⟨⟨weight w p.val.1,by have H:=p.property; omega⟩,⟨p.val.1,rfl⟩,
    ⟨p.val.2,by dsimp only; have H:=p.property; omega⟩⟩
  left_inv x:=by
    rcases x with ⟨⟨k,hk⟩,⟨d,hd⟩,⟨e,he⟩⟩
    dsimp only at hd he ⊢
    subst k
    rfl
  right_inv p:=rfl

variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
local instance instRingTorus : Ring (Torus v Ω) := Torus.instRing v Ω

attribute [local instance] OAI.ElementaryPositivity.WeightedTorusSeries.instAddCommMonoidTorus
local instance instAddGroupTorus_rbf0789_1 : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
def pushCoeff (f : (I→ℕ) → R) (n : ℕ) : Torus v Ω :=
  ∑d : Slice w n,Torus.monomial v Ω (P d.val) (f d.val)
def push (f : (I→ℕ) → R) : PowerSeries (Torus v Ω) := mk (pushCoeff w v Ω P f)

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_QuotientAlg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma eval_map_rat {R T : Type*} [Semiring R] [Semiring T] [Algebra ℚ R] [Algebra ℚ T]
    (φ : R →ₐ[ℚ] T) (p : Polynomial R) (t : ℚ) :
    (Polynomial.map φ.toRingHom p).eval (algebraMap ℚ T t) =
      φ (p.eval (algebraMap ℚ R t)) := by
  rw [Polynomial.eval_map]
  calc
    _ = Polynomial.eval₂ φ.toRingHom (φ (algebraMap ℚ R t)) p :=
      congrArg (fun x => Polynomial.eval₂ φ.toRingHom x p) (φ.commutes t).symm
    _ = _ := Polynomial.eval₂_at_apply φ.toRingHom (algebraMap ℚ R t)

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_CrossDifference
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def relativeRaw (d e : I → ℕ) :
    MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ →ₐ[ℚ]
      Polynomial (MvPolynomial ((Σi,Fin (d i)) ⊕ (Σi,Fin (e i))) ℚ) :=
  aeval (Sum.elim (fun x => Polynomial.C (X (Sum.inl x)) + Polynomial.X)
    (fun y => Polynomial.C (X (Sum.inr y))))

omit [Fintype I] [DecidableEq I] in
lemma relativeRaw_right (d e : I → ℕ) (f : MvPolynomial (Σi,Fin (e i)) ℚ) :
    relativeRaw d e (rename Sum.inr f) = Polynomial.C (rename Sum.inr f) := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [relativeRaw]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f i hf =>
    simp only [map_mul,rename_X,hf]
    congr 1
    simp [relativeRaw]

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LabeledPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A B : I → Type*} [∀ i,DecidableEq (A i)] [∀ i,DecidableEq (B i)]

def packEmbedding (φ : ∀ i,A i ↪ B i) : (Σi,A i) ↪ (Σi,B i) :=
  Function.Embedding.sigmaMap (Function.Embedding.refl I) φ

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_Mass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I]

omit [Fintype I] in
lemma add_ne_zero_left (d e : I → ℕ) (hd : d ≠ 0) : d+e ≠ 0 := by
  intro h
  apply hd
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply,Pi.zero_apply] at hi
  change d i = 0
  omega

omit [Fintype I] in
lemma add_ne_zero_right (d e : I → ℕ) (he : e ≠ 0) : d+e ≠ 0 := by
  rw [add_comm]
  exact add_ne_zero_left e d he

end ElementaryPositivity.SlopeArithmetic

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_RestrictionB
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open ElementaryPositivity.SlopeArithmetic
open scoped TensorProduct
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]

inductive SplitTree (I : Type u) where
  | leaf (d : I → ℕ)
  | node (l r : SplitTree I)

namespace SplitTree

@[reducible] def dim : SplitTree I → I → ℕ
  | .leaf d => d
  | .node l r => l.dim + r.dim

end SplitTree
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_LaurentKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open scoped TensorProduct
namespace SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]

def inverseExponent (a : I → I → ℕ) (i j : I) : ℤ :=
  (if i=j then 1 else 0)-(a i j:ℤ)

end SeparationInfinity
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_ExtendPolynomial
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle.SplitTree
open MvPolynomial
open scoped TensorProduct

noncomputable def extendPolynomial {A B α β : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B) (j : α → β) :
    MvPolynomial α A →ₐ[ℚ] MvPolynomial β B :=
  ((rename j).restrictScalars ℚ).comp (mapAlgHom f)

@[simp] lemma extendPolynomial_C {A B α β : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B) (j : α → β) (a : A) :
    extendPolynomial f j (C a) = C (f a) := by
  simp [extendPolynomial]

@[simp] lemma extendPolynomial_X {A B α β : Type*} [CommRing A] [CommRing B]
    [Algebra ℚ A] [Algebra ℚ B] (f : A →ₐ[ℚ] B) (j : α → β) (i : α) :
    extendPolynomial f j (X i) = X (j i) := by
  simp [extendPolynomial]

end ElementaryPositivity.RawShuffle.SplitTree

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_PolynomialCoeffLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def polynomialCoeffLinear (R : Type*) [CommRing R] [Algebra ℚ R] (s : ℕ) :
    Polynomial R →ₗ[ℚ] R where
  toFun p := p.coeff s
  map_add' p q := Polynomial.coeff_add p q s
  map_smul' r p := by simp

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_PrimitiveUnitRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (ε : I → Bool) (d : I → ℕ)

def elementaryDiagonal (i : I) : ℕ := if ε i then 0 else 1

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InputTorusEnergy
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (κ : I → ℤ)

def crossInteraction (d : I → ℕ) : ℤ :=
  (∑ i,∑ j,(a i j:ℤ)*d i*d j)-∑ i,(a i i:ℤ)*(d i:ℤ)^2

end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_HNSlope
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open UnitSelections WallUnits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I]
variable (a : I → I → ℕ) (κ : I → ℤ) (ε : I → Bool)

def literalInputCoefficient (d : I → ℕ) : LaurentSeries ℚ :=
  (∏i,LaurentRay.atInfinity (PowerSeries.coeff (d i) (indexedUnit (elementaryDiagonal ε i) (κ i)))) *
      HahnSeries.single (-crossInteraction a d) 1

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_HNSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle ElementaryPositivity.QuantumTorus PowerSeries
noncomputable section
universe u
variable {I : Type u} [Fintype I]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]

lemma weight_eq_zero_iff (d : I → ℕ) : weight w d=0 ↔ d=0 := by
  constructor
  · intro H
    funext i
    have h:=coord_le_weight w d i
    rw [H] at h
    exact Nat.eq_zero_of_le_zero h
  · intro H; subst d; exact map_zero _

instance sliceZeroUnique : Unique (Slice w 0) where
  default:=⟨0,map_zero _⟩
  uniq d:=Subtype.ext ((weight_eq_zero_iff w d.val).mp d.property)

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_SupportedConvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

def Supported (S : Finset I) (d : I → ℕ) : Prop := ∀i,i∉S → d i=0

def restrictDim (S : Finset I) (d : I → ℕ) : I → ℕ := fun i=>if i∈S then d i else 0

def supportedCoefficient (S : Finset I) (f : (I → ℕ) → R) (d : I → ℕ) : R := by
  classical
  exact if Supported S d then f d else 0

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_GradedAlgebra_InputOrderedProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle QuantumTorus PowerSeries
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (a : I → I → ℕ) (u : I → ℕ → R)
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)

def partialCoefficient (S : Finset I) : (I → ℕ) → R :=
  supportedCoefficient S (fun d=>(∏i∈S,u i (d i))*↑(v^(crossInteraction a d)))

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Shuffle_InputProduct
attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace ElementaryPositivity.RawShuffle
open QuantumTorus WeightedTorusSeries PowerSeries WallUnits
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I M : Type*} [Fintype I] [DecidableEq I] [AddCommGroup M]
variable (a : I → I → ℕ) (κ : I → ℤ) (ε : I → Bool)
variable (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
variable (w : I → ℕ) [Fact (∀i,0<w i)]

def literalAxisScalar (i : I) : PowerSeries (LaurentSeries ℚ) :=
  PowerSeries.map LaurentRay.atInfinity (UnitSelections.indexedUnit (elementaryDiagonal ε i) (κ i))

def literalAxis (i : I) : PowerSeries (Torus LaurentRay.vUnit Ω) :=
  weightedRay LaurentRay.vUnit Ω (w i) (P (Pi.single i 1)) (literalAxisScalar κ ε i)

end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic QuantumTorus
noncomputable section
variable {I M : Type*} [Fintype I] [DecidableEq I] [AddCommGroup M]
variable (Ω : M →+ M →+ ℤ) (p : I → M) (ε : I → Bool)

def geometricQuiver (i j : I) : ℕ :=
  if i=j then elementaryDiagonal ε i else (Ω (p j) (p i)).toNat

def rootSum : (I→ℕ) →+ M where
  toFun d:=∑i,d i • p i
  map_zero':=by simp
  map_add':=by intro d e; simp only [Pi.add_apply,add_nsmul,Finset.sum_add_distrib]

end
end ElementaryPositivity.RawShuffle

end

end OAI
end

section
-- module Solutions.OAIQ368_CHROM.Chromatic_Walls_DegreeIsolatedReordering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity
namespace RootTruncation
open PowerSeries
noncomputable section
variable {A : Type*} [Ring A]
def patchTop (n : ℕ) (G F : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk (fun j=>if j≤n then coeff j G else if j=n+1 then coeff j F else 0)
@[simp] lemma coeff_patchTop (n j : ℕ) (G F : PowerSeries A) :
    coeff j (patchTop n G F)=if j≤n then coeff j G else if j=n+1 then coeff j F else 0 :=
  coeff_mk _ _
end
end RootTruncation
end ElementaryPositivity

end

end OAI
end


