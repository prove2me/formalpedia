-- Prove2me | Definitions.Def_OAIQ124K013
-- name    : OAIQ124K013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:55:49.512357+00:00
-- url     : https://prove2.me/theorems/c041ffa1-a89f-4355-bf90-2b7b10b284ec
-- title:
--   Definitions bundle OAIQ124K013 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 11 definitions, 1 instance and 9 theorems. The definitions and types are `OAI.KLInvariance.TitsSpace.BottCompatible`, `OAI.KLInvariance.TitsSpace.BottFlabby`, `OAI.KLInvariance.TitsSpace.BottProjectiveUpper`, `OAI.KLInvariance.TitsSpace.BottUpperIndex`, `OAI.KLInvariance.TitsSpace.bottCoordinateDenominator`, `OAI.KLInvariance.TitsSpace.bottIndexSetEval`, `OAI.KLInvariance.TitsSpace.bottInterRestriction`, `OAI.KLInvariance.TitsSpace.bottProjectionSheaf`, `OAI.KLInvariance.TitsSpace.bottSetImage`, `OAI.KLInvariance.TitsSpace.bottSetProjection`, `OAI.KLInvariance.TitsSpace.bottSetRestrict`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BottSamelson`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BottSamelson.lean), [`KazhdanLusztig_Frobenius`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Frobenius.lean), [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K008`, `OAIQ124K009` and `OAIQ124K010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K016`, `OAIQ124K017` and `OAIQ124K018`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K008
import Definitions.Def_OAIQ124K009
import Definitions.Def_OAIQ124K010

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Frobenius
attribute [-instance] _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_graded _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_graded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coxeter Frobenius extensions, tensor duality and translation across reflection pairs.
-/


section

/-! Tensor induction of integral self-dual bimodules across a Frobenius
extension. All pairings refer to actual integral modules. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
noncomputable section

attribute [instance] PairedModule.add PairedModule.module PairedModule.free PairedModule.finite

end
end KLInvariance.FrobeniusDuality

end


section

/-! Integral denominators exhibit the full generic subexpression support of
an actual tensor word. No moment-sheaf character assertion is made. -/
namespace KLInvariance.TitsSpace
open Module
open scoped Matrix
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottCoordinateDenominator (l : List I) : SymmetricCoefficient (M := M) := by
  classical
  exact (bottEvaluationMatrix cs l).det

 theorem bottEvaluation_contains_scaled_coordinates (l : List I)
    (v : BottIndex l → SymmetricCoefficient (M := M)) :
    ∃ m : BottSamelsonModule cs l, ∀ e,
      bottEvaluation cs l e m = bottCoordinateDenominator cs l * v e := by
  classical
  refine ⟨(bottBasis cs l).equivFun.symm ((bottEvaluationMatrix cs l).adjugate *ᵥ v),?_⟩
  intro e
  rw [bottEvaluation_expand]
  simp only [LinearEquiv.apply_symm_apply,Matrix.mulVec_mulVec,Matrix.mul_adjugate,
    Matrix.smul_mulVec,Matrix.one_mulVec,Pi.smul_apply,smul_eq_mul,bottCoordinateDenominator]

end
end KLInvariance.TitsSpace

end


section

/-! The actual integral two-vertex projection sheaf of a tensor
Bott--Samelson module. This is the localization-functor construction, not
an assumed BMP sheaf. Surjectivity onto ALL sections, flabbiness, free stalks,
and the indecomposable normalization remain separate obligations. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottProjectionSheaf (l : List I) (u b : W) : Sheaf (R := SymmetricCoefficient (M := M))
    (graph cs u b) where
  vertex x := ModuleCat.of _ (bottStalk cs l x.val)
  edge e := ModuleCat.of _ (PairProjection.Edge
    (bottStalkProjection cs l (source cs u b e).val)
    (bottStalkProjection cs l (target cs u b e).val))
  lower e := by
    change (bottStalk cs l (source cs u b e).val) →ₗ[SymmetricCoefficient (M := M)] _
    exact PairProjection.lower (bottStalkProjection cs l (source cs u b e).val)
      (bottStalkProjection cs l (target cs u b e).val)
  upper e := by
    change (bottStalk cs l (target cs u b e).val) →ₗ[SymmetricCoefficient (M := M)] _
    exact PairProjection.upper (bottStalkProjection cs l (source cs u b e).val)
      (bottStalkProjection cs l (target cs u b e).val)

 theorem bottProjectionSheaf_upper_surjective (l : List I) (u b : W) (e : Edge cs u b) :
    Function.Surjective ((bottProjectionSheaf cs l u b).upper e) :=
  PairProjection.upper_surjective _ _ (bottStalkProjection_surjective cs l _)

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! Intermediate standard-filtration predicates on the genuine tensor word.
These are proved by word induction; they are not main-theorem assumptions. -/
namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottStalk_smul_injective (l : List I) (x : W)
    {r : SymmetricCoefficient (M := M)} (hr : r≠0) :
    Function.Injective (fun z : bottStalk cs l x => r • z) :=
  smul_right_injective (bottStalk cs l x) hr

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottStalk_nil_subsingleton (x : W) (hx : x≠1) : Subsingleton (bottStalk cs [] x) := by
  constructor
  intro p q
  apply Subtype.ext
  funext e
  exact False.elim (hx e.property.symm)

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_IntegralPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert recurrences, projective section ranges, integral lattices and graded perfect adjoints.
-/


section

/-! Upper sets and actual finite-word projection predicates. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection
universe u v
variable {I : Type u} [klPreservedInstance11 : Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSetImage (l : List I) (U : Set W) := image (bottStalkProjection cs l) U
 instance bottSetImageModule (l : List I) (U : Set W) : Module (SymmetricCoefficient (M := M)) (bottSetImage cs l U) :=
  Submodule.module _

 def bottSetProjection (l : List I) (U : Set W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)] bottSetImage cs l U := project (bottStalkProjection cs l) U

 def BottCompatible (l : List I) (U : Set W) (z : ∀ x : U, bottStalk cs l x.val) : Prop :=
  ∀ (x y : W) (hx : x∈U) (hy : y∈U), BruhatStep cs x y →
    ∃ m : BottSamelsonModule cs l,
      bottStalkProjection cs l x m=z ⟨x,hx⟩ ∧ bottStalkProjection cs l y m=z ⟨y,hy⟩

 def BottFlabby (l : List I) : Prop :=
  ∀ U, BruhatUpper cs U → ∀ z, BottCompatible cs l U z → z∈bottSetImage cs l U

 def BottProjectiveUpper (l : List I) : Prop :=
  ∀ U, BruhatUpper cs U → Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U)

end
end KLInvariance.TitsSpace

end


section

/-! Genuine first/reflected-tail maps on projected upper-set images. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
open CoordinateProjection ProjectiveRange
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottSetProjection_zero_iff (l : List I) (U : Set W) (m : BottSamelsonModule cs l) :
    bottSetProjection cs l U m=0 ↔ ∀ x∈U, bottStalkProjection cs l x m=0 :=
  project_zero_iff _ _ _

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module TensorProduct CoordinateProjection ReflectionPairTranslation
open FrobeniusDuality ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def bottSetRestrict (l : List I) {U K : Set W} (h : U⊆K) :
    bottSetImage cs l K →ₗ[SymmetricCoefficient (M := M)] bottSetImage cs l U :=
  restrict (bottStalkProjection cs l) h

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottInterRestriction (i : I) (l : List I) (U : Set W) :
    bottSetImage cs l U →ₗ[SymmetricCoefficient (M := M)] bottSetImage cs l (simpleInter cs i U) :=
  bottSetRestrict cs l (fun _ h => h.1)

end
end KLInvariance.TitsSpace

end


section

/-! Every nontrivial prime-local congruence class of actual Coxeter
polynomial characters is a two-vertex reflection block. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem isReflection_of_prime_character_congruence
    (p : SymmetricCoefficient (M := M)) (hp : Prime p)
    {x y : W} (hxy : x ≠ y)
    (hcon : ∀ a, p ∣ coefficientAction cs x a-coefficientAction cs y a) :
    cs.IsReflection (y*x⁻¹) := by
  let w := y*x⁻¹
  have hw : w ≠ 1 := by
    intro h
    exact hxy (mul_inv_eq_one.mp h).symm
  have hex : ∃ v : Extended M, extendedAction M cs w v-v ≠ 0 := by
    by_contra! h
    apply hw
    apply extendedAction_injective M cs
    apply LinearEquiv.ext
    intro v
    rw [map_one]
    exact sub_eq_zero.mp (h v)
  obtain ⟨v,hv⟩ := hex
  let d := extendedAction M cs w v-v
  have hd : d ≠ 0 := hv
  have hdiv (z : Extended M) : p ∣ SymmetricAlgebra.ι ℝ (Extended M)
      (extendedAction M cs w z-z) := by
    let a := (coefficientAction cs x).symm (SymmetricAlgebra.ι ℝ (Extended M) z)
    have hx : coefficientAction cs x a=SymmetricAlgebra.ι ℝ (Extended M) z :=
      AlgEquiv.apply_symm_apply _ _
    have hy : coefficientAction cs y a =
        coefficientAction cs w (SymmetricAlgebra.ι ℝ (Extended M) z) := by
      have h := coefficientAction_mul cs w x a
      rw [show w*x=y by dsimp [w]; group,hx] at h
      exact h
    have h := hcon a
    rw [hx,hy,coefficientAction_ι,← map_sub] at h
    simpa only [← map_neg,neg_sub] using dvd_neg.mpr h
  have hassoc := hp.associated_of_dvd (EdgeAlgebra.symmetric_ι_prime d hd) (hdiv v)
  have heq : LinearMap.range ((extendedAction M cs w).toLinearMap-LinearMap.id) =
      Submodule.span ℝ {d} := by
    apply le_antisymm
    · rintro z ⟨a,rfl⟩
      change extendedAction M cs w a-a ∈ Submodule.span ℝ {d}
      exact (EdgeAlgebra.symmetric_ι_dvd_iff d _).mp
        (dvd_trans hassoc.symm.dvd (hdiv a))
    · apply Submodule.span_le.mpr
      intro z hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact ⟨v,rfl⟩
  apply isReflection_of_moving_rank_one M cs w
  rw [heq,finrank_span_singleton hd]

end
end KLInvariance.TitsSpace

end


section

/-! Integral local projectors for finite character lattices. This lemma does
not assert any BMP character theorem or identify a chosen summand with BMP. -/
namespace KLInvariance.FiniteCharacterLocalization
universe u v w
variable {R : Type u} [CommRing R] {X : Type v}
  {E : X → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)]
noncomputable section

/-- Pair/blockwise liftability at a prime suffices for integral local
membership in a finite character-stable lattice. -/
 theorem character_local_denominator [Fintype X] {A : Type*}
    (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p)
    (χ : A → X → R) (hχ : ∀ a, χ a ∈ stabilizer L) (z : ∀ x, E x)
    (hlift : ∀ x, ∃ m ∈ L, ∀ y, (residueSetoid p χ).r x y → m y=z y) :
    ∃ a : R, ¬ p ∣ a ∧ a • z ∈ L := by
  classical
  let Q := Quotient (residueSetoid p χ)
  let : Fintype Q := Fintype.ofFinite Q
  let q : X → Q := Quotient.mk''
  have hq (j : Q) (y : X) : q y=j ↔ (residueSetoid p χ).r j.out y := by
    constructor
    · intro h
      exact (residueSetoid p χ).symm (Quotient.exact (h.trans (Quotient.out_eq j).symm))
    · intro h
      exact (Quotient.sound ((residueSetoid p χ).symm h)).trans (Quotient.out_eq j)
  have hproj (j : Q) := character_class_projector L p hp χ hχ j.out
  choose d hd g hg hgin hgout using hproj
  have hm (j : Q) := hlift j.out
  choose m hm hmatch using hm
  exact partition_local_denominator L p hp q z d hd g hg
    (fun j y h => hgin j y ((hq j y).mp h))
    (fun j y h => hgout j y (fun hh => h ((hq j y).mpr hh)))
    m hm (fun j y h => hmatch j y ((hq j y).mp h))

end
end KLInvariance.FiniteCharacterLocalization

end


section

/-! Prime-local realization on arbitrary upper coordinate sets. Projectivity
of the actual image is kept explicit here and discharged by word induction. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection FiniteCharacterLocalization
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottSet_scaled (l : List I) (U : Set W)
    (z : ∀ x : U, bottStalk cs l x.val) :
    bottCoordinateDenominator cs l • z ∈ bottSetImage cs l U := by
  classical
  let c (e : BottIndex l) : SymmetricCoefficient (M := M) :=
    if h : bottWeight cs l e∈U then (z ⟨bottWeight cs l e,h⟩).val ⟨e,rfl⟩ else 0
  obtain ⟨m,hm⟩ := bottEvaluation_contains_scaled_coordinates cs l c
  refine ⟨m,?_⟩
  funext x
  apply Subtype.ext
  funext e
  rcases x with ⟨x,hx⟩
  rcases e with ⟨e,he⟩
  change bottWeight cs l e=x at he
  subst x
  change bottEvaluation cs l e m=bottCoordinateDenominator cs l * (z ⟨bottWeight cs l e,hx⟩).val ⟨e,rfl⟩
  simpa only [c,dite_eq_left hx] using hm e

 theorem BottCompatible.reflection_lift {l : List I} {U : Set W}
    {z : ∀ x : U, bottStalk cs l x.val} (hz : BottCompatible cs l U z)
    (x y : U) (t : W) (ht : cs.IsReflection t) (he : t*x.val=y.val) :
    ∃ m : BottSamelsonModule cs l,
      bottStalkProjection cs l x.val m=z x ∧ bottStalkProjection cs l y.val m=z y := by
  have he' : t*y.val=x.val := by rw [← he,← mul_assoc,ht.mul_self,one_mul]
  have hne : cs.length y.val ≠ cs.length x.val := by
    rw [← he]
    exact ht.length_mul_right_ne x.val
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨m,hm,hn⟩ := hz y.val x.val y.property x.property ⟨hlt,t,ht,he'.symm⟩
    exact ⟨m,hn,hm⟩
  · exact hz x.val y.val x.property y.property ⟨hlt,t,ht,he.symm⟩

 def BottUpperIndex (l : List I) (U : Set W) := {e : BottIndex l // bottWeight cs l e∈U}

 def bottIndexSetEval (l : List I) (U : Set W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)]
    (∀ e : BottUpperIndex cs l U, bottStalk cs l (bottWeight cs l e.val)) :=
  LinearMap.pi (fun e => bottStalkProjection cs l (bottWeight cs l e.val))

end
end KLInvariance.TitsSpace

end


end OAI
end


