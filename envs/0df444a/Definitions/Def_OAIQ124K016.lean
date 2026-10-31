-- Prove2me | Definitions.Def_OAIQ124K016
-- name    : OAIQ124K016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:05:57.693227+00:00
-- url     : https://prove2.me/theorems/02ee5162-13a6-4e3f-b718-d2a621fd4327
-- title:
--   Definitions bundle OAIQ124K016 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 20 declarations of OpenAI's Lean: 1 definition, 1 instance and 18 theorems. The definitions and types are `OAI.KLInvariance.TitsSpace.bottHeadPairEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BottSamelson`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BottSamelson.lean), [`KazhdanLusztig_Frobenius`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Frobenius.lean), [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean), [`KazhdanLusztig_Support`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Support.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K012`, `OAIQ124K013` and `OAIQ124K014` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K019`, `OAIQ124K020` and `OAIQ124K021`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K012
import Definitions.Def_OAIQ124K013
import Definitions.Def_OAIQ124K014

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Frobenius
attribute [-instance] _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_graded _root_.OAI.KLInvariance.TitsSpace.bottHeadPairAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottHeadPairModule _root_.OAI.KLInvariance.TitsSpace.bottSetImageModule _root_.OAI.KLInvariance.TitsSpace.bottStalkFinite _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_graded
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

 theorem bottCoordinateDenominator_ne_zero (l : List I) :
    bottCoordinateDenominator cs l ≠ 0 := by
  classical
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  exact Matrix.mulVec_injective_iff.mp (bottEvaluationMatrix_injective cs l)

end
end KLInvariance.TitsSpace

end


section

/-! The exact simple-wall kernel for the actual integral tensor word module.
This is a step toward word-sheaf recognition, not a character theorem or a
proof of combinatorial invariance. No stalk freeness is assumed. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

/-- The reverse inclusion to edge annihilation for the simple wall at the
first tensor letter, expressed directly on kernel projections. -/
theorem bottSimpleWall_kernel_projection (i : I) (l : List I) (x : W)
    {m : BottSamelsonModule cs (i::l)} (hm : bottStalkProjection cs (i::l) x m=0) :
    ∃ n : bottStalk cs (i::l) (cs.simple i*x),
      bottStalkProjection cs (i::l) (cs.simple i*x) m = simpleRootPolynomial (M := M) i • n := by
  obtain ⟨n,hn⟩ := bottSimpleFlip_divisible cs i l m
  refine ⟨bottStalkProjection cs (i::l) (cs.simple i*x) n, ?_⟩
  have he := congrArg (bottStalkProjection cs (i::l) (cs.simple i*x)) hn
  rw [map_sub, map_smul, bottStalkProjection_flip_zero cs i l x hm, sub_zero] at he
  exact he

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
attribute [-instance] _root_.OAI.KLInvariance.TitsSpace.bottSetImageModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! The genuine head-word stalk is an integral reflected pair lattice of the
tail word. This supplies the stalk-freeness step once tail edge exactness is
proved; it does not assume the desired main conclusion. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 variable (i : I) (l : List I) (x : W)

 theorem bottHeadPairToStalk_injective : Function.Injective (bottHeadPairToStalk cs i l x) := by
  intro p q h
  apply Subtype.ext
  exact bottHeadPairCoordinates_injective cs i l x (congrArg Subtype.val h)

 theorem bottHeadPairToStalk_surjective : Function.Surjective (bottHeadPairToStalk cs i l x) := by
  exact codRestrict_surjective_of_range_le (A := SymmetricCoefficient (M := M))
    (P := bottHeadPairLattice cs i l x)
    (V := {e : BottIndex (i::l) // bottWeight cs (i::l) e=x} → SymmetricCoefficient (M := M))
    ((bottHeadPairCoordinates cs i l x).comp (bottHeadPairLattice cs i l x).subtype)
    (bottStalk cs (i::l) x) _ (bottHeadPair_range cs i l x)

 def bottHeadPairEquiv : bottHeadPairLattice cs i l x ≃ₗ[
     SymmetricCoefficient (M := M)] bottStalk cs (i::l) x :=
  LinearEquiv.ofBijective (bottHeadPairToStalk cs i l x)
    ⟨bottHeadPairToStalk_injective cs i l x,bottHeadPairToStalk_surjective cs i l x⟩

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius ReflectionPairTranslation
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottHeadLocalPair_value (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadLocalPair cs i l x m =
      (bottStalkProjection cs l x (bottHeadTail cs i l m),
       Twist.mk (bottStalkProjection cs l (cs.simple i*x) (bottHeadReflectedTail cs i l m).val)) := rfl

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

 theorem bottKernelExact_cons_nonhead (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x t : W) (a : I → ℝ) (ha : Represents M cs t a)
    (hlt : cs.length x < cs.length (t*x)) (hts : t≠cs.simple i)
    (m : BottSamelsonModule cs (i::l)) (hm : bottStalkProjection cs (i::l) x m=0) :
    ∃ z : bottStalk cs (i::l) (t*x), bottStalkProjection cs (i::l) (t*x) m=
      SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z := by
  have he : t*x≠cs.simple i*x := fun h => hts (mul_right_cancel h)
  have hstep : BruhatStep cs x (t*x) := ⟨hlt,t,ha.isReflection,rfl⟩
  have hstep' := bruhatStep_simple_mul cs hstep i he
  have hconj : (cs.simple i*t*(cs.simple i)⁻¹)*(cs.simple i*x)=cs.simple i*(t*x) := by group
  have hzero := (bottHeadLocalPair_zero_iff cs i l x m).mp hm
  have hμ : bottStalkProjection cs l x (bottHeadTail cs i l m)=0 := congrArg Prod.fst hzero
  have hν : bottStalkProjection cs l (cs.simple i*x) (bottHeadReflectedTail cs i l m).val=0 :=
    congrArg (fun p => p.2.val) hzero
  obtain ⟨p,hp⟩ := H x t a ha hlt (bottHeadTail cs i l m) hμ
  obtain ⟨q,hq⟩ := H.projection_of_mul cs (cs.simple i*x) (cs.simple i*(t*x))
    (cs.simple i*t*(cs.simple i)⁻¹) (ha.act (cs.simple i)) hconj hstep'.1
    (bottHeadReflectedTail cs i l m).val hν
  let β : SymmetricCoefficient (M := M) := SymmetricAlgebra.ι ℝ (Extended M) (embed M a)
  let p' : bottStalk cs l (t*x) × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*(t*x))) := (p,⟨q⟩)
  have hβ' : coefficientAction cs (cs.simple i) β =
      SymmetricAlgebra.ι ℝ (Extended M) (embed M (action M cs (cs.simple i) a)) := by
    rw [coefficientAction_ι,extendedAction_restrict]
  have heq : bottHeadLocalPair cs i l (t*x) m=β • p' := by
    apply Prod.ext
    · exact hp
    · apply Twist.ext
      change bottStalkProjection cs l (cs.simple i*(t*x))
        (bottHeadReflectedTail cs i l m).val = coefficientAction cs (cs.simple i) β • q
      rw [hβ']
      exact hq
  have hn : ¬simpleRootPolynomial (M := M) i ∣ β :=
    represents_polynomial_not_dvd cs (simple_represents cs i) ha (Ne.symm hts)
  exact bottHeadStalk_divisible cs i l H F (t*x) m β hn p' heq

 theorem bottKernelExact_cons (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x)) :
    BottKernelExact cs (i::l) := by
  intro x t a ha hlt m hm
  by_cases hts : t=cs.simple i
  · subst t
    obtain ⟨z,hz⟩ := bottSimpleWall_kernel_projection cs i l x hm
    rcases ha.unique_up_to_sign (simple_represents cs i) with h|h
    · subst a
      exact ⟨z,hz⟩
    · subst a
      refine ⟨-z,?_⟩
      rw [hz]
      change simpleRootPolynomial (M := M) i • z =
        SymmetricAlgebra.ι ℝ (Extended M) (embed M (-root i)) • (-z)
      have he : embed M (-root i) = -embed M (root i) := by simp [embed]
      have hn : SymmetricAlgebra.ι ℝ (Extended M) (embed M (-root i)) =
          -simpleRootPolynomial (M := M) i := by
        rw [he]
        exact (SymmetricAlgebra.ι ℝ (Extended M)).map_neg _
      rw [hn]
      exact (neg_smul_neg _ z).symm
  · exact bottKernelExact_cons_nonhead cs i l H F x t a ha hlt hts m hm

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

 theorem bottStalk_free_cons (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x : W) : Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs (i::l) x) := by
  let := F x
  let := F (cs.simple i*x)
  have hα : simpleRootPolynomial (M := M) i ≠ 0 :=
    (represents_polynomial_prime cs (simple_represents cs i)).ne_zero
  have hlattice : Module.Free (SymmetricCoefficient (M := M)) (bottHeadPairLattice cs i l x) := by
    rcases lt_or_gt_of_ne (cs.length_simple_mul_ne x i) with hdesc | hasc
    · apply lattice_free_right
        (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
        (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
        (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
      · intro z
        have hh := H.kernel_iff_of_mul cs (cs.simple i*x) x (cs.simple i)
          (simple_represents cs i) (cs.simple_mul_simple_cancel_left i) hdesc z
        simpa only [and_comm,simpleRootPolynomial,extendedRoot] using hh
      · exact bottStalkProjection_surjective cs l (cs.simple i*x)
      · exact bottStalk_smul_injective cs l x hα
    · exact lattice_free (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
        (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
        (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
        (H.kernel_iff cs x (cs.simple i) (simple_represents cs i) hasc)
        (bottStalkProjection_surjective cs l x)
        (bottStalk_smul_injective cs l (cs.simple i*x) hα)
  let := hlattice
  exact Module.Free.of_equiv (bottHeadPairEquiv cs i l x)

 theorem bottStalk_nil_free (x : W) :
    Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs [] x) := by
  by_cases hx : x=1
  · subst x
    exact Module.Free.of_equiv (bottTopStalkEquiv cs [] (by simp [CoxeterSystem.IsReduced])).symm
  · let := bottStalk_nil_subsingleton cs x hx
    infer_instance

 theorem bottKernelExact_nil : BottKernelExact cs [] := by
  intro x t a ha hlt m hm
  have hx : t*x≠1 := by
    intro h
    rw [h] at hlt
    rw [cs.length_one] at hlt
    exact Nat.not_lt_zero _ hlt
  let := bottStalk_nil_subsingleton cs (t*x) hx
  exact ⟨0,Subsingleton.elim _ _⟩

end
end KLInvariance.TitsSpace

end


section

/-! Unconditional integral free stalks and exact oriented edge kernels for
all tensor words. These are the local parts of BMP recognition; flabbiness
and the KL character are not asserted here. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottStandardStalks (l : List I) :
    BottKernelExact cs l ∧ ∀ x : W,
      Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x) := by
  induction l with
  | nil => exact ⟨bottKernelExact_nil cs,bottStalk_nil_free cs⟩
  | cons i l h => exact ⟨bottKernelExact_cons cs i l h.1 h.2,
      bottStalk_free_cons cs i l h.1 h.2⟩

 theorem bottKernelExact (l : List I) : BottKernelExact cs l := (bottStandardStalks cs l).1

 theorem bottProjectionSheaf_upper_kernel (l : List I) (u b : W) (e : Edge cs u b)
    {a : I → ℝ} (ha : Represents M cs (label cs u b e) a)
    (z : (bottProjectionSheaf cs l u b).vertex (target cs u b e)) :
    (bottProjectionSheaf cs l u b).upper e z=0 ↔
      ∃ w, z=SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • w := by
  change PairProjection.upper (bottStalkProjection cs l (source cs u b e).val)
      (bottStalkProjection cs l (target cs u b e).val) z=0 ↔ _
  exact (PairProjection.kernel_upper _ _ z).trans
    ((bottKernelExact cs l).kernel_iff_of_mul cs _ _ _ ha
      (label_mul_source cs u b e) e.property.1 z)

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

 instance bottSetImageAddCommGroup (l : List I) (U : Set W) : AddCommGroup (bottSetImage cs l U) :=
  Submodule.addCommGroup _

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

 theorem prime_character_class (p : SymmetricCoefficient (M := M)) (hp : Prime p)
    {x y : W} (hxy : x ≠ y)
    (hcon : ∀ a, p ∣ coefficientAction cs x a-coefficientAction cs y a) :
    ∃ t : W, cs.IsReflection t ∧ y=t*x ∧
      ∀ z, (∀ a, p ∣ coefficientAction cs x a-coefficientAction cs z a) ↔
        x=z ∨ z=t*x := by
  let t := y*x⁻¹
  have ht := isReflection_of_prime_character_congruence cs p hp hxy hcon
  let a := (positiveRoot M cs ⟨t,ht⟩).val
  have ha : Represents M cs t a := positiveRoot_represents M cs ⟨t,ht⟩
  have he : t*x=y := by dsimp [t]; group
  obtain ⟨c,hc⟩ := reflectionCoefficient_difference cs ha x
  rw [he] at hc
  have hpa : p ∣ SymmetricAlgebra.ι ℝ (Extended M) (embed M a) := hc ▸ hcon c
  have hane : embed M a ≠ 0 := by
    intro h
    have hn : extendedForm M (embed M a) (embed M a)=2 := by
      rw [(extendedForm_spec M).2.2]
      exact ha.isRoot.norm
    rw [h,map_zero] at hn
    norm_num at hn
  have hassoc := hp.associated_of_dvd (EdgeAlgebra.symmetric_ι_prime (embed M a) hane) hpa
  refine ⟨t,ht,he.symm,?_⟩
  intro z
  rw [← reflection_character_congruence_iff cs ha x z]
  exact forall_congr' fun c => ⟨fun h => dvd_trans hassoc.symm.dvd h,
    fun h => dvd_trans hassoc.dvd h⟩

end
end KLInvariance.TitsSpace

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

 theorem BottCompatible.prime_lift {l : List I} {U : Set W}
    {z : ∀ x : U, bottStalk cs l x.val} (hz : BottCompatible cs l U z)
    (p : SymmetricCoefficient (M := M)) (hp : Prime p) (x : U) :
    ∃ m : BottSamelsonModule cs l, ∀ y : U,
      (∀ a, p ∣ coefficientAction cs x.val a-coefficientAction cs y.val a) →
      bottStalkProjection cs l y.val m=z y := by
  classical
  by_cases hx : ∃ y : U, x≠y ∧
      ∀ a, p ∣ coefficientAction cs x.val a-coefficientAction cs y.val a
  · obtain ⟨y,hxy,hcon⟩ := hx
    obtain ⟨t,ht,he,hclass⟩ := prime_character_class cs p hp
      (fun h => hxy (Subtype.ext h)) hcon
    obtain ⟨m,hm,hn⟩ := hz.reflection_lift cs x y t ht he.symm
    refine ⟨m,?_⟩
    intro w hw
    rcases (hclass w.val).mp hw with hxw | hwy
    · have h : w=x := Subtype.ext hxw.symm
      subst w
      exact hm
    · have h : w=y := Subtype.ext (hwy.trans he.symm)
      subst w
      exact hn
  · obtain ⟨m,hm⟩ := bottStalkProjection_surjective cs l x.val (z x)
    refine ⟨m,?_⟩
    intro y hy
    have h : y=x := by
      by_contra h
      exact hx ⟨y,Ne.symm h,hy⟩
    subst y
    exact hm

 theorem bottIndexSetEval_stable (l : List I) (U : Set W)
    (a : SymmetricCoefficient (M := M)) :
    (fun e : BottUpperIndex cs l U => coefficientAction cs (bottWeight cs l e.val) a) ∈
      stabilizer (LinearMap.range (bottIndexSetEval cs l U)) := by
  rintro z ⟨m,rfl⟩
  refine ⟨bottSamelsonRight cs l a m,?_⟩
  funext e
  exact bottStalkProjection_right cs l _ a m

 theorem BottCompatible.local_denominator {l : List I} {U : Set W}
    {z : ∀ x : U, bottStalk cs l x.val} (hz : BottCompatible cs l U z)
    (p : SymmetricCoefficient (M := M)) (hp : Prime p) :
    ∃ a : SymmetricCoefficient (M := M), ¬p ∣ a ∧ a • z∈bottSetImage cs l U := by
  classical
  let : Fintype (BottUpperIndex cs l U) := inferInstanceAs (Fintype {e : BottIndex l // bottWeight cs l e∈U})
  let zz : ∀ e : BottUpperIndex cs l U, bottStalk cs l (bottWeight cs l e.val) :=
    fun e => z ⟨bottWeight cs l e.val,e.property⟩
  have hlift : ∀ e : BottUpperIndex cs l U, ∃ m ∈ LinearMap.range (bottIndexSetEval cs l U),
      ∀ f, (residueSetoid p (fun a e => coefficientAction cs (bottWeight cs l e.val) a)).r e f → m f=zz f := by
    intro e
    obtain ⟨m,hm⟩ := hz.prime_lift cs p hp ⟨bottWeight cs l e.val,e.property⟩
    exact ⟨bottIndexSetEval cs l U m,⟨m,rfl⟩,fun f hf => hm ⟨bottWeight cs l f.val,f.property⟩ hf⟩
  obtain ⟨a,ha,m,hm⟩ := character_local_denominator
    (LinearMap.range (bottIndexSetEval cs l U)) p hp
    (fun a e => coefficientAction cs (bottWeight cs l e.val) a)
    (bottIndexSetEval_stable cs l U) zz hlift
  refine ⟨a,ha,m,?_⟩
  funext x
  apply Subtype.ext
  funext e
  rcases x with ⟨x,hx⟩
  rcases e with ⟨e,he⟩
  change bottWeight cs l e=x at he
  subst x
  have hh := congrArg (fun q => (q ⟨e,hx⟩).val ⟨e,rfl⟩) hm
  exact hh

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded unit splittings, integral support and balanced cuts, and boundary-sheaf support and recognition.
-/


section

/-! The actual minimal-boundary sheaf is a summand of the reduced word.
No splitting or word-recognition axiom is supplied as a premise. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottGradedProjectionSheaf_upperQuotient (l : List I) (u b : W) :
    (bottGradedProjectionSheaf cs basis l u b).UpperQuotient (symmetricLabel cs u b) := by
  intro e
  exact ⟨bottProjectionSheaf_upper_surjective cs l u b e,
    bottProjectionSheaf_upper_kernel cs l u b e (symmetricLabel_represents cs u b e)⟩

end
end KLInvariance.TitsSpace

end


end OAI
end


