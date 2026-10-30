-- Prove2me | Definitions.Def_OAIQ124K012
-- name    : OAIQ124K012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:56:16.808495+00:00
-- url     : https://prove2.me/theorems/77744c47-0660-47a3-8187-c712aaf19065
-- title:
--   Definitions bundle OAIQ124K012 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 18 definitions, 3 instances and 39 theorems. The definitions and types are `OAI.KLInvariance.TitsSpace.BottKernelExact`, `OAI.KLInvariance.TitsSpace.bottBoundarySheafTopInclusion`, `OAI.KLInvariance.TitsSpace.bottBoundarySheafTopProjection`, `OAI.KLInvariance.TitsSpace.bottEdgeData`, `OAI.KLInvariance.TitsSpace.bottGradedProjectionSheaf`, `OAI.KLInvariance.TitsSpace.bottHeadLocalPair`, `OAI.KLInvariance.TitsSpace.bottHeadPairCoordinates`, `OAI.KLInvariance.TitsSpace.bottHeadPairLattice`, `OAI.KLInvariance.TitsSpace.bottHeadPairToStalk`, `OAI.KLInvariance.TitsSpace.bottIndexFlip`, `OAI.KLInvariance.TitsSpace.bottLowerHom`, `OAI.KLInvariance.TitsSpace.bottStalkHom`, `OAI.KLInvariance.TitsSpace.bottTopHom`, `OAI.KLInvariance.TitsSpace.bottTopInvHom`, `OAI.KLInvariance.TitsSpace.bottTopStalkEquiv`, `OAI.KLInvariance.TitsSpace.bottUpperHom`, `OAI.KLInvariance.TitsSpace.bottWordData`, `OAI.KLInvariance.TitsSpace.instDecidableEqBottIndex`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BalancedPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean), [`KazhdanLusztig_BottSamelson`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BottSamelson.lean), [`KazhdanLusztig_Frobenius`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Frobenius.lean), [`KazhdanLusztig_Support`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Support.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K008` and `OAIQ124K009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K016`, `OAIQ124K017` and `OAIQ124K018`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K008
import Definitions.Def_OAIQ124K009

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

/-! Actual subexpression-weight coordinates of the tensor Bott--Samelson
module, and the genuine right-action eigenvalue. These are the localization
maps required for moment-sheaf realization; no character theorem is assumed. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
universe u v un
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottEvaluation_right (l : List I) (e : BottIndex l)
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottEvaluation cs l e (bottSamelsonRight cs l a m) =
      coefficientAction cs (bottWeight cs l e) a * bottEvaluation cs l e m := by
  induction l with
  | nil =>
    change SymmetricCoefficient (M := M) at m
    change a*m = coefficientAction cs 1 a * m
    rw [coefficientAction_one]
  | cons i l ih =>
    change SymmetricCoefficient (M := M) ⊗[simpleFixed cs i] BottSamelsonModule cs l at m
    induction m using OAI.tensorInductionOn with
    | add m n hm hn => erw [map_add,map_add,map_add,hm,hn,mul_add]
    | tmul b m =>
      change bottEvaluation cs (i::l) e (b ⊗ₜ[simpleFixed cs i] bottSamelsonRight cs l a m) = _
      erw [bottEvaluation_tmul,bottEvaluation_tmul,ih]
      change b*(if e.1=0 then _ else _) = coefficientAction cs
        (if e.1=0 then bottWeight cs l e.2 else cs.simple i*bottWeight cs l e.2) a * _
      split_ifs with h
      · ring
      · rw [map_mul,coefficientAction_mul]
        ring

end
end KLInvariance.TitsSpace

end


section

/-! The actual tensor Bott--Samelson module embeds integrally in its individual
subexpression coordinates. Together with the checked weight eigenvalue this
identifies its generic support. It does not assert the integral moment-sheaf
recognition or the Elias--Williamson character theorem. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
open scoped Matrix
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem bottEvaluationMatrix_mulVec_cons (i : I) (l : List I)
    (v : BottIndex (i::l) → SymmetricCoefficient (M := M)) :
    bottEvaluationMatrix cs (i::l) *ᵥ v =
      wallCoordinate (coefficientAction cs (cs.simple i)).toRingEquiv
        (simpleRootPolynomial i) (bottEvaluationMatrix cs l) v := by
  have heq : bottEvaluationMatrix cs (i::l) =
      wallMatrix (coefficientAction cs (cs.simple i)).toRingEquiv
        (simpleRootPolynomial i) (bottEvaluationMatrix cs l) := by
    funext e f
    rcases e with ⟨r,j⟩
    rcases f with ⟨c,k⟩
    exact bottEvaluationMatrix_cons cs i l r c j k
  rw [heq]
  exact wallMatrix_mulVec (coefficientAction cs (cs.simple i)).toRingEquiv
    (simpleRootPolynomial i) (bottEvaluationMatrix cs l) v

 theorem bottEvaluationMatrix_injective (l : List I) :
    Function.Injective (Matrix.mulVec (bottEvaluationMatrix cs l)) := by
  classical
  let : CharZero (SymmetricCoefficient (M := M)) := Algebra.charZero_of_charZero ℝ _
  induction l with
  | nil =>
    intro v w h
    funext j
    change PUnit at j
    cases j
    have hh := congrFun h PUnit.unit
    let : Unique (BottIndex ([] : List I)) := inferInstanceAs (Unique PUnit)
    have hcol (k : BottIndex ([] : List I)) :
        bottEvaluationMatrix cs [] PUnit.unit k = 1 := by
      change PUnit at k
      change (Basis.singleton PUnit (SymmetricCoefficient (M := M)) k) = 1
      simp only [Basis.singleton_apply]
    simp only [Matrix.mulVec,dotProduct,hcol,one_mul,Finset.univ_unique,
      Finset.sum_singleton] at hh
    simpa only [Subsingleton.elim (default : BottIndex ([] : List I)) PUnit.unit] using hh
  | cons i l ih =>
    intro v w h
    apply wallCoordinate_injective (coefficientAction cs (cs.simple i)).toRingEquiv
      (simpleRootPolynomial i) (simpleRootPolynomial_ne_zero i) (bottEvaluationMatrix cs l) ih
    rw [← bottEvaluationMatrix_mulVec_cons,← bottEvaluationMatrix_mulVec_cons]
    exact h

 theorem bottEvaluation_injective (l : List I) :
    Function.Injective (fun m : BottSamelsonModule cs l => fun e => bottEvaluation cs l e m) := by
  intro m n h
  apply (bottBasis cs l).equivFun.injective
  apply bottEvaluationMatrix_injective cs l
  funext e
  rw [← bottEvaluation_expand,← bottEvaluation_expand]
  exact congrFun h e

end
end KLInvariance.TitsSpace

end


section

/-! Integral weight support and orthogonality for the actual tensor module.
These are the vertex support statements behind the section pairing, not an
identification of the minimal BMP sheaf or its character. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
local instance instDecidableEqBottIndex (l : List I) : DecidableEq (BottIndex l) := Classical.decEq _

end
end KLInvariance.TitsSpace

end


section

/-! The actual tensor word's integral weight-support lattice is the dual of
its integral projected stalk lattice. This is not merely a fraction-field
isomorphism. It still does NOT identify BMP sections with an indecomposable
summand of the tensor word, or prove the character theorem. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottWeightProjection_eq_zero (l : List I) (x : W) (m : BottSamelsonModule cs l) :
    bottWeightProjection cs l x m = 0 ↔ ∀ e, bottWeight cs l e=x → bottEvaluation cs l e m=0 := by
  constructor
  · intro h e he
    exact congrFun h ⟨e,he⟩
  · intro h
    funext e
    exact h e.val e.property

 theorem bottStalkProjection_eq_zero (l : List I) (x : W) (m : BottSamelsonModule cs l) :
    bottStalkProjection cs l x m=0 ↔ bottWeightProjection cs l x m=0 := by
  exact Subtype.ext_iff

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

 theorem bottStalkProjection_right (l : List I) (x : W)
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottStalkProjection cs l x (bottSamelsonRight cs l a m) =
      coefficientAction cs x a • bottStalkProjection cs l x m := by
  apply Subtype.ext
  funext e
  change bottEvaluation cs l e.val (bottSamelsonRight cs l a m) =
    coefficientAction cs x a * bottEvaluation cs l e.val m
  rw [bottEvaluation_right,e.property]

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


/-- Exchange the two branches of the first subexpression slot. -/
def bottIndexFlip (i : I) (l : List I) (e : BottIndex (i::l)) : BottIndex (i::l) :=
  (1-e.1,e.2)

omit [Fintype I] in
theorem bottWeight_flip (i : I) (l : List I) (e : BottIndex (i::l)) :
    bottWeight cs (i::l) (bottIndexFlip i l e) = cs.simple i * bottWeight cs (i::l) e := by
  rcases e with ⟨ε,e⟩
  fin_cases ε <;> simp [bottIndexFlip, bottWeight, cs.simple_mul_simple_cancel_left]

theorem bottEvaluation_flip (i : I) (l : List I) (e : BottIndex (i::l))
    (m : BottSamelsonModule cs (i::l)) :
    bottEvaluation cs (i::l) e (bottSimpleFlip cs i l m) =
      coefficientAction cs (cs.simple i)
        (bottEvaluation cs (i::l) (bottIndexFlip i l e) m) := by
  change SymmetricCoefficient (M := M) ⊗[simpleFixed cs i] BottSamelsonModule cs l at m
  induction m using OAI.tensorInductionOn with
  | add m n hm hn => erw [map_add, map_add, map_add, map_add, hm, hn]
  | tmul a m =>
    rcases e with ⟨ε,e⟩
    fin_cases ε
    · change coefficientAction cs (cs.simple i) a * bottEvaluation cs l e m =
        coefficientAction cs (cs.simple i)
          (a * coefficientAction cs (cs.simple i) (bottEvaluation cs l e m))
      rw [map_mul, simple_involutive cs i]
    · change coefficientAction cs (cs.simple i) a *
        coefficientAction cs (cs.simple i) (bottEvaluation cs l e m) =
        coefficientAction cs (cs.simple i) (a * bottEvaluation cs l e m)
      rw [map_mul]

theorem bottStalkProjection_flip_zero (i : I) (l : List I) (x : W)
    {m : BottSamelsonModule cs (i::l)} (hm : bottStalkProjection cs (i::l) x m=0) :
    bottStalkProjection cs (i::l) (cs.simple i*x) (bottSimpleFlip cs i l m)=0 := by
  apply (bottStalkProjection_eq_zero cs _ _ _).mpr
  apply (bottWeightProjection_eq_zero cs _ _ _).mpr
  intro e he
  rw [bottEvaluation_flip]
  have hh := (bottWeightProjection_eq_zero cs _ _ _).mp
    ((bottStalkProjection_eq_zero cs _ _ _).mp hm)
  rw [hh (bottIndexFlip i l e) (by
    rw [bottWeight_flip, he, cs.simple_mul_simple_cancel_left]), map_zero]


/-- Any old word's simple-edge quotient is killed by the actual label. -/
theorem bottSimpleEdge_annihilated (i : I) (l : List I) (x : W)
    (z : PairProjection.Edge (bottStalkProjection cs l x)
      (bottStalkProjection cs l (cs.simple i*x))) :
    simpleRootPolynomial (M := M) i • z = 0 := by
  obtain ⟨p,hp⟩ := simpleCoefficient_difference cs i x
  rw [← hp]
  exact PairProjection.difference_annihilates _ _
    (bottStalkProjection_surjective cs _ _) (bottStalkProjection_surjective cs _ _)
    (bottSamelsonRight cs l p) _ _
    (bottStalkProjection_right cs _ _ p) (bottStalkProjection_right cs _ _ p) z

theorem bottSimpleEdge_kernel_inclusion (i : I) (l : List I) (x : W)
    (y : bottStalk cs l (cs.simple i*x)) :
    ∃ n : BottSamelsonModule cs l, bottStalkProjection cs l x n=0 ∧
      bottStalkProjection cs l (cs.simple i*x) n=simpleRootPolynomial (M := M) i • y := by
  apply (PairProjection.kernel_upper _ _ _).mp
  rw [map_smul]
  exact bottSimpleEdge_annihilated cs i l x _

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

namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
universe u v up
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite
 theorem bottWeightProjection_range_le (i : I) (l : List I) (x : W)
    {P : Type up} [AddCommGroup P] [Module (SymmetricCoefficient (M := M)) P]
    (G : P →ₗ[SymmetricCoefficient (M := M)]
      ({e : BottIndex (i::l) // bottWeight cs (i::l) e=x} → SymmetricCoefficient (M := M)))
    (h : ∀ n : BottSamelsonModule cs l,
      bottWeightProjection cs (i::l) x ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n) ∈ LinearMap.range G) :
    LinearMap.range (bottWeightProjection cs (i::l) x) ≤ LinearMap.range G := by
  exact tensor_range_le_of_one_tmul (C := simpleFixed cs i)
    (A := SymmetricCoefficient (M := M)) (N := BottSamelsonModule cs l)
    (bottWeightProjection cs (i::l) x) G h

end
end KLInvariance.TitsSpace

end


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

 omit [Fintype I] in
 theorem bottWeight_tail_zero (i : I) (l : List I) (x : W)
    (e : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x}) (h : e.val.1=0) :
    bottWeight cs l e.val.2=x := by
  simpa only [bottWeight,ite_eq_left h] using e.property

 omit [Fintype I] in
 theorem bottWeight_tail_one (i : I) (l : List I) (x : W)
    (e : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x}) (h : e.val.1≠0) :
    bottWeight cs l e.val.2=cs.simple i*x := by
  have he : cs.simple i*bottWeight cs l e.val.2=x := by
    simpa only [bottWeight,ite_eq_right h] using e.property
  simpa only [cs.simple_mul_simple_cancel_left] using (congrArg (cs.simple i * ·) he)

 def bottHeadPairCoordinates (i : I) (l : List I) (x : W) :
    (bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x))) →ₗ[SymmetricCoefficient (M := M)]
      ({e : BottIndex (i::l) // bottWeight cs (i::l) e=x} → SymmetricCoefficient (M := M)) where
  toFun p e := if h : e.val.1=0 then
      p.1.val ⟨e.val.2,bottWeight_tail_zero cs i l x e h⟩
    else coefficientAction cs (cs.simple i)
      (p.2.val.val ⟨e.val.2,bottWeight_tail_one cs i l x e h⟩)
  map_add' p q := by
    funext e
    by_cases h : e.val.1=0
    · simp only [Pi.add_apply,dite_eq_left h]; rfl
    · simp only [Pi.add_apply,dite_eq_right h]
      exact map_add (coefficientAction cs (cs.simple i)) _ _
  map_smul' r p := by
    funext e
    dsimp
    split_ifs with h
    · rfl
    · change coefficientAction cs (cs.simple i)
        (coefficientAction cs (cs.simple i) r * _) = r * coefficientAction cs (cs.simple i) _
      rw [map_mul,simple_involutive]; rfl

 theorem bottHeadPairCoordinates_injective (i : I) (l : List I) (x : W) :
    Function.Injective (bottHeadPairCoordinates cs i l x) := by
  rintro ⟨p,q⟩ ⟨p',q'⟩ h
  apply Prod.ext
  · apply Subtype.ext
    funext e
    have hh := congrFun h ⟨(0,e.val),by simpa only [bottWeight,ite_true, if_true] using e.property⟩
    simpa only [bottHeadPairCoordinates,LinearMap.coe_mk,AddHom.coe_mk,dite_eq_left rfl,dite_true] using hh
  · apply Twist.ext
    apply Subtype.ext
    funext e
    have he : bottWeight cs (i::l) (1,e.val)=x := by
      change (if (1 : Fin 2)=0 then _ else cs.simple i*bottWeight cs l e.val)=x
      rw [ite_eq_right (by decide),e.property,cs.simple_mul_simple_cancel_left]
    have hh := congrFun h ⟨(1,e.val),he⟩
    have hh' : coefficientAction cs (cs.simple i) (q.val.val e) =
        coefficientAction cs (cs.simple i) (q'.val.val e) := by
      simpa only [bottHeadPairCoordinates,LinearMap.coe_mk,AddHom.coe_mk,
        dite_eq_right (show (1 : Fin 2)≠0 by decide)] using hh
    exact (coefficientAction cs (cs.simple i)).injective hh'

 variable (i : I) (l : List I) (x : W)

 def bottHeadPairLattice := lattice (bottStalkProjection cs l x)
    (bottStalkProjection cs l (cs.simple i*x)) (coefficientAction cs (cs.simple i)).toRingEquiv
    (simpleRootPolynomial (M := M) i) (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)

 instance bottHeadPairAddCommGroup : AddCommGroup (bottHeadPairLattice cs i l x) :=
  Submodule.addCommGroup (bottHeadPairLattice cs i l x)

 instance bottHeadPairModule : Module (SymmetricCoefficient (M := M)) (bottHeadPairLattice cs i l x) :=
  Submodule.module (bottHeadPairLattice cs i l x)

 theorem bottHeadPairCoordinates_seed (n : BottSamelsonModule cs l) :
    bottHeadPairCoordinates cs i l x
      (bottStalkProjection cs l x n,⟨bottStalkProjection cs l (cs.simple i*x) n⟩) =
    bottWeightProjection cs (i::l) x ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n) := by
  funext e
  change (if h : e.val.1=0 then _ else _) = (1 : SymmetricCoefficient (M := M))*(if e.val.1=0 then _ else _)
  rw [one_mul]
  split_ifs <;> rfl

 def bottHeadPairToStalk : bottHeadPairLattice cs i l x →ₗ[
     SymmetricCoefficient (M := M)] bottStalk cs (i::l) x :=
  LinearMap.codRestrict (bottStalk cs (i::l) x)
    ((bottHeadPairCoordinates cs i l x).comp (bottHeadPairLattice cs i l x).subtype) (by
      rintro ⟨⟨p,q⟩,n,hn,hn'⟩
      refine ⟨(1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n,?_⟩
      change bottWeightProjection cs (i::l) x _=bottHeadPairCoordinates cs i l x (p,q)
      rw [← bottHeadPairCoordinates_seed]
      congr 1
      exact Prod.ext hn (Twist.ext hn'))

 theorem bottHeadPair_range :
    LinearMap.range (bottWeightProjection cs (i::l) x) ≤
      LinearMap.range ((bottHeadPairCoordinates cs i l x).comp
        (bottHeadPairLattice cs i l x).subtype) := by
  refine bottWeightProjection_range_le cs i l x (P := bottHeadPairLattice cs i l x)
    ((bottHeadPairCoordinates cs i l x).comp (bottHeadPairLattice cs i l x).subtype) ?_
  intro n
  refine ⟨⟨(bottStalkProjection cs l x n,⟨bottStalkProjection cs l (cs.simple i*x) n⟩),n,rfl,rfl⟩,?_⟩
  exact bottHeadPairCoordinates_seed cs i l x n

end
end KLInvariance.TitsSpace

end


section

/-! The top projection lattice of a reduced actual tensor word is exactly A.
This verifies the genuine rank-one top used in the BMP summand construction;
it does not assert that the other projection lattices form a flabby sheaf. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottTopCoordinate_bijective (l : List I) (hl : cs.IsReduced l) :
    Function.Bijective (bottTopCoordinate cs l) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    funext e
    have he : e=⟨bottFullIndex l,bottWeight_full cs l⟩ :=
      Subtype.ext (bottWeight_eq_top cs l hl e.val e.property)
    subst e
    exact hab
  · intro a
    obtain ⟨m,hm⟩ := bottEvaluation_surjective cs l (bottFullIndex l) a
    exact ⟨bottStalkProjection cs l (cs.wordProd l) m,hm⟩

 def bottTopStalkEquiv (l : List I) (hl : cs.IsReduced l) :
    bottStalk cs l (cs.wordProd l) ≃ₗ[SymmetricCoefficient (M := M)]
      SymmetricCoefficient (M := M) :=
  LinearEquiv.ofBijective (bottTopCoordinate cs l) (bottTopCoordinate_bijective cs l hl)

end
end KLInvariance.TitsSpace

end


section

/-! Actual integral projection and support lattices inherit their grading from
the genuine tensor word. In particular a homogeneous stalk vector has a
homogeneous tensor lift. No freeness/character claim is assumed. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottStalkProjection_homogeneous (l : List I) (x : W) (n : ℤ)
    (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottStalkProjection cs l x m ∈ bottStalkPiece cs basis l x n :=
  bottWeightProjection_homogeneous cs basis l x n m hm

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

 def bottHeadLocalPair (i : I) (l : List I) (x : W) : BottSamelsonModule cs (i::l) →ₗ[
    SymmetricCoefficient (M := M)]
    (bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x))) :=
  ((bottStalkProjection cs l x).comp (bottHeadTail cs i l)).prod
    ((twistMap (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalkProjection cs l (cs.simple i*x))).comp (bottHeadReflectedTail cs i l))

 theorem bottHeadLocalPair_seed (i : I) (l : List I) (x : W) (n : BottSamelsonModule cs l) :
    bottHeadLocalPair cs i l x ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=
      (bottStalkProjection cs l x n,Twist.mk (bottStalkProjection cs l (cs.simple i*x) n)) := by
  change ((bottStalkProjection cs l x) (bottHeadTail cs i l _),
    (twistMap (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalkProjection cs l (cs.simple i*x))) (bottHeadReflectedTail cs i l _)) = _
  rw [bottHeadTail_seed,bottHeadReflectedTail_seed]
  rfl
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

 theorem bottHeadLocalPair_coordinates (i : I) (l : List I) (x : W) :
    (bottHeadPairCoordinates cs i l x).comp (bottHeadLocalPair cs i l x) =
      bottWeightProjection cs (i::l) x := by
  apply bottTensor_maps_eq cs i l
  intro n
  change bottHeadPairCoordinates cs i l x (bottHeadLocalPair cs i l x _) = _
  rw [bottHeadLocalPair_seed,bottHeadPairCoordinates_seed]

 theorem bottHeadLocalPair_mem (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadLocalPair cs i l x m ∈ bottHeadPairLattice cs i l x := by
  exact linearMap_mem_of_coordinates (bottHeadPairLattice cs i l x)
    (bottHeadPairCoordinates cs i l x) (bottHeadLocalPair cs i l x)
    (bottWeightProjection cs (i::l) x) (bottHeadPairCoordinates_injective cs i l x)
    (bottHeadLocalPair_coordinates cs i l x) (bottHeadPair_range cs i l x) m

 theorem bottHeadLocalPair_zero_iff (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) :
    bottStalkProjection cs (i::l) x m=0 ↔ bottHeadLocalPair cs i l x m=0 := by
  constructor
  · intro h
    apply bottHeadPairCoordinates_injective cs i l x
    rw [map_zero]
    have hh := congrArg Subtype.val h
    change bottWeightProjection cs (i::l) x m=0 at hh
    exact (LinearMap.congr_fun (bottHeadLocalPair_coordinates cs i l x) m).trans hh
  · intro h
    apply Subtype.ext
    change bottWeightProjection cs (i::l) x m=0
    rw [← LinearMap.congr_fun (bottHeadLocalPair_coordinates cs i l x) m]
    change bottHeadPairCoordinates cs i l x (bottHeadLocalPair cs i l x m)=0
    rw [h,map_zero]

 theorem bottHeadLocalPair_toStalk (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) :
    bottHeadPairToStalk cs i l x ⟨bottHeadLocalPair cs i l x m,bottHeadLocalPair_mem cs i l x m⟩ =
      bottStalkProjection cs (i::l) x m := by
  apply Subtype.ext
  exact LinearMap.congr_fun (bottHeadLocalPair_coordinates cs i l x) m

 theorem bottHeadStalk_divisible_of_pair (i : I) (l : List I) (x : W)
    (m : BottSamelsonModule cs (i::l)) (β : SymmetricCoefficient (M := M))
    (p : bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x)))
    (hm : bottHeadLocalPair cs i l x m=β • p) (hp : p ∈ bottHeadPairLattice cs i l x) :
    ∃ z : bottStalk cs (i::l) x, bottStalkProjection cs (i::l) x m=β • z := by
  let z : bottHeadPairLattice cs i l x := ⟨p,hp⟩
  refine ⟨bottHeadPairToStalk cs i l x z,?_⟩
  have he : (⟨bottHeadLocalPair cs i l x m,bottHeadLocalPair_mem cs i l x m⟩ :
      bottHeadPairLattice cs i l x) = β • z := Subtype.ext hm
  calc
    bottStalkProjection cs (i::l) x m =
        bottHeadPairToStalk cs i l x ⟨bottHeadLocalPair cs i l x m,bottHeadLocalPair_mem cs i l x m⟩ :=
      (bottHeadLocalPair_toStalk cs i l x m).symm
    _ = bottHeadPairToStalk cs i l x (β • z) := congrArg (bottHeadPairToStalk cs i l x) he
    _ = β • bottHeadPairToStalk cs i l x z := map_smul _ _ _

end
end KLInvariance.TitsSpace

end


section

/-! Intermediate standard-filtration predicates on the genuine tensor word.
These are proved by word induction; they are not main-theorem assumptions. -/
namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def BottKernelExact (l : List I) : Prop :=
  ∀ (x t : W) (a : I → ℝ), Represents M cs t a →
    cs.length x < cs.length (t*x) →
    ∀ m : BottSamelsonModule cs l, bottStalkProjection cs l x m=0 →
      ∃ z : bottStalk cs l (t*x), bottStalkProjection cs l (t*x) m=
        SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z

 instance bottStalkFinite (l : List I) (x : W) :
    Module.Finite (SymmetricCoefficient (M := M)) (bottStalk cs l x) :=
  Module.Finite.of_surjective (bottStalkProjection cs l x) (bottStalkProjection_surjective cs l x)

 theorem bottReflectionEdge_annihilated (l : List I) (x t : W) {a : I → ℝ}
    (ha : Represents M cs t a)
    (z : PairProjection.Edge (bottStalkProjection cs l x) (bottStalkProjection cs l (t*x))) :
    SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z=0 := by
  obtain ⟨p,hp⟩ := reflectionCoefficient_difference cs ha x
  rw [← hp]
  exact PairProjection.difference_annihilates _ _
    (bottStalkProjection_surjective cs _ _) (bottStalkProjection_surjective cs _ _)
    (bottSamelsonRight cs l p) _ _
    (bottStalkProjection_right cs _ _ p) (bottStalkProjection_right cs _ _ p) z

 theorem BottKernelExact.upper_kernel {l : List I} (H : BottKernelExact cs l)
    (x t : W) {a : I → ℝ} (ha : Represents M cs t a)
    (hlt : cs.length x < cs.length (t*x)) (z : bottStalk cs l (t*x)) :
    PairProjection.upper (bottStalkProjection cs l x) (bottStalkProjection cs l (t*x)) z=0 ↔
      ∃ w, z=SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • w :=
  PairProjection.upper_kernel_of_divisibility _ _ _ (H x t a ha hlt)
    (bottReflectionEdge_annihilated cs l x t ha) z

 theorem BottKernelExact.kernel_iff {l : List I} (H : BottKernelExact cs l)
    (x t : W) {a : I → ℝ} (ha : Represents M cs t a)
    (hlt : cs.length x < cs.length (t*x)) (z : bottStalk cs l (t*x)) :
    (∃ m, bottStalkProjection cs l x m=0 ∧ bottStalkProjection cs l (t*x) m=z) ↔
      ∃ w, z=SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • w := by
  rw [← PairProjection.kernel_upper]
  exact H.upper_kernel cs x t ha hlt z

 theorem BottKernelExact.kernel_iff_of_mul {l : List I} (H : BottKernelExact cs l)
    (x y t : W) {a : I → ℝ} (ha : Represents M cs t a) (hxy : t*x=y)
    (hlt : cs.length x < cs.length y) (z : bottStalk cs l y) :
    (∃ m, bottStalkProjection cs l x m=0 ∧ bottStalkProjection cs l y m=z) ↔
      ∃ w, z=SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • w := by
  subst y
  exact H.kernel_iff cs x t ha hlt z

 theorem BottKernelExact.projection_of_mul {l : List I} (H : BottKernelExact cs l)
    (x y t : W) {a : I → ℝ} (ha : Represents M cs t a) (hxy : t*x=y)
    (hlt : cs.length x < cs.length y) (m : BottSamelsonModule cs l)
    (hm : bottStalkProjection cs l x m=0) :
    ∃ z : bottStalk cs l y, bottStalkProjection cs l y m=
      SymmetricAlgebra.ι ℝ (Extended M) (embed M a) • z := by
  subst y
  exact H x t a ha hlt m hm

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

 theorem bottSimpleEdge_regular (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x : W) (β : SymmetricCoefficient (M := M)) (hβ : ¬simpleRootPolynomial (M := M) i ∣ β) :
    Function.Injective (fun e : PairProjection.Edge (bottStalkProjection cs l x)
      (bottStalkProjection cs l (cs.simple i*x)) => β • e) := by
  have hα : Prime (simpleRootPolynomial (M := M) i) :=
    represents_polynomial_prime cs (simple_represents cs i)
  rcases lt_or_gt_of_ne (cs.length_simple_mul_ne x i) with hdesc | hasc
  · let := F x
    apply FiniteFreeScalar.scalar_quotient_regular
      (Module.Free.chooseBasis (SymmetricCoefficient (M := M)) (bottStalk cs l x))
      (PairProjection.lower (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x)))
      (PairProjection.lower_surjective _ _ (bottStalkProjection_surjective cs l (cs.simple i*x)))
      (simpleRootPolynomial (M := M) i) β hα hβ
    intro z
    rw [PairProjection.kernel_lower]
    have hh := H.kernel_iff_of_mul cs (cs.simple i*x) x (cs.simple i)
      (simple_represents cs i) (cs.simple_mul_simple_cancel_left i) hdesc z
    simpa only [and_comm,simpleRootPolynomial,extendedRoot] using hh
  · let := F (cs.simple i*x)
    exact FiniteFreeScalar.scalar_quotient_regular
      (Module.Free.chooseBasis (SymmetricCoefficient (M := M)) (bottStalk cs l (cs.simple i*x)))
      (PairProjection.upper (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x)))
      (PairProjection.upper_surjective _ _ (bottStalkProjection_surjective cs l x))
      (simpleRootPolynomial (M := M) i) β hα hβ
      (H.upper_kernel cs x (cs.simple i) (simple_represents cs i) hasc)

 theorem bottHeadPairLattice_saturated (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x : W) (β : SymmetricCoefficient (M := M)) (hβ : ¬simpleRootPolynomial (M := M) i ∣ β)
    (p : bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x))) :
    β • p ∈ bottHeadPairLattice cs i l x ↔ p ∈ bottHeadPairLattice cs i l x :=
  lattice_saturated (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
    (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
    (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
    β (bottSimpleEdge_annihilated cs i l x) (bottSimpleEdge_regular cs i l H F x β hβ) p

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

 theorem bottHeadStalk_divisible (i : I) (l : List I)
    (H : BottKernelExact cs l)
    (F : ∀ x : W, Module.Free (SymmetricCoefficient (M := M)) (bottStalk cs l x))
    (x : W) (m : BottSamelsonModule cs (i::l)) (β : SymmetricCoefficient (M := M))
    (hβ : ¬simpleRootPolynomial (M := M) i ∣ β)
    (p : bottStalk cs l x × Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (bottStalk cs l (cs.simple i*x)))
    (hm : bottHeadLocalPair cs i l x m=β • p) :
    ∃ z : bottStalk cs (i::l) x, bottStalkProjection cs (i::l) x m=β • z := by
  have hp := bottHeadLocalPair_mem cs i l x m
  have hp' : β • p ∈ bottHeadPairLattice cs i l x := hm ▸ hp
  exact bottHeadStalk_divisible_of_pair cs i l x m β p hm
    ((bottHeadPairLattice_saturated cs i l H F x β hβ p).mp hp')

end
end KLInvariance.TitsSpace

end


section

/-! The genuine projection WORD sheaf with its nonnegative grading and finite
integral stalk/edge modules. No free-stalk, flabbiness, or KL character claim
is smuggled into the grading. The universe here contains both the finite
Coxeter matrix and its standard Coxeter group, as needed by the main reduction. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottPiece_negative (l : List I) (n : ℤ) (hn : n<0) :
    bottPiece cs basis l n=⊥ := by
  apply bot_unique
  intro m hm
  change m=0
  apply bottEvaluation_injective cs l
  funext e
  have h := bottEvaluation_homogeneous cs basis l e n m hm
  rw [symmetricGrading_negative basis n hn,Submodule.mem_bot] at h
  exact h.trans (map_zero (bottEvaluation cs l e)).symm

 def bottWordData (l : List I) : ModuleData.{0,u,u} (symmetricGrading basis) where
  obj := ModuleCat.of _ (BottSamelsonModule cs l)
  kModule := inferInstance
  tower := inferInstance
  piece := bottPiece cs basis l
  decomposition := inferInstance
  graded := inferInstance
  nonneg := bottPiece_negative cs basis l
  finite := inferInstance

 def bottStalkHom (l : List I) (x : W) :
    ModuleData.Hom (bottWordData cs basis l) (bottStalkData cs basis l x) where
  map := bottStalkProjection cs l x
  graded := bottStalkProjection_homogeneous cs basis l x

 theorem bottStalkHom_surjective (l : List I) (x : W) :
    Function.Surjective (bottStalkHom cs basis l x).map :=
  bottStalkProjection_surjective cs l x

 def bottEdgeData (l : List I) (x y : W) : ModuleData.{0,u,u} (symmetricGrading basis) :=
  ModuleData.pairEdge (bottStalkHom cs basis l x) (bottStalkHom cs basis l y)
    (bottStalkHom_surjective cs basis l y)

 def bottLowerHom (l : List I) (x y : W) :
    ModuleData.Hom (bottStalkData cs basis l x) (bottEdgeData cs basis l x y) :=
  ModuleData.pairLower (bottStalkHom cs basis l x) (bottStalkHom cs basis l y)
    (bottStalkHom_surjective cs basis l y)

 def bottUpperHom (l : List I) (x y : W) :
    ModuleData.Hom (bottStalkData cs basis l y) (bottEdgeData cs basis l x y) :=
  ModuleData.pairUpper (bottStalkHom cs basis l x) (bottStalkHom cs basis l y)
    (bottStalkHom_surjective cs basis l y)

 def bottGradedProjectionSheaf (l : List I) (u b : W) :
    GradedSheaf (𝓐 := symmetricGrading basis) (graph cs u b) where
  vertex x := bottStalkData cs basis l x.val
  edge e := bottEdgeData cs basis l (source cs u b e).val (target cs u b e).val
  lower e := bottLowerHom cs basis l (source cs u b e).val (target cs u b e).val
  upper e := bottUpperHom cs basis l (source cs u b e).val (target cs u b e).val

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BalancedPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded stalk duality, integral perfect balanced all-sections pairings, recognition and top grading.
-/


section

/-! The actual reduced word's top stalk is A in degree zero, integrally and
in BOTH grading directions. This is the normalization needed to start a BMP
summand construction, not a claim about the other stalks. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

omit [Fintype σ] in
 theorem bottTopStalkEquiv_homogeneous_iff (n : ℤ)
    (s : bottStalk cs l (cs.wordProd l)) :
    bottTopStalkEquiv cs l hl s ∈ symmetricGrading basis n ↔
      s ∈ bottStalkPiece cs basis l (cs.wordProd l) n := by
  constructor
  · intro hs e _
    have he : e=⟨bottFullIndex l,bottWeight_full cs l⟩ :=
      Subtype.ext (bottWeight_eq_top cs l hl e.val e.property)
    subst e
    exact hs
  · intro hs
    exact hs ⟨bottFullIndex l,bottWeight_full cs l⟩ (Set.mem_univ _)

 def bottTopHom : ModuleData.Hom (bottStalkData cs basis l (cs.wordProd l))
    (ModuleData.unit (symmetricGrading_negative basis)) where
  map := LinearMap.pi (fun _ => (bottTopStalkEquiv cs l hl).toLinearMap)
  graded := by
    intro n s hs j
    change bottTopStalkEquiv cs l hl s ∈ symmetricGrading basis (n-0)
    simpa only [sub_zero] using
      (bottTopStalkEquiv_homogeneous_iff cs basis l hl n s).mpr hs

 def bottTopInvHom : ModuleData.Hom (ModuleData.unit (symmetricGrading_negative basis))
    (bottStalkData cs basis l (cs.wordProd l)) where
  map := (bottTopStalkEquiv cs l hl).symm.toLinearMap.comp (LinearMap.proj PUnit.unit)
  graded := by
    intro n a ha
    apply (bottTopStalkEquiv_homogeneous_iff cs basis l hl n _).mp
    change bottTopStalkEquiv cs l hl ((bottTopStalkEquiv cs l hl).symm (a PUnit.unit)) ∈ _
    rw [LinearEquiv.apply_symm_apply]
    have h := ha PUnit.unit
    change a PUnit.unit ∈ symmetricGrading basis (n-0) at h
    simpa only [sub_zero] using h

 theorem bottTopHom_inv (a : ModuleData.unit (symmetricGrading_negative basis)) :
    (bottTopHom cs basis l hl).map ((bottTopInvHom cs basis l hl).map a)=a := by
  funext j
  change bottTopStalkEquiv cs l hl ((bottTopStalkEquiv cs l hl).symm (a PUnit.unit))=a j
  rw [LinearEquiv.apply_symm_apply]

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

 def bottBoundarySheafTopInclusion (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    ModuleData.Hom (B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
      (bottStalkData cs basis l (cs.wordProd l)) :=
  (bottTopInvHom cs basis l hl).comp
    ⟨(ModuleData.equivOfEq B.top).toLinearMap,ModuleData.equivOfEq_graded B.top⟩

 def bottBoundarySheafTopProjection (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    ModuleData.Hom (bottStalkData cs basis l (cs.wordProd l))
      (B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :=
  (⟨(ModuleData.equivOfEq B.top.symm).toLinearMap,ModuleData.equivOfEq_graded B.top.symm⟩ :
    ModuleData.Hom _ _).comp (bottTopHom cs basis l hl)

 theorem bottBoundarySheafTop_split (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
    (v : B.sheaf.vertex ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    (bottBoundarySheafTopProjection cs basis l hl B).map
      ((bottBoundarySheafTopInclusion cs basis l hl B).map v)=v := by
  change ModuleData.equivOfEq B.top.symm ((bottTopHom cs basis l hl).map
    ((bottTopInvHom cs basis l hl).map (ModuleData.equivOfEq B.top v)))=v
  rw [bottTopHom_inv]
  exact ModuleData.equivOfEq_inverse B.top v

end
end KLInvariance.TitsSpace

end


end OAI
end


