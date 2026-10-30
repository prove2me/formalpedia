-- Prove2me | Definitions.Def_OAIQ124K009
-- name    : OAIQ124K009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:50:41.166454+00:00
-- url     : https://prove2.me/theorems/8594d647-afdf-423e-996f-058359a41c30
-- title:
--   Definitions bundle OAIQ124K009 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 7 definitions and 23 theorems. The definitions and types are `OAI.KLInvariance.BruhatGraph.edgeFactorLift`, `OAI.KLInvariance.Graded.ModuleData.descended`, `OAI.KLInvariance.ReflectionPairTranslation.kernelEquiv`, `OAI.KLInvariance.ReflectionPairTranslation.kernelMap`, `OAI.KLInvariance.TitsSpace.bottHeadReflectedTail`, `OAI.KLInvariance.TitsSpace.bottHeadTail`, `OAI.KLInvariance.TitsSpace.bottSamelsonRight`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BalancedPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean), [`KazhdanLusztig_BottSamelson`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BottSamelson.lean), [`KazhdanLusztig_Frobenius`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Frobenius.lean), [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean), [`KazhdanLusztig_PlaneLocalization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/PlaneLocalization.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K004`, `OAIQ124K005` and `OAIQ124K006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K012`, `OAIQ124K013`, `OAIQ124K014` and `OAIQ124K015`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K004
import Definitions.Def_OAIQ124K005
import Definitions.Def_OAIQ124K006

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Frobenius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coxeter Frobenius extensions, tensor duality and translation across reflection pairs.
-/

section

namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem coefficientAction_mul (w z : W) (a : SymmetricCoefficient (M := M)) :
    coefficientAction cs (w*z) a = coefficientAction cs w (coefficientAction cs z a) := by
  have he : (coefficientAction cs (w*z)).toAlgHom =
      (coefficientAction cs w).toAlgHom.comp (coefficientAction cs z).toAlgHom := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro x
    change coefficientAction cs (w*z) (SymmetricAlgebra.ι ℝ (Extended M) x) =
      coefficientAction cs w (coefficientAction cs z (SymmetricAlgebra.ι ℝ (Extended M) x))
    simp only [coefficientAction_ι,map_mul,LinearEquiv.mul_apply]
  exact congrArg (fun f : SymmetricCoefficient (M := M) →ₐ[ℝ] SymmetricCoefficient (M := M) => f a) he

end
end KLInvariance.TitsSpace

end


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

/-! Genuine tensor-defined Bott--Samelson bimodules for the extended real
Coxeter realization. The perfect pairing is integral and balanced. This
construction alone does not identify indecomposable BMP summands or prove
the Elias--Williamson character theorem. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSamelsonRight (l : List I) : SymmetricCoefficient (M := M) →+*
    End (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l) :=
  (bottSamelson cs l).right

end
end KLInvariance.TitsSpace

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

 theorem coefficientAction_one (a : SymmetricCoefficient (M := M)) :
    coefficientAction cs 1 a = a := by
  have h := coefficientAction_mul cs 1 1 a
  rw [one_mul] at h
  exact (coefficientAction cs 1).injective h.symm

attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

end
end KLInvariance.TitsSpace

end


section

/-! Full reflection labels, rather than just simple-wall labels, in the
actual tensor bimodule coefficient action. -/
namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem coefficientAction_reflection {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    coefficientAction cs t = reflectionAction (embed M a) (extendedForm M (embed M a))
      (show extendedForm M (embed M a) (embed M a) = 2 by
        rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm) := by
  rw [coefficientAction,ha.extendedAction_eq]

 theorem reflectionCoefficient_anti {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    coefficientAction cs t (SymmetricAlgebra.ι ℝ (Extended M) (embed M a)) =
      -SymmetricAlgebra.ι ℝ (Extended M) (embed M a) := by
  rw [coefficientAction_reflection cs ha]
  exact reflectionAction_anti _ _ _

 theorem reflectionCoefficient_divisible {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (p : SymmetricCoefficient (M := M)) :
    SymmetricAlgebra.ι ℝ (Extended M) (embed M a) ∣ p-coefficientAction cs t p := by
  rw [coefficientAction_reflection cs ha]
  exact reflectionAction_divisible _ _ _ p

 theorem reflectionCoefficient_difference {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (x : W) : ∃ p : SymmetricCoefficient (M := M),
    coefficientAction cs x p-coefficientAction cs (t*x) p =
      SymmetricAlgebra.ι ℝ (Extended M) (embed M a) := by
  let α := SymmetricAlgebra.ι ℝ (Extended M) (embed M a)
  let c : SymmetricCoefficient (M := M) := (1/2 : ℝ) • α
  refine ⟨(coefficientAction cs x).symm c,?_⟩
  rw [coefficientAction_mul,AlgEquiv.apply_symm_apply]
  change (1/2 : ℝ) • α - coefficientAction cs t ((1/2 : ℝ) • α) = α
  rw [map_smul,reflectionCoefficient_anti cs ha]
  module

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

/-- The integral divisibility statement, before any localization. -/
theorem bottSimpleFlip_divisible (i : I) (l : List I) (m : BottSamelsonModule cs (i::l)) :
    ∃ n : BottSamelsonModule cs (i::l),
      m-bottSimpleFlip cs i l m = simpleRootPolynomial (M := M) i • n := by
  change SymmetricCoefficient (M := M) ⊗[simpleFixed cs i] BottSamelsonModule cs l at m
  induction m using OAI.tensorInductionOn with
  | add m n hm hn =>
    obtain ⟨m',hm'⟩ := hm
    obtain ⟨n',hn'⟩ := hn
    refine ⟨m'+n', ?_⟩
    erw [map_add, add_sub_add_comm, hm', hn', smul_add]
  | tmul a m =>
    obtain ⟨b,hb⟩ := simple_divisible cs i a
    refine ⟨b ⊗ₜ[simpleFixed cs i] m, ?_⟩
    erw [bottSimpleFlip_tmul, ← sub_tmul, hb]
    rfl


theorem simpleCoefficient_difference (i : I) (x : W) :
    ∃ p : SymmetricCoefficient (M := M),
      coefficientAction cs x p - coefficientAction cs (cs.simple i*x) p =
        simpleRootPolynomial (M := M) i := by
  let α := simpleRootPolynomial (M := M) i
  refine ⟨(coefficientAction cs x).symm ((1/2 : ℝ) • α), ?_⟩
  rw [coefficientAction_mul, AlgEquiv.apply_symm_apply]
  change (1/2 : ℝ) • α - coefficientAction cs (cs.simple i) ((1/2 : ℝ) • α) = α
  rw [map_smul, simple_anti]
  module


end
end KLInvariance.TitsSpace

end


section

/-! Integral simple-wall translation of a two-stalk projection lattice.
The hypotheses are explicit old-word edge properties, not character claims.
No freeness of a submodule is inferred merely from finite generation. -/
namespace KLInvariance.ReflectionPairTranslation
universe u v w z
variable {R : Type u} [CommRing R]

attribute [local instance] RingHomInvPair.of_ringEquiv

variable {N : Type v} [AddCommGroup N] [Module R N]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : N →ₗ[R] X) (g : N →ₗ[R] Y) (τ : R ≃+* R) (α : R)
  (hdiv : ∀ r : R, α ∣ τ r-r)
  (hinc : ∀ y : Y, ∃ n : N, f n=0 ∧ g n=α • y)

/-- Its kernel is the alpha-multiple of the twisted upper stalk. -/
def kernelMap : Twist τ Y →ₗ[R] LinearMap.ker (left f g τ α hdiv hinc) where
  toFun y := ⟨⟨(0,⟨α • y.val⟩),hinc y.val⟩,rfl⟩
  map_add' y z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change (0 : X)=0+0; simp
    · change Twist.mk (α • (y.val+z.val)) = Twist.mk (α • y.val+α • z.val)
      rw [smul_add]
  map_smul' r y := by
    apply Subtype.ext
    apply Subtype.ext
    change (0,Twist.mk (α • (τ r • y.val)))=(r • (0 : X),Twist.mk (τ r • (α • y.val)))
    rw [smul_zero,smul_comm α (τ r)]

 variable (hker : ∀ y : Y, (∃ n : N, f n=0 ∧ g n=y) ↔ ∃ z : Y, y=α • z)

 include hker in
 theorem kernelMap_surjective : Function.Surjective (kernelMap f g τ α hdiv hinc) := by
  rintro ⟨⟨⟨x,y⟩,n,hn,hn'⟩,hx⟩
  change x=0 at hx
  subst x
  obtain ⟨z,hz⟩ := (hker y.val).mp ⟨n,hn,hn'⟩
  refine ⟨⟨z⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext rfl (congrArg Twist.mk hz.symm)

 theorem kernelMap_injective (hinj : Function.Injective (fun y : Y => α • y)) :
    Function.Injective (kernelMap f g τ α hdiv hinc) := by
  intro y z h
  apply Twist.ext
  exact hinj (congrArg (fun p => p.val.val.2.val) h)

noncomputable def kernelEquiv (hinj : Function.Injective (fun y : Y => α • y)) :
    Twist τ Y ≃ₗ[R] LinearMap.ker (left f g τ α hdiv hinc) :=
  LinearEquiv.ofBijective (kernelMap f g τ α hdiv hinc)
    ⟨kernelMap_injective f g τ α hdiv hinc hinj,kernelMap_surjective f g τ α hdiv hinc hker⟩

 include hker in
 theorem lattice_free (hf : Function.Surjective f)
    (hinj : Function.Injective (fun y : Y => α • y))
    [Module.Free R X] [Module.Free R Y] :
    Module.Free R (lattice f g τ α hdiv hinc) := by
  let : Module.Free R (LinearMap.ker (left f g τ α hdiv hinc)) :=
    Module.Free.of_equiv (kernelEquiv f g τ α hdiv hinc hker hinj)
  exact free_of_surjective_of_ker_free (left f g τ α hdiv hinc)
    (left_surjective f g τ α hdiv hinc hf)

end KLInvariance.ReflectionPairTranslation

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
 theorem bottTensor_maps_eq (i : I) (l : List I)
    {P : Type up} [AddCommGroup P] [Module (SymmetricCoefficient (M := M)) P]
    (F G : BottSamelsonModule cs (i::l) →ₗ[SymmetricCoefficient (M := M)] P)
    (h : ∀ n : BottSamelsonModule cs l,
      F ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=
      G ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)) : F=G :=
  tensor_maps_eq_of_one_tmul (C := simpleFixed cs i)
    (A := SymmetricCoefficient (M := M)) (N := BottSamelsonModule cs l) F G h

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

 theorem simpleReverseDivisibility (i : I) (a : SymmetricCoefficient (M := M)) :
    simpleRootPolynomial (M := M) i ∣ coefficientAction cs (cs.simple i) a-a :=
  (dvd_sub_comm).mpr (simple_divisible cs i a)

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

 def bottHeadTail (i : I) (l : List I) : BottSamelsonModule cs (i::l) →ₗ[
    SymmetricCoefficient (M := M)] BottSamelsonModule cs l :=
  tensorFirst (C := simpleFixed cs i)

 def bottHeadReflectedTail (i : I) (l : List I) : BottSamelsonModule cs (i::l) →ₗ[
    SymmetricCoefficient (M := M)] Twist (coefficientAction cs (cs.simple i)).toRingEquiv
      (BottSamelsonModule cs l) :=
  tensorSecond (C := simpleFixed cs i) (coefficientAction cs (cs.simple i)).toRingEquiv
    (fun c => c.property)

 theorem bottHeadTail_seed (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    bottHeadTail cs i l ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=n := by
  exact one_smul _ n

 theorem bottHeadReflectedTail_seed (i : I) (l : List I) (n : BottSamelsonModule cs l) :
    bottHeadReflectedTail cs i l ((1 : SymmetricCoefficient (M := M)) ⊗ₜ[simpleFixed cs i] n)=Twist.mk n := by
  change Twist.mk ((coefficientAction cs (cs.simple i)) 1 • n)=Twist.mk n
  rw [map_one,one_smul]

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

 theorem represents_polynomial_prime {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    Prime (SymmetricAlgebra.ι ℝ (Extended M) (embed M a)) := by
  apply EdgeAlgebra.symmetric_ι_prime
  intro h
  exact ha.isRoot.ne_zero (congrArg Prod.fst h)

 theorem represents_polynomial_not_dvd {t s : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b) (hne : t≠s) :
    ¬ SymmetricAlgebra.ι ℝ (Extended M) (embed M a) ∣
      SymmetricAlgebra.ι ℝ (Extended M) (embed M b) := by
  rw [EdgeAlgebra.symmetric_ι_dvd_iff]
  intro h
  have hi := hb.extended_independent_of_ne ha (Ne.symm hne)
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp h
  exact (linearIndependent_fin2.mp hi).2 r hr

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

 omit [Fintype I] in
 theorem BruhatUpper.mem_simpleInter (U : Set W) (hU : BruhatUpper cs U) (i : I) (x : W) :
    x∈simpleInter cs i U ↔ lowerSimple cs i x∈U := by
  constructor
  · rintro ⟨hx,hsx⟩
    classical
    unfold lowerSimple
    split_ifs <;> assumption
  · intro hx
    refine ⟨hU (lowerSimple_le cs i x) hx,?_⟩
    have he : lowerSimple cs i (cs.simple i*x)∈U := by simpa only [lowerSimple_mul] using hx
    exact hU (lowerSimple_le cs i (cs.simple i*x)) he

include klPreservedInstance11 in
 theorem BruhatUpper.simpleInter (U : Set W) (hU : BruhatUpper cs U) (i : I) :
    BruhatUpper cs (simpleInter cs i U) := by
  have _ := klPreservedInstance11
  intro x y hxy hx
  exact (hU.mem_simpleInter cs U i y).mpr
    (hU (lowerSimple_mono cs i hxy) ((hU.mem_simpleInter cs U i x).mp hx))

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

/-- Separate one residue-character class from its complement without
inverting any element of the coefficient domain. -/
 theorem class_projector [Fintype X] (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p)
    (C : Finset X) (x : X)
    (test : X → X → R) (htest : ∀ y, test y ∈ stabilizer L)
    (hzero : ∀ y ∉ C, test y y=0)
    (hunit : ∀ y ∉ C, ¬ p ∣ test y x)
    (hcongr : ∀ z ∈ C, ∀ y, p ∣ test y z-test y x) :
    ∃ d : R, ¬ p ∣ d ∧ ∃ g ∈ stabilizer L,
      (∀ z ∈ C, g z=d) ∧ (∀ z ∉ C, g z=0) := by
  classical
  let f : X → R := ∏ y ∈ Finset.univ \ C, test y
  have hf : f ∈ stabilizer L :=
    (stabilizer L).prod_mem fun y _ => htest y
  have hfu (z : X) (hz : z ∈ C) : ¬ p ∣ f z := by
    dsimp [f]
    rw [Finset.prod_apply]
    apply hp.not_dvd_finsetProd
    intro y hy
    have hyC := (Finset.mem_sdiff.mp hy).2
    intro h
    apply hunit y hyC
    simpa only [sub_sub_cancel] using dvd_sub h (hcongr z hz y)
  have hfz (z : X) (hz : z ∉ C) : f z=0 := by
    dsimp [f]
    rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hz⟩) (hzero z hz)
  obtain ⟨g,hg,hgc,hgz⟩ := uniform_projector L C f hf hfz
  refine ⟨∏ z ∈ C, f z,?_,g,hg,hgc,hgz⟩
  exact hp.not_dvd_finsetProd (fun z hz => hfu z hz)

/-- Local lifts on each finite character block assemble after a single
scalar denominator away from the prime. -/
 theorem partition_local_denominator {Q : Type*} [Fintype Q]
    (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p) (q : X → Q)
    (z : ∀ x, E x) (d : Q → R) (hd : ∀ j, ¬ p ∣ d j)
    (g : Q → X → R) (hg : ∀ j, g j ∈ stabilizer L)
    (hgin : ∀ j x, q x=j → g j x=d j)
    (hgout : ∀ j x, q x≠j → g j x=0)
    (m : Q → ∀ x, E x) (hm : ∀ j, m j ∈ L)
    (hmatch : ∀ j x, q x=j → m j x=z x) :
    ∃ a : R, ¬ p ∣ a ∧ a • z ∈ L := by
  classical
  refine ⟨∏ j, d j,hp.not_dvd_finsetProd (fun j _ => hd j),?_⟩
  have hh : (∑ j : Q, (∏ k ∈ Finset.univ.erase j, d k) •
      diagonal (g j) (m j)) ∈ L := by
    exact L.sum_mem fun j _ => L.smul_mem _ (hg j _ (hm j))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [Pi.smul_apply,Finset.sum_apply]
  rw [Finset.sum_eq_single (q x)]
  · change (∏ j, d j) • z x = (∏ k ∈ Finset.univ.erase (q x),d k) •
      (g (q x) x • m (q x) x)
    rw [hgin _ _ rfl,hmatch _ _ rfl,← mul_smul,
      Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  · intro j _ hj
    change (∏ k ∈ Finset.univ.erase j,d k) • (g j x • m j x)=0
    rw [hgout j x (Ne.symm hj),zero_smul,smul_zero]
  · simp

 theorem character_class_projector [Fintype X] {A : Type*}
    (L : Submodule R (∀ x, E x)) (p : R) (hp : Prime p)
    (χ : A → X → R) (hχ : ∀ a, χ a ∈ stabilizer L) (x : X) :
    ∃ d : R, ¬ p ∣ d ∧ ∃ g ∈ stabilizer L,
      (∀ z, (residueSetoid p χ).r x z → g z=d) ∧
      (∀ z, ¬ (residueSetoid p χ).r x z → g z=0) := by
  classical
  let C : Finset X := Finset.univ.filter ((residueSetoid p χ).r x)
  have hc (z : X) : z ∈ C ↔ (residueSetoid p χ).r x z := by simp [C]
  have ha : ∀ y : {y : X // y ∉ C}, ∃ a, ¬ p ∣ χ a x-χ a y.val := by
    intro y
    have hh : ¬ ∀ a, p ∣ χ a x-χ a y.val := fun h => y.property ((hc _).mpr h)
    exact not_forall.mp hh
  choose a ha using ha
  let test (y : X) : X → R := if hy : y ∉ C then
    χ (a ⟨y,hy⟩)-algebraMap R (X → R) (χ (a ⟨y,hy⟩) y) else 0
  have ht (y : X) : test y ∈ stabilizer L := by
    by_cases hy : y ∉ C
    · simp only [test,dite_eq_left hy]
      exact (stabilizer L).sub_mem (hχ _) ((stabilizer L).algebraMap_mem _)
    · simp only [test,dite_eq_right hy]
      exact (stabilizer L).zero_mem
  have hz (y : X) (hy : y ∉ C) : test y y=0 := by simp [test,hy]
  have hu (y : X) (hy : y ∉ C) : ¬ p ∣ test y x := by simpa [test,hy] using ha ⟨y,hy⟩
  have hcon (z : X) (hz : z ∈ C) (y : X) : p ∣ test y z-test y x := by
    by_cases hy : y ∉ C
    · simp only [test,dite_eq_left hy]
      change p ∣ (χ (a ⟨y,hy⟩) z-χ (a ⟨y,hy⟩) y)-
        (χ (a ⟨y,hy⟩) x-χ (a ⟨y,hy⟩) y)
      rw [sub_sub_sub_cancel_right]
      exact (residueSetoid p χ).symm ((hc z).mp hz) _
    · simp only [test,dite_eq_right hy,Pi.zero_apply,sub_self]
      exact dvd_zero _
  obtain ⟨d,hd,g,hg,hgc,hgz⟩ := class_projector L p hp C x test ht hz hu hcon
  exact ⟨d,hd,g,hg,fun z h => hgc z ((hc z).mpr h),
    fun z h => hgz z (fun hz => h ((hc z).mp hz))⟩

end
end KLInvariance.FiniteCharacterLocalization

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

namespace KLInvariance.Graded.ModuleData
open PairProjection LinearDescent
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M X Y : ModuleData.{uk,ua,um} 𝓐}
  (e : Hom M M) (f : Hom M X) (g : Hom M Y)
  (hf : Function.Surjective f.map) (hg : Function.Surjective g.map)
  (hef : ∀ m, f.map m=0 → f.map (e.map m)=0)
  (heg : ∀ m, g.map m=0 → g.map (e.map m)=0)
noncomputable section

 def descended : Hom X X where
  map := descend f.map hf e.map hef
  graded := by
    intro n x hx
    obtain ⟨m,hm,rfl⟩ := f.homogeneous_lift hf n x hx
    rw [descend_apply]
    exact f.graded n _ (e.graded n m hm)

include heg in
 theorem lower_kernel_preserved (x : X) (hx : lower f.map g.map x=0) :
    lower f.map g.map ((descended e f hf hef).map x)=0 := by
  obtain ⟨m,hm,hn⟩ := (kernel_lower f.map g.map x).mp hx
  apply (kernel_lower f.map g.map _).mpr
  refine ⟨e.map m,?_,heg m hn⟩
  rw [← hm]
  exact (descend_apply f.map hf e.map hef m).symm

end
end KLInvariance.Graded.ModuleData

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PlaneLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Symmetric plane ideals, sheaf localization and scaled local products along genuine edges.
-/


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section


 def edgeFactorLift (x : W) (a : PositiveRoot M cs) : Coefficient (σ := σ) :=
  ∏ P : (planeWeight x a).support,
    polynomialRoot cs basis (planeRoot x a P) ^ (planeWeight x a P.val).toNat

end
end KLInvariance.BruhatGraph

end


end OAI
end


