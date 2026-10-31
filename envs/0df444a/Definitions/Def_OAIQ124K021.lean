-- Prove2me | Definitions.Def_OAIQ124K021
-- name    : OAIQ124K021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:10:03.813773+00:00
-- url     : https://prove2.me/theorems/5482deb4-2fad-402a-ae24-f7e0ff1bf63d
-- title:
--   Definitions bundle OAIQ124K021 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 15 declarations of OpenAI's Lean: 6 definitions, 2 instances and 7 theorems. The definitions and types are `OAI.KLInvariance.TitsSpace.bottHeadKernelEquiv`, `OAI.KLInvariance.TitsSpace.bottHeadKernelPiece`, `OAI.KLInvariance.TitsSpace.bottHeadLeft`, `OAI.KLInvariance.TitsSpace.bottHeadRight`, `OAI.KLInvariance.TitsSpace.bottHeadRightKernelEquiv`, `OAI.KLInvariance.TitsSpace.bottHeadRightKernelPiece`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BalancedPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean), [`KazhdanLusztig_BottSamelson`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BottSamelson.lean).
--
--   **Imports.** It imports the bundles `OAIQ124K016`, `OAIQ124K017` and `OAIQ124K018` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ124K023`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ124K016
import Definitions.Def_OAIQ124K017
import Definitions.Def_OAIQ124K018

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.bottSetImageAddCommGroup _root_.OAI.KLInvariance.TitsSpace.bottSetImageModule _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! The genuine head-word projection maps, on the fixed real field, preserve
homogeneous degrees. These maps are not abstract character operators. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded ReflectionPairTranslation
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def bottHeadLeft (i : I) (l : List I) (x : W) :
    bottStalk cs (i::l) x →ₗ[SymmetricCoefficient (M := M)] bottStalk cs l x :=
  (ReflectionPairTranslation.left (bottStalkProjection cs l x)
    (bottStalkProjection cs l (cs.simple i*x)) (coefficientAction cs (cs.simple i)).toRingEquiv
    (simpleRootPolynomial (M := M) i) (simpleReverseDivisibility cs i)
    (bottSimpleEdge_kernel_inclusion cs i l x)).comp (bottHeadPairEquiv cs i l x).symm.toLinearMap

 def bottHeadRight (i : I) (l : List I) (x : W) :
    bottStalk cs (i::l) x →ₗ[ℝ] bottStalk cs l (cs.simple i*x) :=
  (Twist.scalarEquiv (coefficientAction cs (cs.simple i)) _).toLinearMap.comp
    (((LinearMap.snd (SymmetricCoefficient (M := M)) (bottStalk cs l x)
      (Twist (coefficientAction cs (cs.simple i)).toRingEquiv (bottStalk cs l (cs.simple i*x)))).comp
        ((bottHeadPairLattice cs i l x).subtype.comp
          (bottHeadPairEquiv cs i l x).symm.toLinearMap)).restrictScalars ℝ)

 theorem bottHeadPairEquiv_coordinates (i : I) (l : List I) (x : W)
    (m : bottStalk cs (i::l) x) :
    bottHeadPairCoordinates cs i l x ((bottHeadPairEquiv cs i l x).symm m).val=m.val :=
  congrArg Subtype.val ((bottHeadPairEquiv cs i l x).apply_symm_apply m)

omit [Fintype σ] in
 theorem bottHeadLeft_homogeneous (i : I) (l : List I) (x : W) (n : ℤ)
    (m : bottStalk cs (i::l) x) (hm : m ∈ bottStalkPiece cs basis (i::l) x n) :
    bottHeadLeft cs i l x m ∈ bottStalkPiece cs basis l x n := by
  intro e _
  change (bottHeadLeft cs i l x m).val e ∈ symmetricGrading basis n
  let E : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x} :=
    ⟨(0,e.val),by simpa only [bottWeight,ite_true, if_true] using e.property⟩
  have he := congrFun (bottHeadPairEquiv_coordinates cs i l x m) E
  have hh : (bottHeadLeft cs i l x m).val e=m.val E := by
    change ((bottHeadPairEquiv cs i l x).symm m).val.1.val e=m.val E at he
    exact he
  rw [hh]
  exact hm E (Set.mem_univ E)

 theorem bottHeadRight_homogeneous (i : I) (l : List I) (x : W) (n : ℤ)
    (m : bottStalk cs (i::l) x) (hm : m ∈ bottStalkPiece cs basis (i::l) x n) :
    bottHeadRight cs i l x m ∈ bottStalkPiece cs basis l (cs.simple i*x) n := by
  intro e _
  change (bottHeadRight cs i l x m).val e ∈ symmetricGrading basis n
  let E : {e : BottIndex (i::l) // bottWeight cs (i::l) e=x} :=
    ⟨(1,e.val),by simp only [bottWeight,ite_eq_right (show (1:Fin 2)≠0 by decide),
      e.property,cs.simple_mul_simple_cancel_left]⟩
  have he := congrFun (bottHeadPairEquiv_coordinates cs i l x m) E
  have hh : coefficientAction cs (cs.simple i) ((bottHeadRight cs i l x m).val e)=m.val E := by
    change coefficientAction cs (cs.simple i)
      (((bottHeadPairEquiv cs i l x).symm m).val.2.val.val e)=m.val E at he
    exact he
  have h := coefficientAction_homogeneous cs basis (cs.simple i) n (m.val E)
    (hm E (Set.mem_univ E))
  rw [← hh,simple_involutive] at h
  exact h

end
end KLInvariance.TitsSpace

end


section

/-! The actual ascent short exact sequence of word stalks has kernel the
upper tail stalk shifted by one. This is the degree-one Hecke normalization. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded ReflectionPairTranslation
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def bottHeadKernelEquiv (i : I) (l : List I) (x : W)
    (h : cs.length x < cs.length (cs.simple i*x)) :
    bottStalk cs l (cs.simple i*x) ≃ₗ[ℝ] LinearMap.ker (bottHeadLeft cs i l x) :=
  (Twist.scalarEquiv (coefficientAction cs (cs.simple i)) _).symm.trans
    (((kernelEquiv (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
      (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
      (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
      ((bottKernelExact cs l).kernel_iff cs x (cs.simple i) (simple_represents cs i) h)
      (bottStalk_smul_injective cs l (cs.simple i*x) (simpleRootPolynomial_ne_zero i))).trans
      (kernelSourceEquiv _ (bottHeadPairEquiv cs i l x))).restrictScalars ℝ)

 def bottHeadKernelPiece (i : I) (l : List I) (x : W) :
    ℤ → Submodule ℝ (LinearMap.ker (bottHeadLeft cs i l x)) :=
  subPiece (bottStalkPiece cs basis (i::l) x) (LinearMap.ker (bottHeadLeft cs i l x))

 theorem bottHeadLeft_kernel_homogeneous (i : I) (l : List I) (x : W) :
    ∀ n m, m ∈ LinearMap.ker (bottHeadLeft cs i l x) →
      component (bottStalkPiece cs basis (i::l) x) n m ∈ LinearMap.ker (bottHeadLeft cs i l x) := by
  intro n m hm
  have h := map_component (bottStalkPiece cs basis (i::l) x) (bottStalkPiece cs basis l x)
    (bottHeadLeft cs i l x) 0 (by
      intro j z hz
      simpa only [add_zero] using (bottHeadLeft_homogeneous cs basis i l x j z hz)) n m
  change bottHeadLeft cs i l x _=0
  rw [sub_zero] at h
  rw [← h,LinearMap.mem_ker.mp hm,map_zero]

 instance bottHeadKernelPiece_decomposition (i : I) (l : List I) (x : W) :
    DirectSum.Decomposition (bottHeadKernelPiece cs basis i l x) :=
  (sub_isInternal (bottStalkPiece cs basis (i::l) x) (LinearMap.ker (bottHeadLeft cs i l x))
    (bottHeadLeft_kernel_homogeneous cs basis i l x)).chooseDecomposition

end
end KLInvariance.TitsSpace

end


section

/-! The descent short exact sequence for the actual word projection lattice.
Its kernel has the genuine degree-one shift, over the unchanged realization. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded ReflectionPairTranslation
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottDescentKernel (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x) < cs.length x) (z : bottStalk cs l x) :
    (∃ n, bottStalkProjection cs l x n=z ∧ bottStalkProjection cs l (cs.simple i*x) n=0) ↔
      ∃ w, z=simpleRootPolynomial (M := M) i • w := by
  have hh := (bottKernelExact cs l).kernel_iff_of_mul cs (cs.simple i*x) x (cs.simple i)
    (simple_represents cs i) (cs.simple_mul_simple_cancel_left i) h z
  simpa only [and_comm,simpleRootPolynomial,embed,extendedRoot] using hh

 def bottHeadRightKernelEquiv (i : I) (l : List I) (x : W)
    (h : cs.length (cs.simple i*x) < cs.length x) :
    bottStalk cs l x ≃ₗ[ℝ] LinearMap.ker (bottHeadRight cs i l x) :=
  ((rightKernelEquiv (bottStalkProjection cs l x) (bottStalkProjection cs l (cs.simple i*x))
      (coefficientAction cs (cs.simple i)).toRingEquiv (simpleRootPolynomial (M := M) i)
      (simpleReverseDivisibility cs i) (bottSimpleEdge_kernel_inclusion cs i l x)
      (bottDescentKernel cs i l x h)
      (bottStalk_smul_injective cs l x (simpleRootPolynomial_ne_zero i))).restrictScalars ℝ).trans
    (kernelMixedEquiv _ (bottHeadPairEquiv cs i l x)
      (Twist.scalarEquiv (coefficientAction cs (cs.simple i)) _))

 def bottHeadRightKernelPiece (i : I) (l : List I) (x : W) :
    ℤ → Submodule ℝ (LinearMap.ker (bottHeadRight cs i l x)) :=
  subPiece (bottStalkPiece cs basis (i::l) x) (LinearMap.ker (bottHeadRight cs i l x))

 theorem bottHeadRight_kernel_homogeneous (i : I) (l : List I) (x : W) :
    ∀ n m, m ∈ LinearMap.ker (bottHeadRight cs i l x) →
      component (bottStalkPiece cs basis (i::l) x) n m ∈ LinearMap.ker (bottHeadRight cs i l x) := by
  exact kernel_homogeneous (A := ℝ) (bottStalkPiece cs basis (i::l) x)
    (bottStalkPiece cs basis l (cs.simple i*x)) (bottHeadRight cs i l x) 0 (by
      intro j z hz
      simpa only [add_zero] using (bottHeadRight_homogeneous cs basis i l x j z hz))

 instance bottHeadRightKernelPiece_decomposition (i : I) (l : List I) (x : W) :
    DirectSum.Decomposition (bottHeadRightKernelPiece cs basis i l x) :=
  (sub_isInternal (bottStalkPiece cs basis (i::l) x) (LinearMap.ker (bottHeadRight cs i l x))
    (bottHeadRight_kernel_homogeneous cs basis i l x)).chooseDecomposition

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BalancedPairings
attribute [-instance] _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded stalk duality, integral perfect balanced all-sections pairings, recognition and top grading.
-/


section

/-! A specified integral graded sheaf splitting identifies its source with
its literal projector image. No existence of a word/BMP splitting is assumed
outside each explicitly parametric helper. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G} (s : SplitIn B C)
noncomputable section

 theorem SplitIn.toImage_imageTo_vertex (x : V) (v : s.projector.image.vertex x) :
    (s.toImage.vertex x).map ((s.imageTo.vertex x).map v)=v := by
  apply Subtype.ext
  obtain ⟨m,hm⟩ := v.property
  change (s.projector.vertex x).map ((s.projector.vertex x).map v.val)=v.val
  rw [s.projector_vertex,← hm,s.projector_vertex]

end
end KLInvariance.MomentGraph.GradedSheaf

end


end OAI
end


