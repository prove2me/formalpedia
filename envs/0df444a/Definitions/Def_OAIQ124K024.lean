-- Prove2me | Definitions.Def_OAIQ124K024
-- name    : OAIQ124K024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:57:47.115863+00:00
-- url     : https://prove2.me/theorems/85dabef6-a878-422d-80c0-c84ee8ad3865
-- title:
--   Definitions bundle OAIQ124K024 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 24 declarations of OpenAI's Lean: 7 definitions and 17 theorems. The definitions and types are `OAI.KLInvariance.BruhatGraph.actualSectionDuality`, `OAI.KLInvariance.BruhatGraph.actualSymmetricPairing`, `OAI.KLInvariance.BruhatGraph.boundaryFreeDuality`, `OAI.KLInvariance.BruhatGraph.boundaryPerfectPairing`, `OAI.KLInvariance.BruhatGraph.costalkCharacter`, `OAI.KLInvariance.TitsSpace.bottCanonicalAdjointIso`, `OAI.KLInvariance.TitsSpace.bottCanonicalPerfectPairing`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_CharacterReciprocity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean), [`KazhdanLusztig_EdgeLocalization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/EdgeLocalization.lean), [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean), [`KazhdanLusztig_PositiveTransfer`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/PositiveTransfer.lean), [`KazhdanLusztig_Support`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Support.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K022`, `OAIQ124K033` and `OAIQ124K023` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.KLInvariance.BruhatGraph.actual_comparison_of_upper_freeness`, `OAI.KLInvariance.BruhatGraph.actual_endpoint_of_rTilde_eq`, `OAI.KLInvariance.BruhatGraph.scaledStalk_reciprocity_upper` and `OAI.KLInvariance.TitsSpace.bottCharacter_decomposition_both`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K022
import Definitions.Def_OAIQ124K033
import Definitions.Def_OAIQ124K023

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_IntegralPairings
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert recurrences, projective section ranges, integral lattices and graded perfect adjoints.
-/


section

/-! Unconditional flabbiness of the actual integral tensor-word projection
sheaf, obtained from projectivity of every upper-coordinate image. -/
namespace KLInvariance.TitsSpace
open Module CoordinateProjection
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottProjectiveUpper (l : List I) : BottProjectiveUpper cs l := by
  induction l with
  | nil => exact fun U _ => bottSetImage_nil_projective cs U
  | cons i l ih => exact bottProjectiveUpper_cons cs i l ih (bottFlabby_of_projective cs l ih)

 theorem bottFlabby (l : List I) : BottFlabby cs l :=
  bottFlabby_of_projective cs l (bottProjectiveUpper cs l)

end
end KLInvariance.TitsSpace

end


section

/-! Flabbiness of the genuine interval word sheaf; the extension outside the
finite support is zero, not an extra assumption on the source interval. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 theorem bottProjectionSheaf_flabby (l : List I) (hl : cs.IsReduced l) :
    (bottProjectionSheaf cs l 1 (cs.wordProd l)).Flabby := by
  intro U hU f hf
  obtain ⟨m,hm⟩ := bottFlabby cs l _ (intervalUpperClosure_upper cs _ U)
    (bottIntervalExtension cs l U f) (bottIntervalExtension_compatible cs l hl U hU f hf)
  refine ⟨(bottSection cs l 1 (cs.wordProd l) m).val,(bottSection cs l 1 (cs.wordProd l) m).property,?_⟩
  intro x hx
  exact (congrFun hm ⟨x.val,x,hx,bruhat_refl cs x.val⟩).trans
    (bottIntervalExtension_apply cs l U f x ⟨x,hx,bruhat_refl cs x.val⟩)

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Support
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
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

 theorem bottBoundarySheaf_splitIn (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    Nonempty (GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))) := by
  classical
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 (cs.wordProd l)
  let := Fintype.ofFinite (Interval cs 1 (cs.wordProd l))
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  exact B.splitIn_of_top_split (symmetricGrading_zero basis) (fun x => x.property.2)
    (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
    (bottGradedProjectionSheaf_upperQuotient cs basis l 1 (cs.wordProd l))
    (fun x => bottStalkFree cs l x.val) (bottProjectionSheaf_flabby cs l hl)
    (bottProjectionSheaf_generated cs l 1 (cs.wordProd l))
    (bottBoundarySheafTopInclusion cs basis l hl B) (bottBoundarySheafTopProjection cs basis l hl B)
    (bottBoundarySheafTop_split cs basis l hl B)

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section

/-! The actual symmetric-coefficient BMP boundary sheaf is isomorphic to
its integral adjoint image. The splitting is constructed from the word's
proved free-stalk, exact-edge and flabbiness properties. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottBoundarySheaf_iso_adjoint : Nonempty
    (GradedSheaf.Iso B.sheaf (bottSplitAdjointSheaf cs basis l hl B.sheaf s)) := by
  classical
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 (cs.wordProd l)
  let := Fintype.ofFinite (Interval cs 1 (cs.wordProd l))
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  let t := bottSplitAdjointSplit cs basis l hl B s
  exact B.iso_of_primitive_top_split (symmetricGrading_zero basis) (fun x => x.property.2)
    (bottSplitAdjointSheaf cs basis l hl B.sheaf s)
    (t.upperQuotient (bottGradedProjectionSheaf_upperQuotient cs basis l 1 (cs.wordProd l)))
    (bottSplitAdjoint_free cs basis l hl B s)
    (t.flabby (bottProjectionSheaf_flabby cs l hl))
    (t.generated (bottProjectionSheaf_generated cs l 1 (cs.wordProd l)))
    (bottBoundarySplitAdjoint_primitive cs basis l hl _ B s)
    (bottSplitAdjointTopInclusion cs basis l hl B s)
    (bottSplitAdjointTopProjection cs basis l hl B s)
    (bottSplitAdjointTop_split cs basis l hl B s)

end
end KLInvariance.TitsSpace

end


section

/-! Unconditional integral graded support-orthogonal duality for the actual
normalized minimal-boundary sheaf over the symmetric coefficient algebra. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem symmetricBoundarySheaf_perfectPairing_word (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    Nonempty (GradedSheaf.PerfectPairing B.sheaf (cs.length (cs.wordProd l) : ℤ)) := by
  obtain ⟨s⟩ := bottBoundarySheaf_splitIn cs basis l hl B
  obtain ⟨j⟩ := bottBoundarySheaf_iso_adjoint cs basis l hl B s
  have hd : cs.length (cs.wordProd l)=l.length := hl
  rw [hd]
  exact ⟨bottRecognizedPerfectPairing cs basis l hl B.sheaf s j⟩

 theorem symmetricBoundarySheaf_perfectPairing (b : W) :
    Nonempty (GradedSheaf.PerfectPairing (symmetricBoundarySheaf cs basis b).sheaf (cs.length b : ℤ)) := by
  obtain ⟨l,hl,he⟩ := cs.exists_isReduced b
  subst b
  exact symmetricBoundarySheaf_perfectPairing_word cs basis l hl _

end
end KLInvariance.TitsSpace

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem boundarySheaf_perfectPairing :
    Nonempty (GradedSheaf.PerfectPairing
      (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf (cs.length b : ℤ)) := by
  classical
  let := interval_finite cs 1 b
  let := Fintype.ofFinite (Interval cs 1 b)
  let := Fintype.ofFinite (Edge cs 1 b)
  let S := symmetricBoundarySheaf cs basis b
  let T := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let e := SymmetricAlgebra.equivMvPolynomial basis
  have he : ∀ n a, a∈symmetricGrading basis n ↔ e a∈polynomialGrading ℝ σ n :=
    mem_symmetricGrading basis
  obtain ⟨p⟩ := symmetricBoundarySheaf_perfectPairing cs basis b
  obtain ⟨j⟩ := BoundarySheaf.iso_coefficientChange e he S T
    (polynomialGrading_zero ℝ σ) (fun x => x.property.2)
  exact ⟨(p.coefficientChange e he).pullback j⟩

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.finiteInterval
attribute [local instance] OAI.KLInvariance.BruhatGraph.finiteEdges
attribute [local instance] OAI.KLInvariance.BruhatGraph.charDecEqC
def boundaryPerfectPairing : GradedSheaf.PerfectPairing
    (boundaryFreeSheaf cs b basis).sheaf (cs.length b : ℤ) :=
  (boundarySheaf_perfectPairing cs b basis).some

 def boundaryFreeDuality : FreeSheaf.SectionDuality cs 1 b basis (boundaryFreeSheaf cs b basis) :=
  FreeSheaf.dualityOfPairing cs 1 b basis _ (boundaryPerfectPairing cs b basis)

 theorem boundaryKernelFree (x : Interval cs 1 b) :
    Module.Free (Coefficient (σ := σ))
      (GradedSheaf.kernelData (boundaryFreeSheaf cs b basis).sheaf x) :=
  FreeSheaf.kernel_free cs b basis _ (boundaryFreeDuality cs b basis) x

 def costalkCharacter (x : Interval cs 1 b) : Polynomial ℤ :=
  GradedSheaf.freeKernelChar (boundaryFreeSheaf cs b basis).sheaf (boundaryKernelFree cs b basis) x

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_2
theorem boundaryModels_kernelFree (c x : Interval cs 1 b) :
    Module.Free (Coefficient (σ := σ))
      (GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x) := by
  by_cases hx : x ≤ c
  · let := boundaryKernelFree cs c.val basis ⟨x.val,x.property.1,hx⟩
    exact Module.Free.of_equiv (lowerKernelEquiv cs b basis c x hx).symm
  · let := (boundaryModels cs b basis).support c x hx
    let : Subsingleton (GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x) :=
      ⟨fun v w => Subtype.ext (Subsingleton.elim _ _)⟩
    infer_instance

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_EdgeLocalization
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bruhat sheaf localization, graded transport, local edge-image bounds and support.
-/


section

/-! The CANONICAL map from a normalized BMP summand to its adjoint image is
invertible. Consequently the ambient WORD form restricts perfectly on this
particular summand; no such assertion is made for an arbitrary summand. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 def bottCanonicalAdjointIso : GradedSheaf.Iso B.sheaf
    (bottSplitAdjointSheaf cs basis l hl B.sheaf s) := by
  classical
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 (cs.wordProd l)
  let := Fintype.ofFinite (Interval cs 1 (cs.wordProd l))
  let := Fintype.ofFinite (Edge cs 1 (cs.wordProd l))
  let j := (bottBoundarySheaf_iso_adjoint cs basis l hl B s).some
  exact B.homIsoOfIso (symmetricGrading_zero basis) j
    ((bottSplitAdjointSplit cs basis l hl B s).upperQuotient
      (bottGradedProjectionSheaf_upperQuotient cs basis l 1 (cs.wordProd l)))
    (bottCanonicalAdjointHom cs basis l hl B s)
    (bottCanonicalAdjointHom_top_bijective cs basis l hl B s)

 theorem bottCanonicalAdjointIso_vertex (x : Interval cs 1 (cs.wordProd l))
    (v : B.sheaf.vertex x) :
    ((bottCanonicalAdjointIso cs basis l hl B s).vertex x v).val=
      ((bottAdjointSheaf cs basis l hl s.projector).vertex x).map
        ((s.inclusion.vertex x).map v) := rfl

end
end KLInvariance.TitsSpace

end


section

/-! On the normalized BMP summand the canonical adjoint recognition proves,
rather than assumes, perfection of the restricted symmetric word form. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottCanonicalAdjointWord (m : B.sheaf.forget.sections Set.univ) :
    bottSplitLeftWord cs basis l hl B.sheaf s
      ((bottCanonicalAdjointIso cs basis l hl B s).toIso.sections Set.univ m)=
    bottAdjoint cs l (bottEndOfSheaf cs basis l hl s.projector)
      (bottSplitRightWord cs basis l hl B.sheaf s m) := by
  apply bottVertexProjection_injective cs l hl
  funext x
  change bottStalkProjection cs l x.val _=bottStalkProjection cs l x.val _
  rw [bottSplitLeftWord_coordinates]
  exact (bottCanonicalAdjointIso_vertex cs basis l hl B s x (m.val x)).trans
    ((congrArg ((bottAdjointSheaf cs basis l hl s.projector).vertex x).map
      (bottSplitRightWord_coordinates cs basis l hl B.sheaf s m x).symm).trans
      (bottAdjointSheaf_vertex cs basis l hl s.projector x _))

 def bottCanonicalPerfectPairing : GradedSheaf.PerfectPairing B.sheaf (l.length : ℤ) :=
  bottRecognizedPerfectPairing cs basis l hl B.sheaf s
    (bottCanonicalAdjointIso cs basis l hl B s)

 theorem bottCanonicalPerfectPairing_apply (m n : B.sheaf.forget.sections Set.univ) :
    (bottCanonicalPerfectPairing cs basis l hl B s).pairing m n=
      bottSamelsonDuality cs l (bottSplitRightWord cs basis l hl B.sheaf s m)
        (bottSplitRightWord cs basis l hl B.sheaf s n) := by
  change bottSplitAdjointEquivDual cs basis l hl B.sheaf s
    ((bottCanonicalAdjointIso cs basis l hl B s).toIso.sections Set.univ m) n=_
  rw [bottSplitAdjointWord_apply,bottCanonicalAdjointWord]
  change bottSamelsonDuality cs l
    (PerfectAdjoint.adjoint (bottSamelsonDuality cs l)
      (bottEndOfSheaf cs basis l hl s.projector) _) _=_
  rw [PerfectAdjoint.pairing,bottSplitRightWord_fixed]

 theorem bottCanonicalPerfectPairing_symmetric (m n : B.sheaf.forget.sections Set.univ) :
    (bottCanonicalPerfectPairing cs basis l hl B s).pairing m n=
      (bottCanonicalPerfectPairing cs basis l hl B s).pairing n m := by
  exact (bottCanonicalPerfectPairing_apply cs basis l hl B s m n).trans
    ((bottSamelson_symmetric cs l _ _).trans
      (bottCanonicalPerfectPairing_apply cs basis l hl B s n m).symm)

end
end KLInvariance.TitsSpace

end


section

/-! Unconditional symmetric, integral, support-orthogonal graded perfection
for the actual minimal-boundary sheaves; symmetry is inherited from the
proved canonical-adjoint recognition, not an arbitrary choice of a dual. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem symmetricBoundarySheaf_symmetricPairing_word (l : List I) (hl : cs.IsReduced l)
    (B : BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 (cs.wordProd l)) (symmetricLabel cs 1 (cs.wordProd l))
      ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩) :
    Nonempty (GradedSheaf.SymmetricPerfectPairing B.sheaf (cs.length (cs.wordProd l) : ℤ)) := by
  obtain ⟨s⟩ := bottBoundarySheaf_splitIn cs basis l hl B
  have hd : cs.length (cs.wordProd l)=l.length := hl
  rw [hd]
  exact ⟨{ toPerfectPairing := bottCanonicalPerfectPairing cs basis l hl B s
           symmetric := bottCanonicalPerfectPairing_symmetric cs basis l hl B s }⟩

 theorem symmetricBoundarySheaf_symmetricPairing (b : W) :
    Nonempty (GradedSheaf.SymmetricPerfectPairing
      (symmetricBoundarySheaf cs basis b).sheaf (cs.length b : ℤ)) := by
  obtain ⟨l,hl,he⟩ := cs.exists_isReduced b
  subst b
  exact symmetricBoundarySheaf_symmetricPairing_word cs basis l hl _

end
end KLInvariance.TitsSpace

namespace KLInvariance.BruhatGraph
open Module _root_.OAI.KLInvariance.Graded MomentGraph TitsSpace
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem boundarySheaf_symmetricPairing :
    Nonempty (GradedSheaf.SymmetricPerfectPairing
      (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf (cs.length b : ℤ)) := by
  classical
  let := interval_finite cs 1 b
  let := Fintype.ofFinite (Interval cs 1 b)
  let := Fintype.ofFinite (Edge cs 1 b)
  let S := symmetricBoundarySheaf cs basis b
  let T := boundarySheaf cs 1 b basis (one_bruhat cs b)
  let e := SymmetricAlgebra.equivMvPolynomial basis
  have he : ∀ n a, a∈symmetricGrading basis n ↔ e a∈polynomialGrading ℝ σ n :=
    mem_symmetricGrading basis
  obtain ⟨p⟩ := symmetricBoundarySheaf_symmetricPairing cs basis b
  obtain ⟨j⟩ := BoundarySheaf.iso_coefficientChange e he S T
    (polynomialGrading_zero ℝ σ) (fun x => x.property.2)
  exact ⟨(p.coefficientChange e he).pullback j⟩

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PositiveTransfer
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive transfer inequalities, strict Hilbert-series detection including higher-codimension support, and reverse-filtration projective-to-free arguments.
-/


section

/-! The genuine BMP local intersection map. All freeness, kernel-minimality and
inverse grading assertions here are now unconditional consequences of the
constructed integral duality. The nonvanishing/Hodge input is deliberately
NOT asserted; the last theorem records precisely how it would force the
strict KL halfdegree bound on ACTUAL homogeneous stalk generators. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

 def actualSymmetricPairing : GradedSheaf.SymmetricPerfectPairing
    (ActualBoundary cs b basis).sheaf (cs.length b : ℤ) :=
  (boundarySheaf_symmetricPairing cs b basis).some

 def actualSectionDuality : SectionDuality cs 1 b basis (one_bruhat cs b)
    (ActualBoundary cs b basis) := by
  let p := actualSymmetricPairing cs b basis
  let B := ActualBoundary cs b basis
  refine ⟨p.pairing,?_⟩
  intro x m n
  exact p.toPerfectPairing.cut_balanced
    (Sheaf.labelProduct (polynomialLabel cs 1 b basis))
    (Sheaf.labelProduct_ne_zero _ (polynomialLabel_ne_zero cs 1 b basis))
    (B.sheaf.forget.scaled_single_section
      (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs 1 b basis)
        (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x m n

end
end KLInvariance.BruhatGraph

end


end OAI
end


