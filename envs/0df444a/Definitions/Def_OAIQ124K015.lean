-- Prove2me | Definitions.Def_OAIQ124K015
-- name    : OAIQ124K015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:55:31.715988+00:00
-- url     : https://prove2.me/theorems/d3fa56c6-8090-4948-a69c-a75ec8393ad5
-- title:
--   Definitions bundle OAIQ124K015 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 14 definitions and 11 theorems. The definitions and types are `OAI.KLInvariance.BruhatGraph.ambientLater`, `OAI.KLInvariance.BruhatGraph.boundaryModels`, `OAI.KLInvariance.BruhatGraph.edgeFactorMap`, `OAI.KLInvariance.BruhatGraph.lowerIntervalEquiv`, `OAI.KLInvariance.BruhatGraph.lowerKernelEquiv`, `OAI.KLInvariance.MomentGraph.GradedSheaf.pullbackKernelEquiv`, `OAI.KLInvariance.MomentGraph.Sheaf.HasFlowDown`, `OAI.KLInvariance.TitsSpace.PlaneBasis.cosetModels`, `OAI.KLInvariance.TitsSpace.PlaneBasis.localModels`, `OAI.KLInvariance.TitsSpace.PlaneBasis.localizedModels`, `OAI.KLInvariance.TitsSpace.PlaneBasis.scheduledLower`, `OAI.KLInvariance.TitsSpace.PlaneBasis.scheduledOutgoing`, `OAI.KLInvariance.TitsSpace.PlaneBasis.scheduledUpper`, `OAI.KLInvariance.TitsSpace.bottPolynomialStalkData`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BottSamelson`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BottSamelson.lean), [`KazhdanLusztig_CharacterReciprocity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean), [`KazhdanLusztig_DihedralIntervals`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/DihedralIntervals.lean), [`KazhdanLusztig_EdgeLocalization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/EdgeLocalization.lean), [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean), [`KazhdanLusztig_MinimalExtensions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/MinimalExtensions.lean), [`KazhdanLusztig_PlaneLocalization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/PlaneLocalization.lean), [`KazhdanLusztig_SheafMorphisms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/SheafMorphisms.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K008`, `OAIQ124K009`, `OAIQ124K010` and `OAIQ124K011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ124K018`; the statement `OAI.KLInvariance.BruhatGraph.boundary_edge_image_le`; the proofs of `OAI.KLInvariance.BruhatGraph.actual_freeSuffixes_of_rTilde_eq`, `OAI.KLInvariance.BruhatGraph.boundary_edge_image_le` and `OAI.KLInvariance.combinatorial_invariance`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K008
import Definitions.Def_OAIQ124K009
import Definitions.Def_OAIQ124K010
import Definitions.Def_OAIQ124K011

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_MinimalExtensions
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.pi_free _root_.OAI.KLInvariance.Graded.ModuleData.prod_free _root_.OAI.KLInvariance.Graded.ModuleData.shift_free _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal-boundary extension sheaves, graded splittings and sheaf decomposition.
-/


section

/-! Finite sums of honest shifted normalized boundary models. A model family
is data for the decomposition lemma, not an assumption of the KL main. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}

namespace ModelSum
variable {hneg} {α : E → A} (O : BoundaryModels hneg (G := G) α)
  {U : Set V} {B : GradedSheaf (𝓐 := 𝓐) G}

lemma free (h : ModelSum O.sheaf U B) (x : V) : Module.Free A (B.vertex x) := by
  induction h with
  | zero => exact inferInstanceAs (Module.Free A PUnit.{max ua um+1})
  | @add C _ c _ n d ih =>
    let _ : Module.Free A (C.vertex x) := ih
    let _ := O.free c x
    change Module.Free A (C.vertex x × (ULift.{um} (Fin n) → (O.sheaf c).vertex x))
    infer_instance

end ModelSum
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue uw uf um
variable {R : Type ur} [CommRing R]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  {W : Type uw} [PartialOrder W] {F : Type uf} {H : OrderedGraph W F}
  (B : Sheaf.{ur,uw,uf,um} (R := R) H) (f : GraphMap G H)
noncomputable section

 theorem pullback_kernel (x : V) (T : Set F)
    (live : Set F) (hdead : ∀ e, e ∉ live → Subsingleton (B.edge e))
    (hlift : ∀ e ∈ live, f.vertex x = H.source e →
      ∃ a, f.edge a=e ∧ G.source a=x) :
    (B.pullback f).upwardKernel x {e | f.edge e.val ∈ T} =
      B.upwardKernel (f.vertex x) {e | e.val ∈ T} := by
  classical
  ext v
  change B.vertex (f.vertex x) at v
  let s : B.Assignment := Function.update (fun _ => 0) (f.vertex x) v
  have hs : s (f.vertex x)=v := Function.update_self (β := fun y => B.vertex y) (f.vertex x) v (fun _ => 0)
  have hxs : B.pullAssignment f s x = v := hs
  constructor
  · intro hv e he
    rw [← hs,B.stalkMap_assignment s]
    by_cases hl : e.val ∈ live
    · obtain ⟨a,ha,hax⟩ := hlift e.val hl e.property.symm
      have hh := hv ⟨a,hax⟩ (show f.edge a ∈ T from ha.symm ▸ he)
      rw [← hxs,(B.pullback f).stalkMap_assignment (B.pullAssignment f s)] at hh
      rw [B.pull_lower f] at hh
      exact (congrArg (fun q : F => B.lower q (s (H.source q)) = 0) ha).mp hh
    · exact @Subsingleton.elim _ (hdead e.val hl) _ _
  · intro hv e he
    have hh := hv ⟨f.edge e.val,(f.source e.val).symm.trans (congrArg f.vertex e.property)⟩ he
    rw [← hs,B.stalkMap_assignment s] at hh
    rw [← hxs,(B.pullback f).stalkMap_assignment (B.pullAssignment f s),B.pull_lower f]
    exact hh

end
end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SheafMorphisms
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroEdge_subsingleton _root_.OAI.KLInvariance.MomentGraph.Sheaf.zeroVertex_subsingleton _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottCoordinatePiece_graded _root_.OAI.KLInvariance.TitsSpace.bottPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottPiece_graded _root_.OAI.KLInvariance.TitsSpace.bottRealModule _root_.OAI.KLInvariance.TitsSpace.bottRealTower _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_decomposition _root_.OAI.KLInvariance.TitsSpace.bottStalkPiece_graded _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime _root_.OAI.KLInvariance.TitsSpace.simpleFixed_finite _root_.OAI.KLInvariance.TitsSpace.simpleFixed_free _root_.OAI.KLInvariance.TitsSpace.symmetricGrading_decomposition _root_.OAI.KLInvariance.TitsSpace.symmetricGrading_graded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded sheaf morphisms, exact section constructions and character sums.
-/

section

namespace KLInvariance.Graded
open Polynomial
universe uk us um ui

attribute [instance] NonnegativeBasis.finite

end KLInvariance.Graded

end


section

/-! Every lower-supported model is an actual Bruhat BMP sheaf on [1,c],
pulled back by the genuine lower-interval graph isomorphism and extended by
zero. Thus its stalk character is not an abstract model selected for convenience. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 local instance instDecidable_solutions_rc66112_1 (p : Prop) : Decidable p := Classical.propDecidable p
def boundaryModels : GradedSheaf.BoundaryModels (polynomialGrading_negative ℝ σ)
    (G := graph cs 1 b) (polynomialLabel cs 1 b basis) where
  sheaf c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend
  free c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_free
    (lowerIntervalBoundary cs b basis c).free
  quotient c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_quotient _
    (lowerIntervalBoundary cs b basis c).quotient
  generated c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_generated
    (lowerIntervalBoundary cs b basis c).generated
  flabby c := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_flabby
    (lowerIntervalBoundary cs b basis c).flabby.flabby
  support c x hx := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_support x hx
  top c := ((lowerIntervalBoundary cs b basis c).sheaf.lowerExtendVertex ⟨c,Set.mem_Iic.mpr le_rfl⟩).trans
    (ModuleData.equivOfEq (lowerIntervalBoundary cs b basis c).top)
  top_graded c n v hv := ModuleData.equivOfEq_graded (lowerIntervalBoundary cs b basis c).top n _
    ((lowerIntervalBoundary cs b basis c).sheaf.lowerExtendVertex_graded ⟨c,Set.mem_Iic.mpr le_rfl⟩ n v hv)
  minimal c x hx := (lowerIntervalBoundary cs b basis c).sheaf.lowerExtend_minimal x
    (fun hxc => (lowerIntervalBoundary cs b basis c).minimal ⟨x,hxc⟩
      (fun hh => hx (congrArg Subtype.val hh)))

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelPiFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelProdFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelShiftFree _root_.OAI.KLInvariance.MomentGraph.GradedSheaf.kernelZeroFree _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! The genuine nonnegative polynomial generator character of word stalks,
with its convergent Hilbert-series interpretation. No KL identification is
asserted or included in the definition. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def bottPolynomialStalkData (l : List I) (x : W) :
    ModuleData.{0,u,u} (polynomialGrading ℝ σ) :=
  ModuleData.change (SymmetricAlgebra.equivMvPolynomial basis) (mem_symmetricGrading basis)
    (bottStalkData cs basis l x)

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

namespace KLInvariance.Graded
open Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
noncomputable section

 theorem adjoint_homogeneous
    (p : M ≃ₗ[A] Dual A M) (l : ℤ)
    (hp : ∀ i j (m n : M), m ∈ 𝓜 i → n ∈ 𝓜 j → p m n ∈ 𝓐 (i+j-l))
    (f : End A M) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓜 n)
    (n : ℤ) (m : M) (hm : m ∈ 𝓜 n) : PerfectAdjoint.adjoint p f m ∈ 𝓜 n := by
  have h := perfect_inverse_of_homogeneous_functional 𝓐 𝓜 p l hp (n-l)
    (f.dualMap (p m)) (by
      intro j v hv
      have hv' := hp n j m (f v) hm (hf j v hv)
      have he : n+j-l=j+(n-l) := by omega
      change p m (f v) ∈ 𝓐 (j+(n-l))
      rw [← he]
      exact hv')
  simpa only [sub_add_cancel,PerfectAdjoint.adjoint,LinearMap.comp_apply,LinearEquiv.coe_coe] using h

end
end KLInvariance.Graded

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

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}
noncomputable section
attribute [local instance] Classical.propDecidable
variable {K : Set V} {hK : IsLowerSet K}

omit [IsNoetherianRing A] in
 theorem fullKernel_pullback (B : GradedSheaf (𝓐 := 𝓐) H) (f : GraphMap G H)
    (hlift : ∀ e x, f.vertex x=H.source e → ∃ a, f.edge a=e ∧ G.source a=x) (x : V) :
    (B.pullback f).upwardSubmodule x Set.univ=B.upwardSubmodule (f.vertex x) Set.univ := by
  exact B.forget.pullback_kernel f x Set.univ Set.univ
    (fun e he => (he (Set.mem_univ e)).elim) (fun e _ he => hlift e x he)

 def pullbackKernelEquiv (B : GradedSheaf (𝓐 := 𝓐) H) (f : GraphMap G H)
    (hlift : ∀ e x, f.vertex x=H.source e → ∃ a, f.edge a=e ∧ G.source a=x) (x : V) :
    kernelData (B.pullback f) x ≃ₗ[A] kernelData B (f.vertex x) where
  toFun m := ⟨m.val,fullKernel_pullback B f hlift x ▸ m.property⟩
  invFun m := ⟨m.val,(fullKernel_pullback B f hlift x).symm ▸ m.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end KLInvariance.MomentGraph.GradedSheaf

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
def lowerKernelEquiv (c x : Interval cs 1 b) (hx : x ≤ c) :
    GradedSheaf.kernelData ((boundaryModels cs b basis).sheaf c) x ≃ₗ[Coefficient (σ := σ)]
      GradedSheaf.kernelData (boundaryFreeSheaf cs c.val basis).sheaf ⟨x.val,x.property.1,hx⟩ :=
  ((lowerIntervalBoundary cs b basis c).sheaf.lowerExtendKernelEquiv ⟨x,hx⟩).trans
    ((boundaryFreeSheaf cs c.val basis).sheaf.pullbackKernelEquiv
      (lowerIntervalMap cs b c) (lowerIntervalMap_outgoing cs b c) ⟨x,hx⟩)

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

 attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_4
attribute [local instance] OAI.KLInvariance.BruhatGraph.lowerConvInterval
def lowerIntervalEquiv (c : Interval cs 1 b) : Set.Iic c ≃ Interval cs 1 c.val where
  toFun := (lowerIntervalMap cs b c).vertex
  invFun z := ⟨⟨z.val,z.property.1,bruhat_trans cs z.property.2 c.property.2⟩,z.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DihedralIntervals
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetFinite _root_.OAI.KLInvariance.TitsSpace.PlaneBasis.cosetOrder _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Signed dihedral coordinates, actual dihedral intervals, exact later-edge counts and root-plane calculations.
-/


section

/-! An elementary flabbiness criterion for the exact rank-one model. Flow-down
sections with the genuine product of outgoing labels suffice. The pairwise
relative-primality condition will be instantiated by actual root labels. -/
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] [DecompositionMonoid R]
  {V : Type uv} [PartialOrder V] {E : Type ue}
  (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section
variable [Fintype E] [DecidableEq V]

def HasFlowDown : Prop :=
  ∀ x, x ≤ c → ∃ f : (structureSheaf G α c).Assignment,
    (structureSheaf G α c).IsGlobal f ∧
    (∀ h : PLift (x ≤ c), f x h = modelProduct G α c x) ∧
    (∀ y, ¬ y ≤ x → f y = 0)

include G α c in
 theorem flowDown_flabby [Finite V]
    (hrel : ∀ x, (modelOutgoing G c x : Set E).Pairwise (Function.onFun IsRelPrime α))
    (hflow : HasFlowDown G α c) : (structureSheaf G α c).Flabby := by
  classical
  let B := structureSheaf G α c
  let : Fintype V := Fintype.ofFinite V
  suffices hh : ∀ s : Finset V, IsUpperSet (s : Set V) →
      ∀ f : B.Assignment, B.CompatibleOn (s : Set V) f →
        ∃ g : B.Assignment, B.IsGlobal g ∧ ∀ x ∈ s, g x = f x by
    intro Ω hΩ f hf
    have hset : (↑(Finset.univ.filter (· ∈ Ω)) : Set V) = Ω := by ext x; simp
    obtain ⟨g,hg,hgf⟩ := hh (Finset.univ.filter (· ∈ Ω)) (by rwa [hset]) f (by rwa [hset])
    exact ⟨g,hg,fun x hx => hgf x (by simpa using hx)⟩
  intro s
  refine Finset.strongInductionOn s ?_
  intro s ih hs f hf
  by_cases hempty : s = ∅
  · subst s
    refine ⟨0,?_,by simp⟩
    exact (B.sections Set.univ).zero_mem
  obtain ⟨a,ha,hmin⟩ := s.exists_minimal (Finset.nonempty_iff_ne_empty.mpr hempty)
  have hu : IsUpperSet (↑(s.erase a) : Set V) := by
    intro x y hxy hx
    have hx' := Finset.mem_erase.mp hx
    refine Finset.mem_erase.mpr ⟨?_,hs hxy hx'.2⟩
    intro hya
    subst y
    exact hx'.1 (le_antisymm hxy (hmin hx'.2 hxy))
  obtain ⟨g,hg,hgf⟩ := ih (s.erase a) (Finset.erase_ssubset ha) hu f
    (fun e he ht => hf e (Finset.mem_of_mem_erase he) (Finset.mem_of_mem_erase ht))
  by_cases hac : a ≤ c
  · obtain ⟨t,ht,hta,htzero⟩ := hflow a hac
    have hdiv : modelProduct G α c a ∣ f a ⟨hac⟩ - g a ⟨hac⟩ := by
      apply Finset.prod_dvd_of_isRelPrime (hrel a)
      intro e he
      obtain ⟨hea,hec⟩ := (mem_modelOutgoing G c a e).mp he
      have hsource : G.source e ∈ s := hea ▸ ha
      have htarget : G.target e ∈ s.erase a := Finset.mem_erase.mpr
        ⟨by simpa [← hea] using (G.increasing e).ne',hs (G.increasing e).le hsource⟩
      have hf' := (structureCompatible_iff G α c (s : Set V) f).mp hf e hsource
        (Finset.mem_of_mem_erase htarget) ⟨hec⟩
      have hg' := (structureCompatible_iff G α c Set.univ g).mp hg e
        (Set.mem_univ _) (Set.mem_univ _) ⟨hec⟩
      rw [hgf _ htarget] at hg'
      have hd := dvd_sub hf' hg'
      rw [sub_sub_sub_cancel_right] at hd
      subst a
      exact hd
    obtain ⟨r,hr⟩ := hdiv
    refine ⟨g+r • t,(B.sections Set.univ).add_mem hg
      ((B.sections Set.univ).smul_mem r ht),?_⟩
    intro x hx
    by_cases hxa : x = a
    · subst x
      funext h
      change g a h + r * t a h = f a h
      rw [hta h]
      change f a h - g a h = modelProduct G α c a * r at hr
      linear_combination -hr
    · have hnot : ¬ x ≤ a := fun h => hxa (le_antisymm h (hmin hx h))
      have ht0 := htzero x hnot
      change g x + r • t x = f x
      rw [ht0,smul_zero,add_zero]
      exact hgf x (Finset.mem_erase.mpr ⟨hxa,hx⟩)
  · refine ⟨g,hg,?_⟩
    intro x hx
    by_cases hxa : x = a
    · subst x
      let := structureSheaf_support G α c a hac
      exact Subsingleton.elim _ _
    · exact hgf x (Finset.mem_erase.mpr ⟨hxa,hx⟩)

end
end KLInvariance.MomentGraph.Sheaf

end


section

/-! Flabbiness of the exact rank-one model with ambient labels, proved by
interpolation rather than an assumed character theorem. -/
namespace KLInvariance.Dihedral
open Module TitsSpace BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v w us
variable {H : Type w} [Group H] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N H)
  {I : Type u} [Fintype I] {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (φ : H →* W)
  (hφ : ∀ t, ds.IsReflection t → cs.IsReflection (φ t))
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 variable (b : H) [Fintype (Edge ds 1 b)] [DecidableEq (Interval ds 1 b)]

 theorem interpolation_product (x c : Interval ds 1 b) :
    (∏ y : oppositeExternal ds x.val c.val,
      linearPolynomial basis (embed M (interpolationRoot ds cs φ hφ x.val c.val y).val)) =
      modelProduct (graph ds 1 b) (inducedLabel ds cs φ hφ basis b) c x := by
  classical
  calc
    _ = ∏ e : ↥(modelOutgoing (graph ds 1 b) c x), inducedLabel ds cs φ hφ basis b e.val :=
      (outgoingEquiv ds b x c).prod_comp _
    _ = _ := Finset.prod_coe_sort _ _

 theorem hasFlowDown (hφinj : Function.Injective φ) (c : Interval ds 1 b) :
    HasFlowDown (graph ds 1 b) (inducedLabel ds cs φ hφ basis b) c := by
  classical
  intro x hxc
  obtain ⟨F,hF,hFx,hFzero⟩ := interpolation_exists ds cs φ hφ basis hφinj hxc
  let f : (structureSheaf (graph ds 1 b) (inducedLabel ds cs φ hφ basis b) c).Assignment :=
    fun v _ => F v.val
  refine ⟨f,?_,?_,?_⟩
  · apply (structureCompatible_iff _ _ _ _ _).mpr
    intro e _ _ h
    have hdiv := hF (label ds 1 b e) (label_isReflection ds 1 b e)
      (inducedRoot ds cs φ hφ b e).val (positiveRoot_represents M cs
        ⟨φ (label ds 1 b e),hφ _ (label_isReflection ds 1 b e)⟩)
      (source ds 1 b e).val
    rw [label_mul_source] at hdiv
    exact hdiv
  · intro _
    exact hFx.trans (interpolation_product ds cs φ hφ basis b x c)
  · intro y hy
    funext h
    exact hFzero y.val h.down hy

 theorem model_flabby (hφinj : Function.Injective φ) (c : Interval ds 1 b) :
    (structureSheaf (graph ds 1 b) (inducedLabel ds cs φ hφ basis b) c).Flabby := by
  classical
  let : Finite (Interval ds 1 b) := interval_finite ds 1 b
  apply flowDown_flabby
  · intro x e he f hf hne
    apply ((inducedLabel_prime ds cs φ hφ basis b e).irreducible.isRelPrime_iff_not_dvd).mpr
    intro hdiv
    apply hne
    apply eq_of_label_source_eq ds 1 b (label_eq_of_induced_dvd ds cs φ hφ basis b hφinj hdiv)
    exact ((mem_modelOutgoing _ _ _ _).mp he).1.trans ((mem_modelOutgoing _ _ _ _).mp hf).1.symm
  · exact hasFlowDown ds cs φ hφ basis b hφinj c

end
end KLInvariance.Dihedral

end


section

/-! Instantiation on the actual maximal subgroup of the ambient root plane.
The exact canonical roots, including degenerate/infinite planes, are used. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem model_flabby (b : planeSubgroup M cs P) [Fintype (Edge B.system 1 b)]
    [DecidableEq (Interval B.system 1 b)] (c : Interval B.system 1 b) :
    (structureSheaf (graph B.system 1 b) (B.modelLabel basis b) c).Flabby :=
  Dihedral.model_flabby B.system cs (planeSubgroup M cs P).subtype
    (fun t => (B.reflection_iff t).mp) basis b Subtype.val_injective c

end
end KLInvariance.TitsSpace.PlaneBasis

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PlaneLocalization
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Symmetric plane ideals, sheaf localization and scaled local products along genuine edges.
-/


section

/-! The rank-one plane models over the actual flat local coefficient ring.
The local-ring label condition is later supplied by the plane prime. -/

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us ur
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (R : Type ur) [CommRing R] [Algebra (MvPolynomial σ ℝ) R]
  [Module.Flat (MvPolynomial σ ℝ) R] [IsLocalRing R]
noncomputable section

 def localModels (b : planeSubgroup M cs P)
    (hα : ∀ e, algebraMap (MvPolynomial σ ℝ) R (B.modelLabel basis b e) ∈
      IsLocalRing.maximalIdeal R) :
    LocalModels (G := graph B.system 1 b)
      (fun e => algebraMap (MvPolynomial σ ℝ) R (B.modelLabel basis b e)) := by
  classical
  let := interval_finite B.system 1 b
  let := Fintype.ofFinite (Edge B.system 1 b)
  exact structureLocalModels _ _ hα (exists_outgoing_below B.system 1 b)
    (fun c => structureSheaf_flat_flabby R _ _ c (B.model_flabby basis b c))

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! The actual plane prime and its localization in the coefficient polynomial
ring of the chosen nondegenerate ambient realization. -/

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 def localizedModels (b : planeSubgroup M cs P) :
    LocalModels (G := graph B.system 1 b)
      (fun e => algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (B.modelLabel basis b e)) :=
  B.localModels basis (PlaneRing basis P) b (B.modelLabel_mem_maximal basis b)

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Rank-one models on the actual finite relative lower ideal in an ambient
plane coset. The ideal need not have a greatest element. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (a₀ b : W) (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 include hmin in
 theorem coset_model_flabby (c : B.CosetVertex a₀ b) :
    (structureSheaf (B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) c).Flabby := by
  classical
  let := Fintype.ofFinite (B.CosetVertex a₀ b)
  obtain ⟨d,hd⟩ := Dihedral.exists_common_upper B.system
    (Finset.univ.image (fun x : B.CosetVertex a₀ b => x.val))
  have hbnd (x : B.CosetVertex a₀ b) : BruhatLE B.system x.val d :=
    hd _ (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
  let f := B.cosetIntoGraph a₀ b d hbnd
  let α : Edge B.system 1 d → PlaneRing basis P := fun e =>
    algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P) (B.modelLabel basis d e)
  let C := structureSheaf (graph B.system 1 d) α (f.vertex c)
  have hfl : C.Flabby := (B.localizedModels basis d).flabby (f.vertex c)
  let := interval_finite B.system 1 d
  have hpull : (C.pullback f).Flabby := by
    apply C.pullback_flabby_live f hfl (B.cosetInto_injective a₀ b d hbnd)
      {e | target B.system 1 d e ≤ f.vertex c}
    · intro e he
      exact structureSheaf_edge_subsingleton _ α (f.vertex c) e he
    · intro e he x hx
      have hlow : BruhatLE B.system (target B.system 1 d e).val c.val := he
      let y : B.CosetVertex a₀ b := ⟨(target B.system 1 d e).val,
        (target B.system 1 d e).property.1,B.coset_lower a₀ b hmin hlow⟩
      have hye : f.vertex y=target B.system 1 d e := rfl
      have hs : BruhatStep B.system x.val y.val := by
        change BruhatStep B.system (f.vertex x).val (f.vertex y).val
        rw [hx,hye]
        exact e.property
      refine ⟨⟨(x,y),hs⟩,?_,rfl⟩
      exact Subtype.ext (Prod.ext hx hye)
  have hh := (structurePullbackIso f α c (fun _ _ => Iff.rfl)).flabby hpull
  have hα : (fun e => α (f.edge e)) = B.cosetLabel basis a₀ b hmin := by
    funext e
    exact congrArg (algebraMap (MvPolynomial σ ℝ) (PlaneRing basis P))
      (B.coset_modelLabel_eq basis a₀ b hmin d hbnd e)
  rwa [hα] at hh

 def cosetModels : LocalModels (G := B.cosetGraph a₀ b) (B.cosetLabel basis a₀ b hmin) :=
  structureLocalModels _ _
    (fun e => (linear_mem_maximal_iff basis P _).mpr (by
      apply (Represents.planeSubgroup_mem_iff M cs
        (positiveRoot_represents M cs ⟨label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e),
          label_isReflection cs 1 b _⟩)).mp
      change label cs 1 b (B.cosetEdgeAmbient a₀ b hmin e) ∈ planeSubgroup M cs P
      rw [B.coset_label_eq a₀ b hmin e]
      exact (planeSubgroup M cs P).mul_mem e.val.2.val.property
        ((planeSubgroup M cs P).inv_mem e.val.1.val.property)))
    (B.coset_outgoing_below a₀ b hmin) (B.coset_model_flabby basis a₀ b hmin)

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
noncomputable section

 def scheduledOutgoing (φ : Interval cs u b ≃o Interval cs' u' b')
    (α : PositiveRoot M' cs') (x : B.CosetVertex a₀ b)
    (hx : BruhatLE cs u ((x.val:W)*a₀)) : Set (Outgoing (G := B.cosetGraph a₀ b) x) :=
  {f | ambientAfterIndicator (φ (B.cosetUpperVertex x hx)).val α
    (φ (B.cosetUpperVertex f.val.val.2 (B.outgoing_upper hmin x hx f))).val = 1}

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
open Module BruhatGraph MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {a₀ u b : W} {u' b' : W'}
  (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def scheduledLower (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    Set (Outgoing (G := B.cosetGraph a₀ b) e.val.1) :=
  B.scheduledOutgoing hmin φ (B.mappedCosetRoot hmin φ e hx) e.val.1 hx

 def scheduledUpper (e : B.CosetEdge a₀ b) (hx : BruhatLE cs u ((e.val.1.val:W)*a₀)) :
    Set (Outgoing (G := B.cosetGraph a₀ b) e.val.2) :=
  B.scheduledOutgoing hmin φ (B.mappedCosetRoot hmin φ e hx) e.val.2
    (B.cosetEdge_target_upper hmin e hx)

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

namespace KLInvariance.BruhatGraph
open TitsSpace MomentGraph MomentGraph.Sheaf
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def ambientLater (α : PositiveRoot M' cs') : Set (Edge cs 1 b) :=
  {e | ∃ hx : BruhatLE cs u (source cs 1 b e).val,
    ambientAfterIndicator (φ ⟨(source cs 1 b e).val,hx,(source cs 1 b e).property.2⟩).val α
      (φ ⟨(target cs 1 b e).val,bruhat_trans cs hx (.single e.property),
        (target cs 1 b e).property.2⟩).val = 1}

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

variable (u b : W) (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)

/-- Multiplication by the genuine plane product on the actual edge module. -/
 def edgeFactorMap (e : Edge cs u b) : B.sheaf.edge e →ₗ[Coefficient (σ := σ)] B.sheaf.edge e :=
  LinearMap.lsmul (Coefficient (σ := σ)) (B.sheaf.edge e)
    (edgeFactorLift cs basis (source cs u b e).val (root cs u b e))

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_EdgeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bruhat sheaf localization, graded transport, local edge-image bounds and support.
-/


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C D : GradedSheaf (𝓐 := 𝓐) G}
  (s : SplitIn B D) (t : SplitIn C D)

 theorem SplitIn.comparison_bijective (x : V)
    (hs : ∀ v, (s.projector.vertex x).map v=v)
    (ht : ∀ v, (t.projector.vertex x).map v=v) :
    Function.Bijective ((t.projection.comp s.inclusion).vertex x).map := by
  let f := ((t.projection.comp s.inclusion).vertex x).map
  let g := ((s.projection.comp t.inclusion).vertex x).map
  have hgf (v : B.vertex x) : g (f v)=v := by
    exact (congrArg (s.projection.vertex x).map (ht ((s.inclusion.vertex x).map v))).trans
      (s.vertex_split x v)
  have hfg (v : C.vertex x) : f (g v)=v := by
    exact (congrArg (t.projection.vertex x).map (hs ((t.inclusion.vertex x).map v))).trans
      (t.vertex_split x v)
  exact ⟨Function.LeftInverse.injective hgf,Function.RightInverse.surjective hfg⟩

end KLInvariance.MomentGraph.GradedSheaf

end


end OAI
end


