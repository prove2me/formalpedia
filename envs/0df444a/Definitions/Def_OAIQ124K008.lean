-- Prove2me | Definitions.Def_OAIQ124K008
-- name    : OAIQ124K008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:50:20.210295+00:00
-- url     : https://prove2.me/theorems/18fbc603-6e8d-4d80-b08b-5f20acf31a3d
-- title:
--   Definitions bundle OAIQ124K008 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 123 declarations of OpenAI's Lean: 49 definitions, 4 inductive types or structures, 11 instances and 59 theorems. The definitions and types are `OAI.KLInvariance.Graded.ModuleData.quotientHom`, `OAI.KLInvariance.Graded.ModuleData.unchangeHom`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Endomorphism.complement`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.PrimitiveProjector`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.coefficientUnchange`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.comp`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.id`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.inverse`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.toEndomorphism`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Hom.zero`, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom`, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.boundary`, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.extend`, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.mapAssignment`, `OAI.KLInvariance.MomentGraph.GradedSheaf.OnHom.ofUniv`, `OAI.KLInvariance.MomentGraph.GradedSheaf.PerfectPairing.coefficientChange`, `OAI.KLInvariance.MomentGraph.GradedSheaf.PerfectPairing.pullback`, `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn`, `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.isoOfPrimitive`, `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.isoOfProjectorEqId`, `OAI.KLInvariance.MomentGraph.GradedSheaf.SplitIn.projector`, `OAI.KLInvariance.MomentGraph.GradedSheaf.SymmetricPerfectPairing`, `OAI.KLInvariance.MomentGraph.GradedSheaf.SymmetricPerfectPairing.coefficientChange`, `OAI.KLInvariance.MomentGraph.GradedSheaf.SymmetricPerfectPairing.pullback`, `OAI.KLInvariance.MomentGraph.GradedSheaf.castVertexHom`, `OAI.KLInvariance.MomentGraph.GradedSheaf.coefficientChange`, `OAI.KLInvariance.MomentGraph.GradedSheaf.coefficientChangeSections`, `OAI.KLInvariance.MomentGraph.Sheaf.AboveIso.symm`, `OAI.KLInvariance.MomentGraph.Sheaf.boundaryImage`, `OAI.KLInvariance.TitsSpace.BottIndex`, `OAI.KLInvariance.TitsSpace.ambientAfterIndicator`, `OAI.KLInvariance.TitsSpace.bottBasis`, `OAI.KLInvariance.TitsSpace.bottCoordinatePiece`, `OAI.KLInvariance.TitsSpace.bottDegree`, `OAI.KLInvariance.TitsSpace.bottEvaluation`, `OAI.KLInvariance.TitsSpace.bottEvaluationMatrix`, `OAI.KLInvariance.TitsSpace.bottFullIndex`, `OAI.KLInvariance.TitsSpace.bottPiece`, `OAI.KLInvariance.TitsSpace.bottStalk` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BalancedPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean), [`KazhdanLusztig_BottSamelson`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BottSamelson.lean), [`KazhdanLusztig_CharacterReciprocity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/CharacterReciprocity.lean), [`KazhdanLusztig_DihedralIntervals`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/DihedralIntervals.lean), [`KazhdanLusztig_EdgeLocalization`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/EdgeLocalization.lean), [`KazhdanLusztig_Frobenius`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Frobenius.lean), [`KazhdanLusztig_GradedSheaves`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/GradedSheaves.lean), [`KazhdanLusztig_SheafMorphisms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/SheafMorphisms.lean), [`KazhdanLusztig_Sheaves`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Sheaves.lean), [`KazhdanLusztig_Support`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/Support.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K004` and `OAIQ124K005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K012`, `OAIQ124K013`, `OAIQ124K014` and `OAIQ124K015`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K004
import Definitions.Def_OAIQ124K005

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Sheaves
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.instAddCommGroupCarrierObj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Ordered moment graphs, sheaves, flabbiness, sections and boundary images.
-/

section

namespace KLInvariance.MomentGraph.Sheaf

universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}
  {G : OrderedGraph V E} (B : Sheaf.{u,v,w,z} (R := R) G)

def boundaryImage (x : V) : Submodule R (B.Boundary x) :=
  LinearMap.range (B.boundaryMap x)

/-- The precise boundary-image identity in `loc:decomposition`.
Generation supplies one inclusion and flabbiness supplies the other. -/
theorem range_stalkMap_eq_boundaryImage
    (hf : B.Flabby) (hg : B.Generated) (x : V) :
    LinearMap.range (B.stalkMap x) = B.boundaryImage x := by
  apply le_antisymm
  · rintro v ⟨b, rfl⟩
    obtain ⟨f, hglob, hfx⟩ := hg x b
    refine ⟨⟨f, B.compatible_mono hglob (Set.subset_univ _)⟩, ?_⟩
    ext e
    change B.upper e.val (f (G.target e.val)) =
      B.lower e.val (e.property.symm ▸ b)
    have hc := hglob e.val (Set.mem_univ _) (Set.mem_univ _)
    rw [← hc]
    congr 1
    cases e with | mk e he => subst x; exact hfx
  · rintro v ⟨f, rfl⟩
    have hu : IsUpperSet (Set.Ioi x) := fun a b hab ha => lt_of_lt_of_le ha hab
    obtain ⟨g, hglob, hgf⟩ := hf (Set.Ioi x) hu f.val f.property
    refine ⟨g x, ?_⟩
    ext e
    change B.lower e.val (e.property.symm ▸ g x) =
      B.upper e.val (f.val (G.target e.val))
    have hc := hglob e.val (Set.mem_univ _) (Set.mem_univ _)
    have ht : G.target e.val ∈ Set.Ioi x := by
      change x < G.target e.val
      exact lt_of_eq_of_lt e.property.symm (G.increasing e.val)
    rw [← hgf _ ht, ← hc]
    congr 1
    cases e with | mk e he => subst x; rfl

end KLInvariance.MomentGraph.Sheaf


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_GradedSheaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded moment-graph sheaves, boundary sections, graded covers and morphisms.
-/


section


namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G) (x : V)

namespace AboveIso
variable {B C x} (j : AboveIso B C x)

def symm : AboveIso C B x where
  vertex y h := (j.vertex y h).symm
  edge e h := (j.edge e h).symm
  lower e h v := by
    apply (j.edge e (h.trans (G.increasing e))).injective
    rw [LinearEquiv.apply_symm_apply,j.lower e h,LinearEquiv.apply_symm_apply]
  upper e h v := by
    apply (j.edge e h).injective
    simp only [LinearEquiv.apply_symm_apply,j.upper]

lemma map_boundaryImage : (B.boundaryImage x).map j.boundary.toLinearMap = C.boundaryImage x := by
  apply le_antisymm
  · rintro v ⟨w,⟨f,rfl⟩,rfl⟩
    exact ⟨⟨j.mapAssignment f.val,j.compatible f.val f.property⟩,(j.boundaryMap f).symm⟩
  · rintro v ⟨f,rfl⟩
    refine ⟨B.boundaryMap x ⟨j.symm.mapAssignment f.val,j.symm.compatible f.val f.property⟩,
      ⟨_,rfl⟩,?_⟩
    funext e
    change j.edge e.val _ (B.upper e.val (j.symm.mapAssignment f.val (G.target e.val))) =
      C.upper e.val (f.val (G.target e.val))
    rw [j.symm.mapAssignment_at _ _ (lt_of_eq_of_lt e.property.symm (G.increasing e.val)),j.upper]
    exact congrArg (C.upper e.val) ((j.vertex _ _).apply_symm_apply _)

lemma map_stalk_image (hBf : B.Flabby) (hBg : B.Generated)
    (hCf : C.Flabby) (hCg : C.Generated) :
    (LinearMap.range (B.stalkMap x)).map j.boundary.toLinearMap =
      LinearMap.range (C.stalkMap x) := by
  rw [B.range_stalkMap_eq_boundaryImage hBf hBg,C.range_stalkMap_eq_boundaryImage hCf hCg]
  exact j.map_boundaryImage

end AboveIso
end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SheafMorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded sheaf morphisms, exact section constructions and character sums.
-/


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
noncomputable section

 def quotientHom {M N E F : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M E) (g : Hom N F) (hf : Function.Surjective f.map)
    (h : Hom M N) (hk : LinearMap.ker f.map ≤ LinearMap.ker (g.map.comp h.map)) : Hom E F where
  map := QuotientEdge.descend f.map g.map hf h.map hk
  graded := by
    intro n v hv
    obtain ⟨w,hw,rfl⟩ := f.homogeneous_preimage hf n v hv
    rw [QuotientEdge.descend_apply]
    exact g.graded n _ (h.graded n w hw)

 theorem quotientHom_apply {M N E F : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M E) (g : Hom N F) (hf : Function.Surjective f.map)
    (h : Hom M N) (hk : LinearMap.ker f.map ≤ LinearMap.ker (g.map.comp h.map))
    (v : M) : (quotientHom f g hf h hk).map (f.map v) = g.map (h.map v) :=
  QuotientEdge.descend_apply _ _ _ _ _ v

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}

structure Hom (B C : GradedSheaf (𝓐 := 𝓐) G) where
  vertex : ∀ x, ModuleData.Hom (B.vertex x) (C.vertex x)
  edge : ∀ e, ModuleData.Hom (B.edge e) (C.edge e)
  lower : ∀ e v, (edge e).map ((B.lower e).map v) =
    (C.lower e).map ((vertex (G.source e)).map v)
  upper : ∀ e v, (edge e).map ((B.upper e).map v) =
    (C.upper e).map ((vertex (G.target e)).map v)

structure OnHom (B C : GradedSheaf (𝓐 := 𝓐) G) (U : Set V) where
  vertex : ∀ x, x ∈ U → ModuleData.Hom (B.vertex x) (C.vertex x)
  edge : ∀ e, G.target e ∈ U → ModuleData.Hom (B.edge e) (C.edge e)
  lower : ∀ e (hs : G.source e ∈ U) (ht : G.target e ∈ U) v,
    (edge e ht).map ((B.lower e).map v) =
      (C.lower e).map ((vertex (G.source e) hs).map v)
  upper : ∀ e (ht : G.target e ∈ U) v,
    (edge e ht).map ((B.upper e).map v) =
      (C.upper e).map ((vertex (G.target e) ht).map v)

namespace Hom
variable {B C D : GradedSheaf (𝓐 := 𝓐) G}

def comp (g : Hom C D) (f : Hom B C) : Hom B D where
  vertex x := (g.vertex x).comp (f.vertex x)
  edge e := (g.edge e).comp (f.edge e)
  lower e v := by
    change (g.edge e).map ((f.edge e).map ((B.lower e).map v)) = _
    rw [f.lower,g.lower]; rfl
  upper e v := by
    change (g.edge e).map ((f.edge e).map ((B.upper e).map v)) = _
    rw [f.upper,g.upper]; rfl

end Hom

namespace OnHom
variable {B C : GradedSheaf (𝓐 := 𝓐) G} {U : Set V} (j : OnHom B C U)
noncomputable section

 def ofUniv (j : OnHom B C Set.univ) : Hom B C where
  vertex x := j.vertex x (Set.mem_univ x)
  edge e := j.edge e (Set.mem_univ _)
  lower e v := j.lower e (Set.mem_univ _) (Set.mem_univ _) v
  upper e v := j.upper e (Set.mem_univ _) v

 def mapAssignment (x : V) (hx : Set.Ioi x ⊆ U)
    (f : B.forget.Assignment) : C.forget.Assignment := by
  classical
  exact fun y => if h : x < y then (j.vertex y (hx h)).map (f y) else 0

 theorem mapAssignment_at (x : V) (hx : Set.Ioi x ⊆ U)
    (f : B.forget.Assignment) (y : V) (h : x < y) :
    j.mapAssignment x hx f y = (j.vertex y (hx h)).map (f y) := by
  classical
  unfold mapAssignment
  exact dite_eq_left h

 theorem compatible (x : V) (hx : Set.Ioi x ⊆ U)
    (f : B.forget.Assignment) (hf : B.forget.CompatibleOn (Set.Ioi x) f) :
    C.forget.CompatibleOn (Set.Ioi x) (j.mapAssignment x hx f) := by
  intro e hs ht
  change x < G.source e at hs
  change x < G.target e at ht
  rw [j.mapAssignment_at x hx f _ hs,j.mapAssignment_at x hx f _ ht]
  change (C.lower e).map ((j.vertex _ (hx hs)).map (f _)) =
    (C.upper e).map ((j.vertex _ (hx ht)).map (f _))
  exact (j.lower e (hx hs) (hx ht) _).symm.trans
    ((congrArg (j.edge e (hx ht)).map (hf e hs ht)).trans (j.upper e (hx ht) _))

variable [Fintype E]

 def boundary (x : V) (hx : Set.Ioi x ⊆ U) :
    ModuleData.Hom (B.boundary x) (C.boundary x) where
  map := LinearMap.pi fun e =>
    ((j.edge e.val (hx (lt_of_eq_of_lt e.property.symm (G.increasing e.val)))).map).comp
      (LinearMap.proj e)
  graded := by
    intro n v hv e he
    exact (j.edge e.val _).graded n _ (hv e he)

 theorem boundaryMap (x : V) (hx : Set.Ioi x ⊆ U)
    (f : B.forget.sections (Set.Ioi x)) :
    (j.boundary x hx).map (B.forget.boundaryMap x f) =
      C.forget.boundaryMap x ⟨j.mapAssignment x hx f.val,j.compatible x hx f.val f.property⟩ := by
  funext e
  change (j.edge e.val _).map ((B.upper e.val).map (f.val (G.target e.val))) =
    (C.upper e.val).map (j.mapAssignment x hx f.val (G.target e.val))
  rw [j.mapAssignment_at _ _ _ _ (lt_of_eq_of_lt e.property.symm (G.increasing e.val))]
  exact j.upper e.val _ _

 theorem map_stalk_image_le (x : V) (hx : Set.Ioi x ⊆ U)
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated) :
    (LinearMap.range (B.forget.stalkMap x)).map (j.boundary x hx).map ≤
      LinearMap.range (C.forget.stalkMap x) := by
  rw [B.forget.range_stalkMap_eq_boundaryImage hBf hBg,
    C.forget.range_stalkMap_eq_boundaryImage hCf hCg]
  rintro v ⟨w,⟨f,rfl⟩,rfl⟩
  exact ⟨⟨j.mapAssignment x hx f.val,j.compatible x hx f.val f.property⟩,
    (j.boundaryMap x hx f).symm⟩

variable [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)

include hneg hzero in
 theorem extend_stalk (x : V) (hx : Set.Ioi x ⊆ U)
    [Module.Free A (B.vertex x)]
    (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated) :
    ∃ f : ModuleData.Hom (B.vertex x) (C.vertex x), ∀ v,
      C.forget.stalkMap x (f.map v) = (j.boundary x hx).map (B.forget.stalkMap x v) := by
  let T := ModuleData.range (C.stalkHom x)
  let f : ModuleData.Hom (B.vertex x) T :=
    { map := LinearMap.codRestrict (LinearMap.range (C.forget.stalkMap x))
        ((j.boundary x hx).map.comp (B.forget.stalkMap x)) (by
          intro v
          exact j.map_stalk_image_le x hx hBf hBg hCf hCg ⟨_,⟨v,rfl⟩,rfl⟩)
      graded := fun n v hv => (j.boundary x hx).graded n _ ((B.stalkHom x).graded n v hv) }
  let π : ModuleData.Hom (C.vertex x) T :=
    { map := (C.forget.stalkMap x).rangeRestrict
      graded := fun n v hv => (C.stalkHom x).graded n v hv }
  have hπ : Function.Surjective π.map := by
    intro v
    obtain ⟨w,hw⟩ := v.property
    exact ⟨w,Subtype.ext hw⟩
  obtain ⟨l,hl⟩ := ModuleData.exists_hom_lift hneg hzero π hπ f
  refine ⟨l,fun v => ?_⟩
  exact congrArg (fun z : T => z.val) (LinearMap.congr_fun hl v)

end
end OnHom
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}

 def castVertexHom {x y : V} (h : x=y)
    (f : ModuleData.Hom (B.vertex x) (C.vertex x)) :
    ModuleData.Hom (B.vertex y) (C.vertex y) := h ▸ f

namespace OnHom
variable {U : Set V} (j : OnHom B C U)
noncomputable section

 def extend (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → A)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : ModuleData.Hom (B.vertex x) (C.vertex x))
    (hout : ∀ e (he : G.source e = x) v,
      (j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
        ((B.lower e).map v) =
      (C.lower e).map ((castVertexHom he.symm jv).map v)) :
    OnHom B C (insert x U) := by
  classical
  let vj : ∀ y, y ∈ insert x U → ModuleData.Hom (B.vertex y) (C.vertex y) := fun y hy =>
    if h : y=x then castVertexHom h.symm jv
    else j.vertex y ((Set.mem_insert_iff.mp hy).resolve_left h)
  have vj_old (y : V) (hy : y ∈ U) : vj y (Set.mem_insert_of_mem x hy) = j.vertex y hy := by
    simp only [vj,dite_eq_right (show y ≠ x from fun h => hx (h ▸ hy))]
  have vj_new : vj x (Set.mem_insert x U) = jv := by simp [vj,castVertexHom]
  let ej : ∀ e, G.target e ∈ insert x U → ModuleData.Hom (B.edge e) (C.edge e) := fun e he =>
    if h : G.target e=x then
      ModuleData.quotientHom (B.upper e) (C.upper e) (hBq e).1 (vj (G.target e) he)
        (QuotientEdge.kernel_scalar_le (B.upper e).map (C.upper e).map (α e)
          (hBq e).2 (hCq e).2 (vj (G.target e) he).map)
    else j.edge e ((Set.mem_insert_iff.mp he).resolve_left h)
  have ej_old (e : E) (he : G.target e ∈ U) :
      ej e (Set.mem_insert_of_mem x he) = j.edge e he := by
    simp only [ej,dite_eq_right (show G.target e ≠ x from fun h => hx (h ▸ he))]
  refine ⟨vj,ej,?_,?_⟩
  · intro e hs ht v
    have htU : G.target e ∈ U := by
      rcases Set.mem_insert_iff.mp hs with hs | hs
      · exact hmax (lt_of_eq_of_lt hs.symm (G.increasing e))
      · exact hU (G.increasing e).le hs
    rw [ej_old e htU]
    by_cases he : G.source e=x
    · subst x
      rw [vj_new]
      exact hout e rfl v
    · have hsU : G.source e ∈ U := (Set.mem_insert_iff.mp hs).resolve_left he
      rw [vj_old _ hsU]
      exact j.lower e hsU htU v
  · intro e ht v
    by_cases he : G.target e=x
    · simp only [ej,dite_eq_left he]
      exact ModuleData.quotientHom_apply _ _ _ _ _ v
    · have htU : G.target e ∈ U := (Set.mem_insert_iff.mp ht).resolve_left he
      rw [ej_old e htU,vj_old _ htU]
      exact j.upper e htU v

 theorem extend_vertex_old (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → A)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : ModuleData.Hom (B.vertex x) (C.vertex x))
    (hout : ∀ e (he : G.source e = x) v,
      (j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
        ((B.lower e).map v) =
      (C.lower e).map ((castVertexHom he.symm jv).map v))
    (y : V) (hy : y ∈ U) :
    (j.extend hU x hx hmax α hBq hCq jv hout).vertex y (Set.mem_insert_of_mem x hy) =
      j.vertex y hy := by
  classical
  simp only [extend,dite_eq_right (show y ≠ x from fun h => hx (h ▸ hy))]

 theorem extend_vertex_new (hU : IsUpperSet U) (x : V) (hx : x ∉ U)
    (hmax : Set.Ioi x ⊆ U) (α : E → A)
    (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
    (jv : ModuleData.Hom (B.vertex x) (C.vertex x))
    (hout : ∀ e (he : G.source e = x) v,
      (j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
        ((B.lower e).map v) =
      (C.lower e).map ((castVertexHom he.symm jv).map v)) :
    (j.extend hU x hx hmax α hBq hCq jv hout).vertex x (Set.mem_insert x U) = jv := by
  classical
  dsimp only [extend]
  exact dite_eq_left rfl

end
end OnHom
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Integral graded lifting of sheaf morphisms. This is the actual minimal
sheaf recognition mechanism needed to split it out of a Bott--Samelson sheaf;
it does not assume or establish the KL character theorem. -/
namespace KLInvariance.MomentGraph.GradedSheaf.OnHom
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
  (α : E → A) (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
  (hBfree : ∀ x, Module.Free A (B.vertex x))
  (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
  (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
noncomputable section

omit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A] [Fintype V] [Fintype E] in
theorem cast_vertex {U U' : Set V} (h : U=U') (j : OnHom B C U)
    (y : V) (hy : y ∈ U') :
    (h ▸ j).vertex y hy = j.vertex y (h.symm ▸ hy) := by
  subst U'
  rfl

include hneg hzero hBq hCq hBfree hBf hBg hCf hCg in
 theorem exists_extension {U : Set V} (hU : IsUpperSet U) (j : OnHom B C U) :
    ∃ f : Hom B C, ∀ x (hx : x ∈ U), f.vertex x = j.vertex x hx := by
  classical
  have h : ∀ s : Finset V, IsUpperSet ((s : Set V)ᶜ) →
      ∀ j : OnHom B C ((s : Set V)ᶜ),
      ∃ f : Hom B C, ∀ x (hx : x ∈ ((s : Set V)ᶜ)), f.vertex x = j.vertex x hx := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro hU j
      by_cases hs : s=∅
      · subst s
        have heq : ((∅ : Finset V) : Set V)ᶜ=Set.univ := by simp
        let jj : OnHom B C Set.univ := heq ▸ j
        refine ⟨jj.ofUniv,fun y hy => ?_⟩
        exact cast_vertex heq j y (Set.mem_univ y)
      · obtain ⟨x,hxs,hxmax⟩ := s.exists_maximal (Finset.nonempty_iff_ne_empty.mpr hs)
        have hx : x ∉ ((s : Set V)ᶜ) := by simpa using hxs
        have hmax : Set.Ioi x ⊆ ((s : Set V)ᶜ) := by
          intro y hy
          change y ∉ s
          intro hys
          exact (not_le_of_gt hy) (hxmax hys hy.le)
        let := hBfree x
        obtain ⟨l,hl⟩ := j.extend_stalk hneg hzero x hmax hBf hBg hCf hCg
        have hout : ∀ e (he : G.source e=x) v,
            (j.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
              ((B.lower e).map v) =
            (C.lower e).map ((castVertexHom he.symm l).map v) := by
          intro e he v
          subst x
          exact (congrFun (hl v) ⟨e,rfl⟩).symm
        let jj := j.extend hU x hx hmax α hBq hCq l hout
        have heq : insert x ((s : Set V)ᶜ) = ((s.erase x : Finset V) : Set V)ᶜ := by
          ext y
          simp only [Set.mem_insert_iff,Set.mem_compl_iff,Finset.mem_coe,Finset.mem_erase]
          tauto
        have hU' : IsUpperSet (insert x ((s : Set V)ᶜ)) := by
          intro y t hyt hy
          rcases Set.mem_insert_iff.mp hy with hy | hy
          · subst y
            by_cases htx : t=x
            · exact Set.mem_insert_iff.mpr (Or.inl htx)
            · exact Set.mem_insert_of_mem x (hmax (lt_of_le_of_ne hyt (Ne.symm htx)))
          · exact Set.mem_insert_of_mem x (hU hyt hy)
        obtain ⟨f,hf⟩ := ih (s.erase x) (Finset.erase_ssubset hxs) (heq ▸ hU') (heq ▸ jj)
        refine ⟨f,fun y hy => ?_⟩
        have hy' : y ∈ ((s.erase x : Finset V) : Set V)ᶜ :=
          heq ▸ Set.mem_insert_of_mem x hy
        exact (hf y hy').trans ((cast_vertex heq jj y hy').trans
          (j.extend_vertex_old hU x hx hmax α hBq hCq l hout y hy))
  let s := (Uᶜ).toFinset
  have heq : (s : Set V)ᶜ=U := by simp [s]
  obtain ⟨f,hf⟩ := h s (heq.symm ▸ hU) (heq.symm ▸ j)
  refine ⟨f,fun x hx => ?_⟩
  exact (hf x (heq.symm ▸ hx)).trans (cast_vertex heq.symm j x (heq.symm ▸ hx))

end
end KLInvariance.MomentGraph.GradedSheaf.OnHom

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {B C : GradedSheaf (𝓐 := 𝓐) G}
  (α : E → A) (hBq : B.UpperQuotient α) (hCq : C.UpperQuotient α)
  (hBfree : ∀ x, Module.Free A (B.vertex x))
  (hBf : B.forget.Flabby) (hBg : B.forget.Generated)
  (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
  (b : V) (hb : ∀ x, x ≤ b)
noncomputable section

include hneg hzero hBq hCq hBfree hBf hBg hCf hCg hb in
 theorem exists_hom_top (t : ModuleData.Hom (B.vertex b) (C.vertex b)) :
    ∃ f : Hom B C, f.vertex b=t := by
  let je : OnHom B C (∅ : Set V) :=
    { vertex x hx := False.elim hx
      edge e he := False.elim he
      lower e hs := False.elim hs
      upper e ht := False.elim ht }
  have hmax : Set.Ioi b ⊆ (∅ : Set V) := by
    intro x hx
    exact False.elim ((not_lt_of_ge (hb x)) hx)
  have hout : ∀ e (he : G.source e=b) v,
      (je.edge e (hmax (lt_of_eq_of_lt he.symm (G.increasing e)))).map
        ((B.lower e).map v) =
      (C.lower e).map ((castVertexHom he.symm t).map v) := by
    intro e he
    exact False.elim ((not_lt_of_ge (hb (G.target e)))
      (lt_of_eq_of_lt he.symm (G.increasing e)))
  let jj := je.extend isUpperSet_empty b (Set.notMem_empty b) hmax α hBq hCq t hout
  have hU : IsUpperSet (insert b (∅ : Set V)) := by
    intro x y hxy hx
    have hxb : x=b := by simpa using hx
    subst x
    have hyb : y=b := le_antisymm (hb y) hxy
    simpa using hyb
  obtain ⟨f,hf⟩ := jj.exists_extension hneg hzero α hBq hCq hBfree hBf hBg hCf hCg hU
  exact ⟨f,(hf b (Set.mem_insert b _)).trans
    (je.extend_vertex_new isUpperSet_empty b (Set.notMem_empty b) hmax α hBq hCq t hout)⟩

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! The actual minimal boundary sheaf is indecomposable: it has no nontrivial
homogeneous idempotent. No KL character or costalk freeness is used here. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}

namespace Endomorphism
variable {B : GradedSheaf (𝓐 := 𝓐) G} (f : Endomorphism B)

 def complement : Endomorphism B where
  vertex x :=
    { map := LinearMap.id - (f.vertex x).map
      graded := fun n v hv => (B.vertex x).piece n |>.sub_mem hv ((f.vertex x).graded n v hv) }
  edge e :=
    { map := LinearMap.id - (f.edge e).map
      graded := fun n v hv => (B.edge e).piece n |>.sub_mem hv ((f.edge e).graded n v hv) }
  lower e v := by
    change (B.lower e).map v - (f.edge e).map ((B.lower e).map v) =
      (B.lower e).map (v-(f.vertex (G.source e)).map v)
    rw [map_sub,f.lower]
  upper e v := by
    change (B.upper e).map v - (f.edge e).map ((B.upper e).map v) =
      (B.upper e).map (v-(f.vertex (G.target e)).map v)
    rw [map_sub,f.upper]

 theorem complement_idempotent (hi : ∀ x v, (f.vertex x).map ((f.vertex x).map v) =
      (f.vertex x).map v) (x : V) (v : B.vertex x) :
    (f.complement.vertex x).map ((f.complement.vertex x).map v) =
      (f.complement.vertex x).map v := by
  change v-(f.vertex x).map v - (f.vertex x).map (v-(f.vertex x).map v) =
    v-(f.vertex x).map v
  rw [map_sub,hi,sub_self,sub_zero]

end Endomorphism
end KLInvariance.MomentGraph.GradedSheaf

namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {hneg : ∀ n < 0, 𝓐 n = ⊥} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B : BoundarySheaf hneg G α b)

 theorem idempotent_zero_of_top_zero [Finite V]
    (f : B.sheaf.Endomorphism)
    (hi : ∀ x v, (f.vertex x).map ((f.vertex x).map v) = (f.vertex x).map v)
    (ht : (f.vertex b).map = 0) :
    (∀ x, (f.vertex x).map = 0) ∧ (∀ e, (f.edge e).map = 0) := by
  have hv : ∀ x, (f.vertex x).map = 0 := by
    intro x
    induction x using WellFoundedGT.induction with
    | ind x ih =>
      by_cases hx : x=b
      · exact hx ▸ ht
      apply ModuleData.idempotent_eq_zero (B.sheaf.vertex x) (f.vertex x) (hi x)
      intro v hv
      obtain ⟨w,rfl⟩ := hv
      apply (B.sheaf.kernelMinimal_iff x).mp (B.minimal x hx)
      change B.sheaf.forget.stalkMap x ((f.vertex x).map w) = 0
      funext e
      rcases e with ⟨e,he⟩
      subst x
      change (B.sheaf.lower e).map ((f.vertex (G.source e)).map w) = 0
      rw [← f.lower]
      have hezero : (f.edge e).map = 0 := by
        ext z
        obtain ⟨y,rfl⟩ := (B.quotient e).1 z
        rw [f.upper,ih (G.target e) (G.increasing e)]
        exact map_zero _
      rw [hezero]
      rfl
  refine ⟨hv,?_⟩
  intro e
  ext z
  obtain ⟨y,rfl⟩ := (B.quotient e).1 z
  rw [f.upper,hv]
  exact map_zero _

/-- Actual indecomposability in the idempotent formulation. A direct sum
splitting supplies such a homogeneous idempotent, hence one summand vanishes. -/
 theorem idempotent_trivial [Finite V] [IsDomain A]
    (f : B.sheaf.Endomorphism)
    (hi : ∀ x v, (f.vertex x).map ((f.vertex x).map v) = (f.vertex x).map v) :
    ((∀ x, (f.vertex x).map = 0) ∧ (∀ e, (f.edge e).map = 0)) ∨
      ((∀ x, (f.vertex x).map = LinearMap.id) ∧
        (∀ e, (f.edge e).map = LinearMap.id)) := by
  have ht : (f.vertex b).map = 0 ∨ (f.vertex b).map = LinearMap.id := by
    have h := B.top
    have general (N : ModuleData.{uk,ua,um} 𝓐) (hN : N=ModuleData.unit hneg)
        (g : ModuleData.Hom N N) (hg : ∀v, g.map (g.map v)=g.map v) :
        g.map=0 ∨ g.map=LinearMap.id := by
      subst N
      exact ModuleData.unit_idempotent_trivial hneg g hg
    exact general _ h (f.vertex b) (hi b)
  rcases ht with ht | ht
  · exact Or.inl (B.idempotent_zero_of_top_zero f hi ht)
  · right
    have hh : (f.complement.vertex b).map = 0 := by
      change LinearMap.id - (f.vertex b).map = 0
      rw [ht,sub_self]
    obtain ⟨hv,he⟩ := B.idempotent_zero_of_top_zero f.complement
      (f.complement_idempotent hi) hh
    constructor
    · intro x
      exact (sub_eq_zero.mp (hv x)).symm
    · intro e
      exact (sub_eq_zero.mp (he e)).symm

end KLInvariance.MomentGraph.BoundarySheaf

end


section

/-! A graded endomorphism of the actual normalized minimal boundary sheaf
is an automorphism as soon as its top component is one. -/

namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B : BoundarySheaf hneg G α b)
noncomputable section

include hzero in
 theorem endomorphism_bijective_of_top (f : B.sheaf.Endomorphism)
    (ht : Function.Bijective (f.vertex b).map) :
    (∀ x, Function.Bijective (f.vertex x).map) ∧
    (∀ e, Function.Bijective (f.edge e).map) := by
  have hv : ∀ x, Function.Bijective (f.vertex x).map := by
    intro x
    induction x using WellFoundedGT.induction with
    | ind x ih =>
      by_cases hx : x=b
      · exact hx ▸ ht
      let j : Sheaf.AboveIso B.sheaf.forget B.sheaf.forget x :=
        { vertex y hy := LinearEquiv.ofBijective (f.vertex y).map (ih y hy)
          edge e he := LinearEquiv.ofBijective (f.edge e).map
            (f.edge_bijective_of_vertex B.quotient e (ih _ he))
          lower e he v := f.lower e v
          upper e he v := f.upper e v }
      let T := ModuleData.range (B.sheaf.stalkHom x)
      let g : T ≃ₗ[A] T := LinearEquiv.ofSubmodules j.boundary _ _
        (j.map_stalk_image B.flabby.flabby B.generated B.flabby.flabby B.generated)
      have hg : ∀ n v, v ∈ T.piece n → g v ∈ T.piece n := by
        intro n v hv e he
        exact (f.edge e.val).graded n _ (hv e he)
      let π : ModuleData.Hom (B.sheaf.vertex x) T :=
        { map := (B.sheaf.forget.stalkMap x).rangeRestrict
          graded := fun n v hv => (B.sheaf.stalkHom x).graded n v hv }
      have hπs : Function.Surjective π.map := by
        intro v
        obtain ⟨w,hw⟩ := v.property
        exact ⟨w,Subtype.ext hw⟩
      have hπm : LinearMap.ker π.map ≤
          positiveIdeal 𝓐 • (⊤ : Submodule A (B.sheaf.vertex x)) := by
        intro v hv
        apply (B.sheaf.kernelMinimal_iff x).mp (B.minimal x hx)
        have hh : π.map v = 0 := LinearMap.mem_ker.mp hv
        exact congrArg (fun z : T => z.val) hh
      let C : ModuleData.MinimalCover T := ⟨B.sheaf.vertex x,B.free x,π,hπs,hπm⟩
      apply C.bijective_of_boundaryIso hneg hzero (f.vertex x) g hg
      intro v
      apply Subtype.ext
      funext e
      change B.sheaf.forget.stalkMap x ((f.vertex x).map v) e =
        (f.edge e.val).map (B.sheaf.forget.stalkMap x v e)
      rcases e with ⟨e,rfl⟩
      exact (f.lower e v).symm
  exact ⟨hv,fun e => f.edge_bijective_of_vertex B.quotient e (hv _)⟩

end
end KLInvariance.MomentGraph.BoundarySheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section

 def Hom.toEndomorphism {B : GradedSheaf (𝓐 := 𝓐) G} (f : Hom B B) : Endomorphism B :=
  ⟨f.vertex,f.edge,f.lower,f.upper⟩

 def Hom.inverse {B C : GradedSheaf (𝓐 := 𝓐) G} (f : Hom B C)
    (hv : ∀ x, Function.Bijective (f.vertex x).map)
    (he : ∀ e, Function.Bijective (f.edge e).map) : Hom C B where
  vertex x := (f.vertex x).inverse (hv x)
  edge e := (f.edge e).inverse (he e)
  lower e v := by
    apply (he e).1
    rw [(f.edge e).map_inverse]
    rw [f.lower,(f.vertex _).map_inverse]
  upper e v := by
    apply (he e).1
    rw [(f.edge e).map_inverse]
    rw [f.upper,(f.vertex _).map_inverse]

 structure SplitIn (B C : GradedSheaf (𝓐 := 𝓐) G) where
  inclusion : Hom B C
  projection : Hom C B
  vertex_split : ∀ x v, (projection.vertex x).map ((inclusion.vertex x).map v)=v
  edge_split : ∀ e v, (projection.edge e).map ((inclusion.edge e).map v)=v

end
end KLInvariance.MomentGraph.GradedSheaf

namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  {hneg : ∀ n < 0, 𝓐 n = ⊥}
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (B : BoundarySheaf hneg G α b) (hb : ∀ x, x ≤ b)
  (C : GradedSheaf (𝓐 := 𝓐) G)
  (hCq : C.UpperQuotient α) (hCfree : ∀ x, Module.Free A (C.vertex x))
  (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
noncomputable section

include hzero hb hCq hCfree hCf hCg in
 theorem splitIn_of_top_split
    (i : ModuleData.Hom (B.sheaf.vertex b) (C.vertex b))
    (p : ModuleData.Hom (C.vertex b) (B.sheaf.vertex b))
    (hpi : ∀ v, p.map (i.map v)=v) : Nonempty (GradedSheaf.SplitIn B.sheaf C) := by
  obtain ⟨ii,hii⟩ := GradedSheaf.exists_hom_top hneg hzero α B.quotient hCq B.free
    B.flabby.flabby B.generated hCf hCg b hb i
  obtain ⟨pp,hpp⟩ := GradedSheaf.exists_hom_top hneg hzero α hCq B.quotient hCfree
    hCf hCg B.flabby.flabby B.generated b hb p
  let f := pp.comp ii
  have ht : Function.Bijective (f.toEndomorphism.vertex b).map := by
    have heq : (f.toEndomorphism.vertex b).map = LinearMap.id := by
      apply LinearMap.ext
      intro v
      change (pp.vertex b).map ((ii.vertex b).map v)=v
      rw [hpp,hii]
      exact hpi v
    rw [heq]
    exact Function.bijective_id
  obtain ⟨hv,he⟩ := B.endomorphism_bijective_of_top hzero f.toEndomorphism ht
  let fi := f.inverse hv he
  refine ⟨⟨ii.comp fi,pp,?_,?_⟩⟩
  · intro x v
    exact (f.vertex x).map_inverse (hv x) v
  · intro e v
    exact (f.edge e).map_inverse (he e) v

end
end KLInvariance.MomentGraph.BoundarySheaf

end


end OAI
end

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

/-! The genuine symmetric-algebra grading of the extended real realization,
transported along a specified realization basis only to access polynomial
homogeneous components. The algebra and action are unchanged. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded ReflectionFrobenius
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def symmetricGrading : ℤ → Submodule ℝ (SymmetricCoefficient (M := M)) :=
  fun n => (polynomialGrading ℝ σ n).map
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap

omit [Fintype σ] in
 theorem mem_symmetricGrading (n : ℤ) (a : SymmetricCoefficient (M := M)) :
    a ∈ symmetricGrading basis n ↔
      SymmetricAlgebra.equivMvPolynomial basis a ∈ polynomialGrading ℝ σ n := by
  constructor
  · rintro ⟨p,hp,hpa⟩
    rw [← hpa]
    simpa using hp
  · intro h
    exact ⟨_,h,(SymmetricAlgebra.equivMvPolynomial basis).symm_apply_apply a⟩

 instance symmetricGrading_decomposition : DirectSum.Decomposition (symmetricGrading basis) := by
  apply DirectSum.IsInternal.chooseDecomposition
  apply image_isInternal (polynomialGrading ℝ σ)
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toLinearMap
    (SymmetricAlgebra.equivMvPolynomial basis).symm.surjective
  intro n p hp
  have hz : p=0 := (SymmetricAlgebra.equivMvPolynomial basis).symm.injective
    (by simpa using hp)
  subst p
  simp

 instance symmetricGrading_graded : SetLike.GradedMonoid (symmetricGrading basis) where
  one_mem := (mem_symmetricGrading basis 0 1).mpr (by
    rw [map_one]
    exact SetLike.one_mem_graded (polynomialGrading ℝ σ))
  mul_mem := by
    intro n m a b ha hb
    apply (mem_symmetricGrading basis (n+m) (a*b)).mpr
    rw [map_mul]
    exact SetLike.GradedMul.mul_mem ((mem_symmetricGrading basis n a).mp ha)
      ((mem_symmetricGrading basis m b).mp hb)

omit [Fintype σ] in
 theorem symmetricGrading_negative (n : ℤ) (hn : n<0) :
    symmetricGrading basis n = ⊥ := by
  simp [symmetricGrading,polynomialGrading_negative ℝ σ n hn]

 theorem simpleRoot_homogeneous (i : I) :
    simpleRootPolynomial (M := M) i ∈ symmetricGrading basis 1 := by
  apply (mem_symmetricGrading basis 1 _).mpr
  exact polynomialLinear_homogeneous basis _

 theorem coefficientAction_homogeneous (w : W) (n : ℤ)
    (a : SymmetricCoefficient (M := M)) (ha : a ∈ symmetricGrading basis n) :
    coefficientAction cs w a ∈ symmetricGrading basis n := by
  apply (mem_symmetricGrading basis n _).mpr
  have h := polynomialAction_homogeneous basis (extendedAction M cs w)
    ((mem_symmetricGrading basis n a).mp ha)
  simpa only [polynomialAction,AlgEquiv.trans_apply,AlgEquiv.symm_apply_apply,
    coefficientAction] using h

end
end KLInvariance.TitsSpace

end


section

/-! The actual tensor-defined Bott--Samelson module has the word grading and
its integral duality lowers degree by word length (degree-one roots).
This does not identify an indecomposable summand with the BMP sheaf. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
open _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def BottIndex : List I → Type u
  | [] => PUnit
  | _ :: l => Fin 2 × BottIndex l

 instance bottIndex_fintype : (l : List I) → Fintype (BottIndex l)
  | [] => inferInstanceAs (Fintype PUnit)
  | _ :: l => by
      let _ := bottIndex_fintype l
      exact inferInstanceAs (Fintype (Fin 2 × BottIndex l))

 def bottDegree : (l : List I) → BottIndex l → ℤ
  | [], _ => 0
  | _ :: l, e => e.1.val + bottDegree l e.2

 def bottBasis : (l : List I) → Basis (BottIndex l) (SymmetricCoefficient (M := M))
    (BottSamelsonModule cs l)
  | [] => Basis.singleton PUnit _
  | i :: l => by
      let : Module.Free (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
        simpleFixed_free cs i
      let : Module.Finite (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
        simpleFixed_finite cs i
      exact inducedBasis (coefficientAction cs (cs.simple i))
        (simpleRootPolynomial i) (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
        (simple_anti cs i) (simple_divisible cs i) (bottSamelson cs l).obj (bottBasis l)

 instance bottRealModule (l : List I) : Module ℝ (BottSamelsonModule cs l) :=
  Module.compHom _ (algebraMap ℝ (SymmetricCoefficient (M := M)))

 instance bottRealTower (l : List I) :
    IsScalarTower ℝ (SymmetricCoefficient (M := M)) (BottSamelsonModule cs l) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

 def bottPiece (l : List I) : ℤ → Submodule ℝ (BottSamelsonModule cs l) :=
  basisPiece (symmetricGrading basis) (bottBasis cs l) (bottDegree l)

 instance bottPiece_decomposition (l : List I) : DirectSum.Decomposition (bottPiece cs basis l) :=
  basisPiece_decomposition _ _ _

 instance bottPiece_graded (l : List I) :
    SetLike.GradedSMul (symmetricGrading basis) (bottPiece cs basis l) :=
  basisPiece_graded _ _ _

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

 def bottWeight : (l : List I) → BottIndex l → W
  | [], _ => 1
  | i::l, e => if e.1=0 then bottWeight l e.2 else cs.simple i*bottWeight l e.2

attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def weightFunctional (i : I) (N : PairedModule.{u,un} (SymmetricCoefficient (M := M)))
    (f : N →ₗ[SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M))
    (ε : Fin 2) : N →ₗ[simpleFixed cs i] SymmetricCoefficient (M := M) where
  toFun m := if ε=0 then f m else coefficientAction cs (cs.simple i) (f m)
  map_add' m n := by split_ifs <;> simp only [map_add]
  map_smul' c m := by
    change (if ε=0 then f ((c:SymmetricCoefficient (M:=M)) • m) else
      coefficientAction cs (cs.simple i) (f ((c:SymmetricCoefficient (M:=M)) • m))) = _
    split_ifs
    · simp only [map_smul,Subalgebra.smul_def,RingHom.id_apply]
    · rw [map_smul]
      change coefficientAction cs (cs.simple i)
        ((c:SymmetricCoefficient (M:=M))*f m) =
        (c:SymmetricCoefficient (M:=M))*coefficientAction cs (cs.simple i) (f m)
      rw [map_mul, show coefficientAction cs (cs.simple i) (c:SymmetricCoefficient (M:=M)) = c from c.property]

 def inducedFunctional (i : I) (N : PairedModule.{u,un} (SymmetricCoefficient (M := M)))
    (f : N →ₗ[simpleFixed cs i] SymmetricCoefficient (M := M)) :
    (SymmetricCoefficient (M := M) ⊗[simpleFixed cs i] N) →ₗ[SymmetricCoefficient (M := M)]
      SymmetricCoefficient (M := M) :=
  AlgebraTensorModule.lift ((LinearMap.id : SymmetricCoefficient (M := M) →ₗ[
    SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M)).smulRight f)

 def bottEvaluation : (l : List I) → BottIndex l →
    BottSamelsonModule cs l →ₗ[SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M)
  | [], _ => LinearMap.id
  | i::l, e => inducedFunctional cs i (bottSamelson cs l).obj
      (weightFunctional cs i (bottSamelson cs l).obj (bottEvaluation l e.2) e.1)

 theorem bottEvaluation_tmul (i : I) (l : List I) (e : BottIndex (i::l))
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottEvaluation cs (i::l) e (a ⊗ₜ[simpleFixed cs i] m) =
      a*(if e.1=0 then bottEvaluation cs l e.2 m else
        coefficientAction cs (cs.simple i) (bottEvaluation cs l e.2 m)) := rfl

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

 def bottEvaluationMatrix (l : List I) : Matrix (BottIndex l) (BottIndex l)
    (SymmetricCoefficient (M := M)) := fun e j => bottEvaluation cs l e (bottBasis cs l j)

 theorem bottEvaluation_expand (l : List I) (e : BottIndex l) (m : BottSamelsonModule cs l) :
    bottEvaluation cs l e m =
      (bottEvaluationMatrix cs l *ᵥ (bottBasis cs l).equivFun m) e := by
  classical
  conv_lhs => rw [← (bottBasis cs l).sum_repr m]
  simp only [map_sum,map_smul,smul_eq_mul,Matrix.mulVec,dotProduct,
    bottEvaluationMatrix,Basis.equivFun_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

 theorem bottEvaluationMatrix_cons (i : I) (l : List I)
    (r c : Fin 2) (j k : BottIndex l) :
    bottEvaluationMatrix cs (i::l) (r,j) (c,k) =
      if r=0 then (if c=0 then bottEvaluationMatrix cs l j k else
        simpleRootPolynomial i*bottEvaluationMatrix cs l j k)
      else if c=0 then coefficientAction cs (cs.simple i) (bottEvaluationMatrix cs l j k)
      else -simpleRootPolynomial i*coefficientAction cs (cs.simple i) (bottEvaluationMatrix cs l j k) := by
  let : Module.Free (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
    simpleFixed_free cs i
  let : Module.Finite (fixed (coefficientAction cs (cs.simple i))) (SymmetricCoefficient (M := M)) :=
    simpleFixed_finite cs i
  change bottEvaluation cs (i::l) (r,j)
    (inducedBasis (coefficientAction cs (cs.simple i)) (simpleRootPolynomial i)
      (simple_involutive cs i) (simpleRootPolynomial_ne_zero i) (simple_anti cs i)
      (simple_divisible cs i) (bottSamelson cs l).obj (bottBasis cs l) (c,k)) = _
  rw [inducedBasis_apply]
  erw [bottEvaluation_tmul]
  fin_cases r <;> fin_cases c <;>
    simp only [Fin.zero_eta,Fin.isValue,Fin.mk_one,ite_true, if_true,
      show (1:Fin 2) ≠ 0 by decide,ite_false, if_false,reflectionBasis_zero,reflectionBasis_one,
      one_smul,one_mul,map_smul,smul_eq_mul,map_mul,simple_anti,bottEvaluationMatrix]

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

 def bottWeightProjection (l : List I) (x : W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)]
    ({e : BottIndex l // bottWeight cs l e=x} → SymmetricCoefficient (M := M)) :=
  LinearMap.pi (fun e => bottEvaluation cs l e.val)

 def bottStalk (l : List I) (x : W) : Submodule (SymmetricCoefficient (M := M))
    ({e : BottIndex l // bottWeight cs l e=x} → SymmetricCoefficient (M := M)) :=
  LinearMap.range (bottWeightProjection cs l x)

 def bottStalkProjection (l : List I) (x : W) : BottSamelsonModule cs l →ₗ[
    SymmetricCoefficient (M := M)] bottStalk cs l x :=
  (bottWeightProjection cs l x).rangeRestrict

 theorem bottStalkProjection_surjective (l : List I) (x : W) :
    Function.Surjective (bottStalkProjection cs l x) := by
  rintro ⟨v,m,hm⟩
  exact ⟨m,Subtype.ext hm⟩

end
end KLInvariance.TitsSpace

end


section

/-! Exact Bruhat support of the actual tensor word's subexpression weights.
The ambient Coxeter system is not assumed crystallographic. -/
namespace KLInvariance.TitsSpace
universe u v
variable {I : Type u} {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSubword : (l : List I) → BottIndex l → List I
  | [], _ => []
  | i::l, e => if e.1=0 then bottSubword l e.2 else i::bottSubword l e.2

 theorem bottSubword_sublist (l : List I) (e : BottIndex l) :
    (bottSubword l e).Sublist l := by
  induction l with
  | nil => exact List.Sublist.refl []
  | cons i l ih =>
    by_cases h : e.1=0
    · rw [bottSubword,ite_eq_left h]
      exact List.Sublist.cons i (ih e.2)
    · rw [bottSubword,ite_eq_right h]
      exact List.Sublist.cons_cons i (ih e.2)

 theorem bottSubword_wordProd (l : List I) (e : BottIndex l) :
    cs.wordProd (bottSubword l e) = bottWeight cs l e := by
  induction l with
  | nil => exact cs.wordProd_nil
  | cons i l ih =>
    by_cases h : e.1=0
    · simp only [bottSubword,bottWeight,ite_eq_left h,ih]
    · simp only [bottSubword,bottWeight,ite_eq_right h,cs.wordProd_cons,ih]

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

/-! The top projection lattice of a reduced actual tensor word is exactly A.
This verifies the genuine rank-one top used in the BMP summand construction;
it does not assert that the other projection lattices form a flabby sheaf. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottFullIndex : (l : List I) → BottIndex l
  | [] => PUnit.unit
  | _::l => (1,bottFullIndex l)

omit [Fintype I] in
 theorem bottWeight_full (l : List I) :
    bottWeight cs l (bottFullIndex l)=cs.wordProd l := by
  induction l with
  | nil => exact cs.wordProd_nil.symm
  | cons i l ih =>
    simp only [bottFullIndex,bottWeight,show (1:Fin 2) ≠ 0 by decide,ite_false, if_false,
      cs.wordProd_cons,ih]

omit [Fintype I] in
 theorem bottSubword_length_eq_full (l : List I) (e : BottIndex l)
    (h : (bottSubword l e).length=l.length) : e=bottFullIndex l := by
  induction l with
  | nil =>
    change PUnit at e
    change e=(PUnit.unit : PUnit)
    exact Subsingleton.elim _ _
  | cons i l ih =>
    change Fin 2 × BottIndex l at e
    by_cases he : e.1=0
    · simp only [bottSubword,ite_eq_left he,List.length_cons] at h
      have hn := (bottSubword_sublist l e.2).length_le
      omega
    · have he1 : e.1=1 := by omega
      simp only [bottSubword,ite_eq_right he,List.length_cons] at h
      exact Prod.ext he1 (ih e.2 (Nat.succ.inj h))

omit [Fintype I] in
 theorem bottWeight_eq_top (l : List I) (hl : cs.IsReduced l) (e : BottIndex l)
    (he : bottWeight cs l e=cs.wordProd l) : e=bottFullIndex l := by
  apply bottSubword_length_eq_full
  apply Nat.le_antisymm (bottSubword_sublist l e).length_le
  have hh := cs.length_wordProd_le (bottSubword l e)
  rwa [bottSubword_wordProd,he,hl.eq] at hh

 def bottUnit : (l : List I) → BottSamelsonModule cs l
  | [] => (1 : SymmetricCoefficient (M := M))
  | i::l => 1 ⊗ₜ[simpleFixed cs i] bottUnit l

 theorem bottEvaluation_unit (l : List I) (e : BottIndex l) :
    bottEvaluation cs l e (bottUnit cs l)=1 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change bottEvaluation cs (i::l) e (1 ⊗ₜ[simpleFixed cs i] bottUnit cs l)=1
    rw [bottEvaluation_tmul,ih]
    split_ifs <;> simp only [map_one,mul_one]

 theorem bottEvaluation_surjective (l : List I) (e : BottIndex l) :
    Function.Surjective (bottEvaluation cs l e) := by
  intro a
  refine ⟨a • bottUnit cs l,?_⟩
  rw [map_smul,bottEvaluation_unit,smul_eq_mul,mul_one]

 def bottTopCoordinate (l : List I) : bottStalk cs l (cs.wordProd l) →ₗ[
    SymmetricCoefficient (M := M)] SymmetricCoefficient (M := M) :=
  (LinearMap.proj ⟨bottFullIndex l,bottWeight_full cs l⟩).comp
    (bottStalk cs l (cs.wordProd l)).subtype

end
end KLInvariance.TitsSpace

end


section

/-! The genuine subexpression projections preserve the actual word grading.
In particular the top projection of a reduced tensor word is a graded copy of
A, rather than just an ungraded rank-one lattice. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem bottEvaluation_basis_homogeneous (l : List I) (e f : BottIndex l) :
    bottEvaluationMatrix cs l e f ∈ symmetricGrading basis (bottDegree l f) := by
  induction l with
  | nil =>
    change PUnit at e f
    change (Basis.singleton PUnit (SymmetricCoefficient (M := M)) f) ∈
      symmetricGrading basis 0
    simp only [Basis.singleton_apply]
    exact SetLike.one_mem_graded _
  | cons i l ih =>
    change Fin 2 × BottIndex l at e f
    rcases e with ⟨r,j⟩
    rcases f with ⟨c,k⟩
    rw [bottEvaluationMatrix_cons]
    by_cases hc : c=0
    · subst c
      simp only [ite_true, if_true,bottDegree,Fin.val_zero,Nat.cast_zero,zero_add]
      split_ifs
      · exact ih j k
      · exact coefficientAction_homogeneous cs basis _ _ _ (ih j k)
    · have hc1 : c=1 := by omega
      subst c
      simp only [show (1:Fin 2) ≠ 0 by decide,ite_false, if_false,bottDegree,Fin.val_one,Nat.cast_one]
      split_ifs
      · exact SetLike.GradedMul.mul_mem (simpleRoot_homogeneous basis i) (ih j k)
      · exact SetLike.GradedMul.mul_mem ((symmetricGrading basis 1).neg_mem
          (simpleRoot_homogeneous basis i))
          (coefficientAction_homogeneous cs basis _ _ _ (ih j k))

 theorem bottEvaluation_homogeneous (l : List I) (e : BottIndex l)
    (n : ℤ) (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottEvaluation cs l e m ∈ symmetricGrading basis n := by
  classical
  have hexp : bottEvaluation cs l e m = ∑ f : BottIndex l,
      (bottBasis cs l).repr m f * bottEvaluationMatrix cs l e f := by
    conv_lhs => rw [← (bottBasis cs l).sum_repr m]
    simp only [map_sum,map_smul,smul_eq_mul,bottEvaluationMatrix]
  rw [hexp]
  apply Submodule.sum_mem
  intro f _
  change ∀ f, (bottBasis cs l).repr m f ∈
    symmetricGrading basis (n-bottDegree l f) at hm
  have h := SetLike.GradedMul.mul_mem (hm f)
    (bottEvaluation_basis_homogeneous cs basis l e f)
  simpa only [sub_add_cancel] using h

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

 def bottCoordinatePiece (l : List I) (x : W) : ℤ → Submodule ℝ
    ({e : BottIndex l // bottWeight cs l e=x} → SymmetricCoefficient (M := M)) :=
  piPiece (fun _ => symmetricGrading basis)

 instance bottCoordinatePiece_decomposition (l : List I) (x : W) :
    DirectSum.Decomposition (bottCoordinatePiece cs basis l x) := by
  classical
  exact (pi_isInternal (fun _ : {e : BottIndex l // bottWeight cs l e=x} =>
    symmetricGrading basis)).chooseDecomposition

 instance bottCoordinatePiece_graded (l : List I) (x : W) :
    SetLike.GradedSMul (symmetricGrading basis) (bottCoordinatePiece cs basis l x) :=
  inferInstanceAs (SetLike.GradedSMul (symmetricGrading basis)
    (piPiece (fun _ : {e : BottIndex l // bottWeight cs l e=x} => symmetricGrading basis)))

 theorem bottWeightProjection_homogeneous (l : List I) (x : W) (n : ℤ)
    (m : BottSamelsonModule cs l) (hm : m ∈ bottPiece cs basis l n) :
    bottWeightProjection cs l x m ∈ bottCoordinatePiece cs basis l x n := by
  intro e _
  exact bottEvaluation_homogeneous cs basis l e.val n m hm

 theorem bottStalk_homogeneous (l : List I) (x : W) :
    ∀ n f, f ∈ bottStalk cs l x →
      component (bottCoordinatePiece cs basis l x) n f ∈ bottStalk cs l x := by
  exact range_homogeneous (bottPiece cs basis l) (bottCoordinatePiece cs basis l x)
    (bottWeightProjection cs l x) 0 (by
      simpa only [add_zero] using bottWeightProjection_homogeneous cs basis l x)

 def bottStalkPiece (l : List I) (x : W) : ℤ → Submodule ℝ (bottStalk cs l x) :=
  subPiece (bottCoordinatePiece cs basis l x) (bottStalk cs l x)

 instance bottStalkPiece_decomposition (l : List I) (x : W) :
    DirectSum.Decomposition (bottStalkPiece cs basis l x) :=
  (sub_isInternal (bottCoordinatePiece cs basis l x) (bottStalk cs l x)
    (bottStalk_homogeneous cs basis l x)).chooseDecomposition

 instance bottStalkPiece_graded (l : List I) (x : W) :
    SetLike.GradedSMul (symmetricGrading basis) (bottStalkPiece cs basis l x) :=
  inferInstanceAs (SetLike.GradedSMul (symmetricGrading basis)
    (subPiece (bottCoordinatePiece cs basis l x) (bottStalk cs l x)))

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

omit [Fintype σ] in
 theorem bottStalkPiece_negative (l : List I) (x : W) (n : ℤ) (hn : n<0) :
    bottStalkPiece cs basis l x n=⊥ := by
  apply subPiece_eq_bot
  exact piPiece_eq_bot (fun _ => symmetricGrading basis) n
    (fun _ => symmetricGrading_negative basis n hn)

 def bottStalkData (l : List I) (x : W) : ModuleData.{0,u,u} (symmetricGrading basis) where
  obj := ModuleCat.of _ (bottStalk cs l x)
  kModule := inferInstance
  tower := inferInstance
  piece := bottStalkPiece cs basis l x
  decomposition := inferInstance
  graded := inferInstance
  nonneg := bottStalkPiece_negative cs basis l x
  finite := Module.Finite.of_surjective (bottStalkProjection cs l x)
    (bottStalkProjection_surjective cs l x)

end
end KLInvariance.TitsSpace

end


section

/-! Grading-preserving coefficient change on the actual finite modules. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
noncomputable section

 theorem change_free (M : ModuleData.{uk,ua,um} 𝓐) [Module.Free A M] :
    Module.Free B (change e he M) := inferInstanceAs (Module.Free B (CoefficientChange e M))

end
end KLInvariance.Graded.ModuleData

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

namespace KLInvariance.TitsSpace
open Module
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))

include basis in
 theorem symmetricCoefficientNoetherian : IsNoetherianRing (SymmetricCoefficient (M := M)) :=
  isNoetherianRing_of_surjective (MvPolynomial σ ℝ) (SymmetricCoefficient (M := M))
    (SymmetricAlgebra.equivMvPolynomial basis).symm.toRingHom
    (SymmetricAlgebra.equivMvPolynomial basis).symm.surjective

end KLInvariance.TitsSpace

end


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

 def SplitIn.projector : Hom C C := s.inclusion.comp s.projection

omit [IsNoetherianRing A] in
 theorem SplitIn.projector_vertex (x : V) (v : C.vertex x) :
    (s.projector.vertex x).map ((s.projector.vertex x).map v)=(s.projector.vertex x).map v := by
  change (s.inclusion.vertex x).map ((s.projection.vertex x).map
    ((s.inclusion.vertex x).map ((s.projection.vertex x).map v)))=_
  rw [s.vertex_split]
  rfl

omit [IsNoetherianRing A] in
 theorem SplitIn.projector_edge (e : E) (v : C.edge e) :
    (s.projector.edge e).map ((s.projector.edge e).map v)=(s.projector.edge e).map v := by
  change (s.inclusion.edge e).map ((s.projection.edge e).map
    ((s.inclusion.edge e).map ((s.projection.edge e).map v)))=_
  rw [s.edge_split]
  rfl

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}

 theorem Hom.eq_of_maps (f g : Hom B C)
    (hv : ∀ x v, (f.vertex x).map v=(g.vertex x).map v)
    (he : ∀ e v, (f.edge e).map v=(g.edge e).map v) : f=g := by
  have hv' : f.vertex=g.vertex := funext (fun x =>
    ModuleData.Hom.eq_of_map_eq _ _ (LinearMap.ext (hv x)))
  have he' : f.edge=g.edge := funext (fun e =>
    ModuleData.Hom.eq_of_map_eq _ _ (LinearMap.ext (he e)))
  cases f
  cases g
  cases hv'
  cases he'
  rfl

end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! The endomorphism-corner formulation of a primitive graded sheaf
projector. This is a criterion, not an assertion of a BMP splitting. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}

 def Hom.zero : Hom B C where
  vertex x := ⟨0,fun n _ _ => (C.vertex x).piece n |>.zero_mem⟩
  edge e := ⟨0,fun n _ _ => (C.edge e).piece n |>.zero_mem⟩
  lower e v := by simp
  upper e v := by simp

 def Hom.id (B : GradedSheaf (𝓐 := 𝓐) G) : Hom B B where
  vertex x := ModuleData.Hom.id (B.vertex x)
  edge e := ModuleData.Hom.id (B.edge e)
  lower _ _ := rfl
  upper _ _ := rfl

 def Hom.PrimitiveProjector (p : Hom B B) : Prop :=
  p.comp p=p ∧ ∀ f : Hom B B, f.comp f=f → f.comp p=f → p.comp f=f →
    f=Hom.zero ∨ f=p

end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Primitive-corner recognition for genuine graded sheaf splittings.
This supplies the algebraic recognition step for a prospective BMP summand;
it neither postulates the splitting nor the word/BMP character. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
  {B C : GradedSheaf (𝓐 := 𝓐) G}
noncomputable section

 theorem SplitIn.projector_eq_id_of_primitive (s : SplitIn B C)
    (h : (Hom.id C).PrimitiveProjector)
    (x : V) [Nontrivial (B.vertex x)] : s.projector=Hom.id C := by
  have hi : s.projector.comp s.projector=s.projector := by
    apply Hom.eq_of_maps
    · exact s.projector_vertex
    · exact s.projector_edge
  have hl : s.projector.comp (Hom.id C)=s.projector := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  have hr : (Hom.id C).comp s.projector=s.projector := by
    apply Hom.eq_of_maps <;> intros <;> rfl
  rcases h.2 s.projector hi hl hr with hz | he
  · obtain ⟨v,hv⟩ := exists_ne (0 : B.vertex x)
    exfalso
    apply hv
    have hh := congrArg (fun q : Hom C C => (s.projection.vertex x).map
      ((q.vertex x).map ((s.inclusion.vertex x).map v))) hz
    change (s.projection.vertex x).map ((s.inclusion.vertex x).map
      ((s.projection.vertex x).map ((s.inclusion.vertex x).map v)))=
      (s.projection.vertex x).map 0 at hh
    simpa only [s.vertex_split,map_zero] using hh
  · exact he

 def SplitIn.isoOfProjectorEqId (s : SplitIn B C) (h : s.projector=Hom.id C) : Iso B C where
  vertex x :=
    { toLinearMap := (s.inclusion.vertex x).map
      invFun := (s.projection.vertex x).map
      left_inv := s.vertex_split x
      right_inv := fun v => congrArg (fun q : Hom C C => (q.vertex x).map v) h }
  edge e :=
    { toLinearMap := (s.inclusion.edge e).map
      invFun := (s.projection.edge e).map
      left_inv := s.edge_split e
      right_inv := fun v => congrArg (fun q : Hom C C => (q.edge e).map v) h }
  lower e v := s.inclusion.lower e v
  upper e v := s.inclusion.upper e v
  vertex_graded x := (s.inclusion.vertex x).graded
  edge_graded e := (s.inclusion.edge e).graded

 def SplitIn.isoOfPrimitive (s : SplitIn B C)
    (h : (Hom.id C).PrimitiveProjector)
    (x : V) [Nontrivial (B.vertex x)] : Iso B C :=
  s.isoOfProjectorEqId (s.projector_eq_id_of_primitive h x)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! A normalized minimal boundary sheaf is primitive, and that property
passes to its projector in every ACTUAL graded splitting. No word splitting
is asserted here. -/

namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {hneg : ∀ n < 0, 𝓐 n=⊥} {V E : Type um} [PartialOrder V] [Finite V]
  {G : OrderedGraph V E} {α : E → A} {b : V} [IsDomain A]
  (B : BoundarySheaf hneg G α b)

 theorem primitive_identity : (GradedSheaf.Hom.id B.sheaf).PrimitiveProjector := by
  constructor
  · apply GradedSheaf.Hom.eq_of_maps <;> intros <;> rfl
  · intro f hf _ _
    have hi : ∀ x v, (f.toEndomorphism.vertex x).map ((f.toEndomorphism.vertex x).map v)=
        (f.toEndomorphism.vertex x).map v := by
      intro x v
      exact congrArg (fun q : GradedSheaf.Hom B.sheaf B.sheaf => (q.vertex x).map v) hf
    rcases B.idempotent_trivial f.toEndomorphism hi with hz | hi
    · left
      apply GradedSheaf.Hom.eq_of_maps
      · intro x v
        exact LinearMap.congr_fun (hz.1 x) v
      · intro e v
        exact LinearMap.congr_fun (hz.2 e) v
    · right
      apply GradedSheaf.Hom.eq_of_maps
      · intro x v
        exact LinearMap.congr_fun (hi.1 x) v
      · intro e v
        exact LinearMap.congr_fun (hi.2 e) v

end KLInvariance.MomentGraph.BoundarySheaf

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


namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem symmetricGrading_zero (a : SymmetricCoefficient (M := M))
    (ha : a ∈ symmetricGrading basis 0) :
    ∃ c : ℝ, algebraMap ℝ (SymmetricCoefficient (M := M)) c=a := by
  obtain ⟨c,hc⟩ := polynomialGrading_zero ℝ σ
    (SymmetricAlgebra.equivMvPolynomial basis a) ((mem_symmetricGrading basis 0 a).mp ha)
  refine ⟨c,?_⟩
  apply (SymmetricAlgebra.equivMvPolynomial basis).injective
  exact ((SymmetricAlgebra.equivMvPolynomial basis).commutes c).trans hc

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

 theorem equivOfEq_inverse {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N) (m : M) :
    equivOfEq h.symm (equivOfEq h m)=m := by
  subst N
  rfl

end KLInvariance.Graded.ModuleData

end


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

 def symmetricLabel (u b : W) (e : Edge cs u b) : SymmetricCoefficient (M := M) :=
  SymmetricAlgebra.ι ℝ (Extended M) (embed M (BruhatGraph.root cs u b e).val)

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 def coefficientChange (S : GradedSheaf (𝓐 := 𝓐) G) : GradedSheaf (𝓐 := 𝓑) G where
  vertex x := ModuleData.change e he (S.vertex x)
  edge f := ModuleData.change e he (S.edge f)
  lower f := ModuleData.changeHom e he (S.lower f)
  upper f := ModuleData.changeHom e he (S.upper f)

 theorem coefficientChange_free (S : GradedSheaf (𝓐 := 𝓐) G) (hS : S.FreeStalks) :
    (coefficientChange e he S).FreeStalks := by
  intro x
  let := hS x
  exact ModuleData.change_free e he (S.vertex x)

 theorem coefficientChange_upperQuotient (S : GradedSheaf (𝓐 := 𝓐) G)
    (α : E → A) (hS : S.UpperQuotient α) :
    (coefficientChange e he S).UpperQuotient (fun f => e (α f)) := by
  intro f
  constructor
  · exact CoefficientChange.map_surjective e _ (hS f).1
  · intro m
    constructor
    · intro hm
      have hz : (S.upper f).map m.val=0 := congrArg CoefficientChange.val hm
      obtain ⟨n,hn⟩ := (hS f).2 m.val |>.mp hz
      refine ⟨CoefficientChange.mk n,CoefficientChange.ext ?_⟩
      change m.val=e.symm (e (α f)) • n
      simpa only [e.symm_apply_apply] using hn
    · rintro ⟨n,rfl⟩
      apply CoefficientChange.ext
      change (S.upper f).map (e.symm (e (α f)) • n.val)=0
      rw [e.symm_apply_apply]
      exact ((hS f).2 _).mpr ⟨n.val,rfl⟩

 theorem coefficientChange_flabby (S : GradedSheaf (𝓐 := 𝓐) G) (hS : S.forget.Flabby) :
    (coefficientChange e he S).forget.Flabby := by
  intro U hU f hf
  have hf' : S.forget.CompatibleOn U (fun x => (f x).val) := fun q hs ht =>
    congrArg CoefficientChange.val (hf q hs ht)
  obtain ⟨g,hg,hgf⟩ := hS U hU (fun x => (f x).val) hf'
  refine ⟨fun x => CoefficientChange.mk (g x),?_,?_⟩
  · intro q hs ht
    exact CoefficientChange.ext (hg q hs ht)
  · intro x hx
    exact CoefficientChange.ext (hgf x hx)

 theorem coefficientChange_generated (S : GradedSheaf (𝓐 := 𝓐) G) (hS : S.forget.Generated) :
    (coefficientChange e he S).forget.Generated := by
  intro x m
  obtain ⟨g,hg,hgx⟩ := hS x m.val
  refine ⟨fun x => CoefficientChange.mk (g x),?_,CoefficientChange.ext hgx⟩
  intro q hs ht
  exact CoefficientChange.ext (hg q hs ht)

 def coefficientChangeSections (S : GradedSheaf (𝓐 := 𝓐) G) (U : Set V) :
    CoefficientChange e (S.forget.sections U) ≃ₗ[B] (coefficientChange e he S).forget.sections U where
  toFun m := ⟨fun x => CoefficientChange.mk (m.val.val x),fun q hs ht =>
    CoefficientChange.ext (m.val.property q hs ht)⟩
  invFun m := CoefficientChange.mk ⟨fun x => (m.val x).val,fun q hs ht =>
    congrArg CoefficientChange.val (m.property q hs ht)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! A genuine homogeneous integral perfect pairing with vertex-support
orthogonality on both sides. Transport does not identify unequal lattices. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section

 def PerfectPairing.pullback {S T : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : PerfectPairing T d) (j : Iso S T) : PerfectPairing S d where
  pairing := (j.toIso.sections Set.univ).trans
    (p.pairing.trans (j.toIso.sections Set.univ).dualMap)
  homogeneous i q m n hm hn := p.homogeneous i q _ _
    (fun x => j.vertex_graded x i _ (hm x)) (fun x => j.vertex_graded x q _ (hn x))
  left_orthogonal x m n hm hn := by
    apply p.left_orthogonal x
    · intro y hy
      change j.vertex y (m.val y)=0
      rw [hm y hy,map_zero]
    · change j.vertex x (n.val x)=0
      rw [hn,map_zero]
  right_orthogonal x m n hm hn := by
    apply p.right_orthogonal x
    · change j.vertex x (m.val x)=0
      rw [hm,map_zero]
    · intro y hy
      change j.vertex y (n.val y)=0
      rw [hn y hy,map_zero]

 variable {B : Type ua} [CommRing B] [Algebra k B] {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)

 def PerfectPairing.coefficientChange {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : PerfectPairing S d) : PerfectPairing (coefficientChange e he S) d where
  pairing := (coefficientChangeSections e he S Set.univ).symm.trans
    ((CoefficientChange.pairingEquiv e p.pairing).trans
      (coefficientChangeSections e he S Set.univ).symm.dualMap)
  homogeneous i j m n hm hn := by
    apply (he (i+j-d) _).mp
    exact p.homogeneous i j _ _
      (fun x => (ModuleData.mem_changePiece e (S.vertex x) i (m.val x)).mp (hm x))
      (fun x => (ModuleData.mem_changePiece e (S.vertex x) j (n.val x)).mp (hn x))
  left_orthogonal x m n hm hn := by
    change e (p.pairing _ _)=0
    apply (congrArg e ?_).trans (map_zero e)
    apply p.left_orthogonal x
    · intro y hy
      exact congrArg (fun v : CoefficientChange e (S.vertex y) => v.val) (hm y hy)
    · exact congrArg (fun v : CoefficientChange e (S.vertex x) => v.val) hn
  right_orthogonal x m n hm hn := by
    change e (p.pairing _ _)=0
    apply (congrArg e ?_).trans (map_zero e)
    apply p.right_orthogonal x
    · exact congrArg (fun v : CoefficientChange e (S.vertex x) => v.val) hm
    · intro y hy
      exact congrArg (fun v : CoefficientChange e (S.vertex y) => v.val) (hn y hy)

end
end KLInvariance.MomentGraph.GradedSheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section

/-! Recognition by the actual minimal-boundary object, not by an asserted
character or by restricting a perfect form to an arbitrary summand. -/
namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] {hneg : ∀ n < 0, 𝓐 n=⊥}
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E} {α : E → A} {b : V}
  (B : BoundarySheaf hneg G α b)
noncomputable section

 theorem top_nontrivial : Nontrivial (B.sheaf.vertex b) := by
  let e := ModuleData.equivOfEq B.top
  let z : ModuleData.unit.{uk,ua,um} hneg := fun _ => (0 : A)
  let o : ModuleData.unit.{uk,ua,um} hneg := fun _ => (1 : A)
  refine ⟨⟨e.symm z,e.symm o,?_⟩⟩
  intro h
  exact zero_ne_one (congrFun (e.symm.injective h) PUnit.unit)

 variable [IsNoetherianRing A] [Fintype V] [Fintype E]

 theorem iso_of_primitive_top_split
    (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c=a)
    (hb : ∀ x, x≤b) (C : GradedSheaf (𝓐 := 𝓐) G)
    (hCq : C.UpperQuotient α) (hCfree : ∀ x, Module.Free A (C.vertex x))
    (hCf : C.forget.Flabby) (hCg : C.forget.Generated)
    (hCp : (GradedSheaf.Hom.id C).PrimitiveProjector)
    (i : ModuleData.Hom (B.sheaf.vertex b) (C.vertex b))
    (p : ModuleData.Hom (C.vertex b) (B.sheaf.vertex b))
    (hpi : ∀ v, p.map (i.map v)=v) : Nonempty (GradedSheaf.Iso B.sheaf C) := by
  let := B.top_nontrivial
  obtain ⟨s⟩ := B.splitIn_of_top_split hzero hb C hCq hCfree hCf hCg i p hpi
  exact ⟨s.isoOfPrimitive hCp b⟩

end
end KLInvariance.MomentGraph.BoundarySheaf

end


section

/-! The same genuine minimal boundary construction over the symmetric
coefficient algebra. Its polynomial-coordinate comparison is proved separately. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 omit [Fintype σ] in
 theorem symmetric_scalar_mod_positive (a : SymmetricCoefficient (M := M)) :
    ∃ c : ℝ, a-algebraMap ℝ (SymmetricCoefficient (M := M)) c ∈ positiveIdeal (symmetricGrading basis) := by
  obtain ⟨c,hc⟩ := symmetricGrading_zero basis _
    (DirectSum.decompose (symmetricGrading basis) a 0).property
  refine ⟨c,?_⟩
  rw [positiveIdeal_eq_augmentation_ker _ (symmetricGrading_negative basis)]
  change component (symmetricGrading basis) 0 (a-algebraMap ℝ (SymmetricCoefficient (M := M)) c)=0
  rw [map_sub,hc]
  rw [show component (symmetricGrading basis) 0
    (DirectSum.decompose (symmetricGrading basis) a 0 : SymmetricCoefficient (M := M)) =
    (DirectSum.decompose (symmetricGrading basis) a 0 : SymmetricCoefficient (M := M)) from
    DirectSum.decompose_of_mem_same _ (DirectSum.decompose (symmetricGrading basis) a 0).property]
  exact sub_self _

 theorem symmetricLabel_homogeneous (u b : W) (e : Edge cs u b) :
    symmetricLabel cs u b e ∈ symmetricGrading basis 1 :=
  (mem_symmetricGrading basis 1 _).mpr (polynomialLabel_homogeneous cs u b basis e)

 theorem exists_symmetricBoundarySheaf (b : W) :
    Nonempty (BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 b) (symmetricLabel cs 1 b) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩) := by
  classical
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 b
  let := Fintype.ofFinite (Interval cs 1 b)
  let := Fintype.ofFinite (Edge cs 1 b)
  exact MomentGraph.exists_boundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 b) (symmetric_scalar_mod_positive basis)
    ⟨b,one_bruhat cs b,bruhat_refl cs b⟩ (fun x => x.property.2)
    (symmetricLabel cs 1 b) (symmetricLabel_homogeneous cs basis 1 b)

 def symmetricBoundarySheaf (b : W) :
    BoundarySheaf (symmetricGrading_negative basis)
      (graph cs 1 b) (symmetricLabel cs 1 b) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩ :=
  (exists_symmetricBoundarySheaf cs basis b).some

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
noncomputable section

 def unchangeHom {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom (change e he M) (change e he N)) :
    Hom M N where
  map :=
    { toFun m := (f.map (CoefficientChange.mk m)).val
      map_add' m n := congrArg CoefficientChange.val (map_add f.map (CoefficientChange.mk m) (CoefficientChange.mk n))
      map_smul' a m := by
        have hh := congrArg CoefficientChange.val (map_smul f.map (e a) (CoefficientChange.mk m))
        change (f.map (CoefficientChange.mk (e.symm (e a) • m))).val=
          e.symm (e a) • (f.map (CoefficientChange.mk m)).val at hh
        simpa only [e.symm_apply_apply, RingHom.id_apply] using hh }
  graded n m hm := (mem_changePiece e N n _).mp
    (f.graded n (CoefficientChange.mk m) ((mem_changePiece e M n _).mpr hm))

end
end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 def Hom.coefficientUnchange {S T : GradedSheaf (𝓐 := 𝓐) G}
    (g : Hom (GradedSheaf.coefficientChange e he S) (GradedSheaf.coefficientChange e he T)) : Hom S T where
  vertex x := ModuleData.unchangeHom e he (g.vertex x)
  edge f := ModuleData.unchangeHom e he (g.edge f)
  lower f m := congrArg CoefficientChange.val (g.lower f (CoefficientChange.mk m))
  upper f m := congrArg CoefficientChange.val (g.upper f (CoefficientChange.mk m))

 theorem coefficientChange_primitive (S : GradedSheaf (𝓐 := 𝓐) G)
    (hS : (Hom.id S).PrimitiveProjector) :
    (Hom.id (GradedSheaf.coefficientChange e he S)).PrimitiveProjector := by
  constructor
  · apply Hom.eq_of_maps <;> intros <;> rfl
  · intro f hf _ _
    let g : Hom S S := f.coefficientUnchange e he
    have hg : g.comp g=g := by
      apply Hom.eq_of_maps
      · intro x m
        exact congrArg (fun q : Hom (GradedSheaf.coefficientChange e he S) (GradedSheaf.coefficientChange e he S) =>
          ((q.vertex x).map (CoefficientChange.mk m)).val) hf
      · intro x m
        exact congrArg (fun q : Hom (GradedSheaf.coefficientChange e he S) (GradedSheaf.coefficientChange e he S) =>
          ((q.edge x).map (CoefficientChange.mk m)).val) hf
    have hgL : g.comp (Hom.id S)=g := by apply Hom.eq_of_maps <;> intros <;> rfl
    have hgR : (Hom.id S).comp g=g := by apply Hom.eq_of_maps <;> intros <;> rfl
    rcases hS.2 g hg hgL hgR with hz | hi
    · left
      apply Hom.eq_of_maps
      · intro x m
        apply CoefficientChange.ext
        exact congrArg (fun q : Hom S S => (q.vertex x).map m.val) hz
      · intro x m
        apply CoefficientChange.ext
        exact congrArg (fun q : Hom S S => (q.edge x).map m.val) hz
    · right
      apply Hom.eq_of_maps
      · intro x m
        apply CoefficientChange.ext
        exact congrArg (fun q : Hom S S => (q.vertex x).map m.val) hi
      · intro x m
        apply CoefficientChange.ext
        exact congrArg (fun q : Hom S S => (q.edge x).map m.val) hi

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.BoundarySheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [DirectSum.Decomposition 𝓑] [SetLike.GradedMonoid 𝓑]
  [IsDomain A] [IsDomain B] [IsNoetherianRing B]
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  {hA : ∀ n<0,𝓐 n=⊥} {hB : ∀ n<0,𝓑 n=⊥}
  {V E : Type um} [PartialOrder V] [Fintype V] [Fintype E]
  {G : OrderedGraph V E} {α : E → A} {b : V}
  (S : BoundarySheaf hA G α b) (T : BoundarySheaf hB G (fun q => e (α q)) b)
noncomputable section

 theorem iso_coefficientChange
    (hzero : ∀ a ∈ 𝓑 0, ∃ c : k, algebraMap k B c=a)
    (hb : ∀ x, x≤b) : Nonempty
      (GradedSheaf.Iso T.sheaf (GradedSheaf.coefficientChange e he S.sheaf)) := by
  exact T.iso_of_primitive_top_split hzero hb (GradedSheaf.coefficientChange e he S.sheaf)
    (GradedSheaf.coefficientChange_upperQuotient e he S.sheaf α S.quotient)
    (GradedSheaf.coefficientChange_free e he S.sheaf S.free)
    (GradedSheaf.coefficientChange_flabby e he S.sheaf S.flabby.flabby)
    (GradedSheaf.coefficientChange_generated e he S.sheaf S.generated)
    (GradedSheaf.coefficientChange_primitive e he S.sheaf S.primitive_identity)
    (ModuleData.changeTopInclusion e he S.top T.top)
    (ModuleData.changeTopProjection e he S.top T.top)
    (ModuleData.changeTop_split e he S.top T.top)

end
end KLInvariance.MomentGraph.BoundarySheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DihedralIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Signed dihedral coordinates, actual dihedral intervals, exact later-edge counts and root-plane calculations.
-/


section

namespace KLInvariance.TitsSpace
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

 def ambientAfterIndicator (x : W) (α : PositiveRoot M cs) (z : W) : ℕ := by
  classical
  exact if h : BruhatStep cs x z then
    if geometricSlope α < geometricSlope (graphRoot h) then 1 else 0
  else 0

end
end KLInvariance.TitsSpace

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
open _root_.OAI.KLInvariance.Graded Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section

 structure SymmetricPerfectPairing (S : GradedSheaf (𝓐 := 𝓐) G) (d : ℤ)
    extends PerfectPairing S d where
  symmetric : ∀ m n, pairing m n=pairing n m

 def SymmetricPerfectPairing.pullback {S T : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : SymmetricPerfectPairing T d) (j : Iso S T) : SymmetricPerfectPairing S d where
  toPerfectPairing := p.toPerfectPairing.pullback j
  symmetric _m _n := p.symmetric _ _

 variable {B : Type ua} [CommRing B] [Algebra k B] {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)

 def SymmetricPerfectPairing.coefficientChange {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ}
    (p : SymmetricPerfectPairing S d) : SymmetricPerfectPairing (coefficientChange e he S) d where
  toPerfectPairing := p.toPerfectPairing.coefficientChange e he
  symmetric _m _n := congrArg e (p.symmetric _ _)

end
end KLInvariance.MomentGraph.GradedSheaf

end


end OAI
end


