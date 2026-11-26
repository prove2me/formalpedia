-- Prove2me | Definitions.Def_ProEtale_Comparator_Sites
-- name    : ProEtale_Comparator_Sites
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T12:05:44.89737+00:00
-- url     : https://prove2.me/theorems/f4aa02c7-425a-4892-9d56-5c3b2431937e
-- title:
--   Étale-to-pro-étale comparison I: the inclusion of sites and the pullback of sheaves
-- statement:
--   For a scheme $X$, this file constructs from Mathlib alone the functors relating the small étale site $X_{\text{ét}}$ and the pro-étale site $X_{\text{proét}}$.
--
--   1. The inclusion `toProEtale X` $: X_{\text{ét}} \to X_{\text{proét}}$, which regards an étale $X$-scheme as a weakly étale one. It preserves finite limits, is representably flat, and is continuous for the étale and pro-étale topologies.
--   2. The induced functors on sheaves with values in a category $A$: restriction $\nu_*$ (`ProEt.sheafPushforward`), its left adjoint $\nu^*$ (`ProEt.sheafPullback`), and the adjunction $\nu^* \dashv \nu_*$ (`ProEt.sheafAdjunction`).
--   3. For abelian sheaves, the facts that $\nu^*$ preserves finite limits and colimits and is additive, together with the supporting statements that abelian groups satisfy AB5 in the relevant universes and that abelian étale sheaves form a Grothendieck abelian category.
--
--   It is the first of three files that set up the objects in which the $\ell$-adic comparison is stated.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Section 5.1 (the morphism of topoi ν). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Comparator/Definitions.lean (declarations kept unchanged, unused ones removed; part 1 of 3 of that file, which is split to keep compilation short).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Definitions: comparison maps between `ℓ`-adic and étale cohomology

This file provides the definitions shared by the `leanprover/comparator`
challenge/solution pair in this directory (see `Challenge.lean` and `Solution.lean`).
It only imports mathlib.

This file constructs, two canonical comparison maps relating it to the étale
cohomology of the constant sheaves `ℤ/ℓⁿℤ`. The
canonical comparison is the zig-zag

`X.EllAdicCohomology ℓ m ⟶ lim_n Hᵐ(X_proét, ℤ/ℓⁿℤ) ⟵ lim_n Hᵐ(X_ét, ℤ/ℓⁿℤ)`

through the pro-étale cohomology of the sheaves of continuous (equivalently, locally
constant) `ℤ/ℓⁿℤ`-valued functions, defined in exact analogy with mathlib's
`ellAdicSheaf`:

- `EllAdicEtaleComparison.ellAdicCohomologyToLimit`: the first map, induced by the
  reductions `ℤ_[ℓ] → ℤ/ℓⁿℤ` on coefficient sheaves.
- `EllAdicEtaleComparison.etaleToProetaleCohomologySystemHom`: the levelwise second
  map, given by functoriality of `Ext` along the pullback `ν^*` from the small étale
  site to the pro-étale site, together with the canonical comparison morphisms of
  constant sheaves (all obtained from adjunctions).
-/

universe u v w

open CategoryTheory Limits Opposite Abelian AlgebraicGeometry AlgebraicGeometry.Scheme
  MorphismProperty

instance Ab.hasFilteredColimitsOfSize [UnivLE.{u, v}] [UnivLE.{u, w}] [UnivLE.{v, w}] :
    HasFilteredColimitsOfSize.{u, v} Ab.{w} :=
  hasFilteredColimitsOfSize_of_univLE.{u, v, w}

instance Ab.ab5OfSize [UnivLE.{u, v}] [UnivLE.{u, w}] [UnivLE.{v, w}] : AB5OfSize.{u, v} Ab.{w} :=
  AB5OfSize_of_univLE.{u, v, w, w} Ab.{w}

/-- The category of abelian sheaves on the small étale site of `X : Scheme.{u}` (with
coefficients in `Ab.{u + 1}`) is Grothendieck abelian. In particular it has enough
injectives and `Ext`-groups (`HasExt`). -/
instance isGrothendieckAbelianSheafSmallEtaleTopologyAb (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology Ab.{u + 1}) := by
  have : EssentiallySmall.{u + 1} X.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

variable (X : Scheme.{u})

/-! ### The inclusion of the small étale site into the pro-étale site

We equip the inclusion `ν : X.Etale ⥤ X.ProEt` with its continuity and flatness
instances, and record that the associated pullback functor on abelian sheaves is exact.
-/

namespace AlgebraicGeometry.Scheme

/-- The inclusion of the étale site into the pro-étale site. -/
@[simps! obj_toComma]
def toProEtale (S : Scheme.{u}) : S.Etale ⥤ S.ProEt :=
  MorphismProperty.Over.changeProp _ etale_le_weaklyEtale le_rfl

variable (S : Scheme.{u})


instance : HasFiniteLimits S.Etale :=
  inferInstanceAs <| HasFiniteLimits (MorphismProperty.Over @Etale ⊤ S)

instance : PreservesFiniteLimits (toProEtale S) := by
  have : PreservesFiniteLimits (toProEtale S ⋙ ProEt.forget S) :=
    inferInstanceAs <| PreservesFiniteLimits (MorphismProperty.Over.forget @Etale ⊤ S)
  exact preservesFiniteLimits_of_reflects_of_preserves (toProEtale S) (ProEt.forget S)

instance representablyFlat_toProEtale : RepresentablyFlat (toProEtale S) :=
  flat_of_preservesFiniteLimits _

set_option backward.isDefEq.respectTransparency.types false in
private lemma ProEt.topology_eq_restrictedTopology :
    ProEt.topology S = (ProEt.forget S).restrictedTopology (proetaleTopology.over S) :=
  MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology
    _ proetalePrecoverage_le_precoverage_weaklyEtale

/-- The inclusion of the étale site into the pro-étale site is continuous.
(Proof as in leanprover-community/mathlib4#41730.) -/
instance isContinuous_toProEtale :
    (toProEtale S).IsContinuous (smallEtaleTopology S) (ProEt.topology S) := by
  refine Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ (toProEtale S)) ?_
  refine ⟨fun {X R} hR ↦ ?_⟩
  rw [ProEt.topology_eq_restrictedTopology, Functor.mem_restrictedTopology_iff,
    ← Sieve.functorPushforward_comp]
  have hR' : R.functorPushforward (Over.forget @Etale ⊤ S) ∈ etaleTopology.over S _ :=
    Functor.mem_restrictedTopology_iff.mp hR
  exact etaleTopology_le_proetaleTopology _ hR'

namespace ProEt

variable (A : Type*) [Category A]

/-- The direct image functor from pro-étale sheafs to étale sheafs. -/
@[simps! obj_obj]
abbrev sheafPushforward :
    Sheaf (ProEt.topology S) A ⥤ Sheaf (smallEtaleTopology S) A :=
  (toProEtale S).sheafPushforwardContinuous _ _ _

instance (F : S.Etaleᵒᵖ ⥤ Ab.{u + 1}) : (toProEtale S).op.HasPointwiseLeftKanExtension F :=
  inferInstance

/-- The direct image functor from pro-étale sheafs to étale sheafs has a left-adjoint. -/
instance : (ProEt.sheafPushforward S Ab.{u + 1}).IsRightAdjoint := inferInstance

variable [(sheafPushforward S A).IsRightAdjoint]

/-- The inverse image functor from étale sheafs to pro-étale sheafs. -/
noncomputable abbrev sheafPullback :
    Sheaf (smallEtaleTopology S) A ⥤ Sheaf (ProEt.topology S) A :=
  (toProEtale S).sheafPullback _ _ _

/-- The inverse image - direct image adjunction for the pro-étale site. -/
noncomputable abbrev sheafAdjunction :
    ProEt.sheafPullback S A ⊣ ProEt.sheafPushforward S A :=
  (toProEtale S).sheafAdjunctionContinuous _ _ _

end ProEt

end AlgebraicGeometry.Scheme

open AlgebraicGeometry.Scheme ProEt

namespace EllAdicEtaleComparison

section LanEvaluation

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- Variant of `CategoryTheory.Functor.lanEvaluationIsoColim` without the smallness
assumptions on the categories involved. -/
noncomputable def lanEvaluationIsoColim' (F : C ⥤ D) (Y : D)
    [∀ G : C ⥤ E, F.HasPointwiseLeftKanExtension G]
    [HasColimitsOfShape (CostructuredArrow F Y) E] :
    F.lan ⋙ (evaluation D E).obj Y ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F Y) ⋙ colim :=
  NatIso.ofComponents (fun G ↦
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G Y)
      (colimit.isColimit _)) (fun {G₁ G₂} φ ↦ by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ Y).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ E) ↦ IsColimit.comp_coconePointUniqueUpToIso_hom
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G Y) (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

end LanEvaluation

/-- The left Kan extension of abelian presheaves along the inclusion of the étale site
into the pro-étale site is exact, since the inclusion is representably flat. -/
noncomputable instance preservesFiniteLimits_lan :
    PreservesFiniteLimits ((toProEtale X).op.lan :
      (X.Etaleᵒᵖ ⥤ Ab.{u + 1}) ⥤ X.ProEtᵒᵖ ⥤ Ab.{u + 1}) := by
  constructor
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
  intro K
  haveI : IsFiltered (CostructuredArrow (toProEtale X).op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (toProEtale X) (unop K))
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim' (toProEtale X).op K).symm

instance : PreservesFiniteLimits (sheafPullback X Ab) := by
  infer_instance

instance : PreservesColimitsOfSize.{0, 0} (sheafPullback X Ab) :=
  (sheafAdjunction X Ab).leftAdjoint_preservesColimits

instance : PreservesFiniteColimits (sheafPullback X Ab) := by
  infer_instance

instance : (sheafPullback X Ab).Additive := by
  haveI : (sheafPullback X Ab).IsLeftAdjoint := (sheafAdjunction X Ab).isLeftAdjoint
  exact Functor.additive_of_preserves_binary_products _


end EllAdicEtaleComparison


