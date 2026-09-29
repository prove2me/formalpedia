-- Prove2me | Definitions.Def_GroupCohomology_TateDimensionShiftMaps
-- name    : GroupCohomology_TateDimensionShiftMaps
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/6230fe33-c3c7-5235-8a73-9e962e0918fb
-- title:
--   Functoriality of the Tate dimension-shift short complex
-- statement:
--   Throughout, $k$ is a commutative ring and $G$ a group, and for $A \in \mathrm{Rep}\,k\,G$ one writes $A_* = \mathrm{indBot}\,A$ for the representation obtained by inducing along $\bot \hookrightarrow G$ the restriction of $A$ to the trivial subgroup, $\pi_A : A_* \to A$ for the map [`Rep.indBotπ`](../def/GroupCohomology_TateDimensionShift.html#L27) coming from the adjunction $\mathrm{Ind} \dashv \mathrm{Res}$, and $A'' = \mathrm{dimShiftDownObj}\,A$ for the subrepresentation $\ker \pi_A$ of $A_*$; [`Rep.dimShiftDown A`](../def/GroupCohomology_TateDimensionShift.html#L42) is the short complex $A'' \to A_* \to A$ with maps the inclusion and $\pi_A$. This module makes these constructions functorial. For $\varphi : A \to B$, [`Rep.indBotMap`](../def/GroupCohomology_TateDimensionShiftMaps.html#L17) is $\varphi_* : A_* \to B_*$, the image under `Rep.indMap` along $\bot \hookrightarrow G$ of the restriction of $\varphi$; [`Rep.indBotMap_comp_indBotπ`](../def/GroupCohomology_TateDimensionShiftMaps.html#L20) is the naturality square $\pi_B \circ \varphi_* = \varphi \circ \pi_A$, obtained from naturality of the adjunction. Consequently $\varphi_*$ carries $\ker \pi_A$ into $\ker \pi_B$, and [`Rep.dimShiftDownObjMap`](../def/GroupCohomology_TateDimensionShiftMaps.html#L36) is the resulting $G$-equivariant map $\varphi'' : A'' \to B''$, whose underlying map is recorded as the restriction of $\varphi_*$; [`Rep.dimShiftDownMap`](../def/GroupCohomology_TateDimensionShiftMaps.html#L49) assembles $(\varphi'', \varphi_*, \varphi)$ into a morphism of short complexes $\mathrm{dimShiftDown}\,A \to \mathrm{dimShiftDown}\,B$.
--
--   The remaining definitions apply these constructions to a short complex $X = (X_1 \to X_2 \to X_3)$ of representations: [`Rep.indBotSC X`](../def/GroupCohomology_TateDimensionShiftMaps.html#L56) is the short complex $(X_1)_* \to (X_2)_* \to (X_3)_*$ and [`Rep.dimShiftDownSC X`](../def/GroupCohomology_TateDimensionShiftMaps.html#L62) is $X_1'' \to X_2'' \to X_3''$, the composites vanishing by functoriality. Finally [`Rep.dimShiftDownSCι`](../def/GroupCohomology_TateDimensionShiftMaps.html#L69) is the morphism $\mathrm{dimShiftDownSC}\,X \to \mathrm{indBotSC}\,X$ given in each spot by the kernel inclusion, and [`Rep.indBotSCπ`](../def/GroupCohomology_TateDimensionShiftMaps.html#L76) the morphism $\mathrm{indBotSC}\,X \to X$ given by the augmentations $\pi_{X_i}$; together they form the three-by-three diagram whose $i$-th column is $0 \to X_i'' \to (X_i)_* \to X_i \to 0$. Only data and the one naturality identity needed to restrict to kernels are provided here; exactness statements are not part of this module.
--
--   **Relation to Mathlib.** Built on Mathlib's `Rep.ind`, `Rep.res`, `Rep.indMap`, the adjunction `Rep.indResAdjunction` and `CategoryTheory.ShortComplex`; the dimension-shift short complex [`Rep.dimShiftDown`](../def/GroupCohomology_TateDimensionShift.html#L42) and its functoriality in the representation, as set up here, are the project's own.
--
--   **Where it is used.** These maps supply the functoriality of the dimension-shifting sequence used to extend Tate cohomology and its cup products to non-positive degrees, and to compare the connecting maps of a short exact sequence of representations with those of its shifted sequences, within the group-cohomology infrastructure of the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_TateDimensionShiftMaps.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology
import Definitions.Def_GroupCohomology_TateDimensionShift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

noncomputable section

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

abbrev indBotMap {A B : Rep.{u} k G} (φ : A ⟶ B) : A.indBot ⟶ B.indBot :=
  Rep.indMap (⊥ : Subgroup G).subtype ((Rep.resFunctor (⊥ : Subgroup G).subtype).map φ)

lemma indBotMap_comp_indBotπ {A B : Rep.{u} k G} (φ : A ⟶ B) : indBotMap φ ≫ indBotπ B = indBotπ A ≫ φ := by
  let adj := Rep.indResAdjunction k (⊥ : Subgroup G).subtype
  have hadj : ∀ (X : Rep.{u} k (⊥ : Subgroup G)) (Y : Rep.{u} k G) (f : Rep.ind (⊥ : Subgroup G).subtype X ⟶ Y),
      adj.homEquiv X Y f = Rep.indResHomEquiv (⊥ : Subgroup G).subtype X Y f := fun X Y f => rfl
  have hπ : ∀ (X : Rep.{u} k G), indBotπ X = (adj.homEquiv _ _).symm (𝟙 _) := fun X => by
    apply (adj.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, hadj]
    exact (Rep.indResHomEquiv (⊥ : Subgroup G).subtype ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj X) X).apply_symm_apply (𝟙 _)
  have e1 := adj.homEquiv_naturality_left_symm ((Rep.resFunctor (⊥ : Subgroup G).subtype).map φ)
    (𝟙 ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj B))
  have e2 := adj.homEquiv_naturality_right_symm (𝟙 ((Rep.resFunctor (⊥ : Subgroup G).subtype).obj A)) φ
  rw [Category.comp_id] at e1
  rw [Category.id_comp] at e2
  rw [hπ A, hπ B]
  exact e1.symm.trans e2

def dimShiftDownObjMap {A B : Rep.{u} k G} (φ : A ⟶ B) : A.dimShiftDownObj ⟶ B.dimShiftDownObj :=
  Rep.ofHom
    ⟨LinearMap.codRestrict _ ((indBotMap φ).hom.toLinearMap ∘ₗ (LinearMap.ker (indBotπ A).hom.toLinearMap).subtype)
        (fun x => by
          show (indBotπ B).hom ((indBotMap φ).hom (x : A.indBot)) = 0
          rw [← Rep.comp_apply, indBotMap_comp_indBotπ, Rep.comp_apply]
          have hx : (indBotπ A).hom (x : A.indBot) = 0 := x.2
          rw [hx, map_zero]),
      fun g => LinearMap.ext fun x => Subtype.ext (Rep.hom_comm_apply (indBotMap φ) g (x : A.indBot))⟩

@[simp] lemma coe_dimShiftDownObjMap_apply {A B : Rep.{u} k G} (φ : A ⟶ B) (x : A.dimShiftDownObj) :
    ((dimShiftDownObjMap φ).hom x : B.indBot) = (indBotMap φ).hom (x : A.indBot) := rfl

def dimShiftDownMap {A B : Rep.{u} k G} (φ : A ⟶ B) : A.dimShiftDown ⟶ B.dimShiftDown where
  τ₁ := dimShiftDownObjMap φ
  τ₂ := indBotMap φ
  τ₃ := φ
  comm₁₂ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  comm₂₃ := indBotMap_comp_indBotπ φ

def indBotSC (X : ShortComplex (Rep.{u} k G)) : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (indBotMap X.f) (indBotMap X.g) (by
    show (Rep.indFunctor k (⊥ : Subgroup G).subtype).map ((Rep.resFunctor (⊥ : Subgroup G).subtype).map X.f)
        ≫ (Rep.indFunctor k (⊥ : Subgroup G).subtype).map ((Rep.resFunctor (⊥ : Subgroup G).subtype).map X.g) = 0
    rw [← Functor.map_comp, ← Functor.map_comp, X.zero, Functor.map_zero, Functor.map_zero])

def dimShiftDownSC (X : ShortComplex (Rep.{u} k G)) : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (dimShiftDownObjMap X.f) (dimShiftDownObjMap X.g) (by
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => Subtype.ext ?_))
    show (indBotMap X.g).hom ((indBotMap X.f).hom (x : X.X₁.indBot)) = 0
    rw [← Rep.comp_apply, show indBotMap X.f ≫ indBotMap X.g = 0 from (indBotSC X).zero]
    rfl)

def dimShiftDownSCι (X : ShortComplex (Rep.{u} k G)) : dimShiftDownSC X ⟶ indBotSC X where
  τ₁ := X.X₁.dimShiftDown.f
  τ₂ := X.X₂.dimShiftDown.f
  τ₃ := X.X₃.dimShiftDown.f
  comm₁₂ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  comm₂₃ := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

def indBotSCπ (X : ShortComplex (Rep.{u} k G)) : indBotSC X ⟶ X where
  τ₁ := indBotπ X.X₁
  τ₂ := indBotπ X.X₂
  τ₃ := indBotπ X.X₃
  comm₁₂ := (indBotMap_comp_indBotπ X.f).symm
  comm₂₃ := (indBotMap_comp_indBotπ X.g).symm

end Rep

end


