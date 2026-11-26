-- Prove2me | Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Pullback
-- name    : ProEtale_Topology_SpectralSpace_WLocal_Pullback
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:42:41.271922+00:00
-- url     : https://prove2.me/theorems/0c593ea0-432a-5a98-8f5d-90750c3be40f
-- title:
--   Pullback of a w-local space along a map from a profinite space to its connected components is w-local
-- statement:
--   A topological space is **w-local** if it is spectral, its set of closed points is closed, and every point specializes to a unique closed point. For a space $X$ let $\pi_0(X)$ be its space of connected components with quotient map $X \to \pi_0(X)$.
--
--   Principal results:
--   1. If $A$ is $T_1$ then a point $p \in A \times B$ is closed iff $p_2$ is closed in $B$; hence the closed points of $A \times B$ are exactly the preimage of the closed points of $B$.
--   2. If $T$ is profinite (compact, Hausdorff, totally disconnected) and $X$ is w-local, then $T \times X$ is w-local.
--   3. (Stacks 096C, second part.) Let $X$ be w-local, $T$ profinite, $i : T \to \pi_0(X)$ continuous, and let $Y$ with maps $f : Y \to X$, $g : Y \to T$ form a pullback square
--   $$\begin{array}{ccc} Y & \xrightarrow{g} & T \\ {\scriptstyle f}\downarrow & & \downarrow{\scriptstyle i} \\ X & \longrightarrow & \pi_0(X) \end{array}$$
--   in the category of topological spaces. Then $Y$ is w-local, and $f^{-1}(X^c) = Y^c$, where $X^c$, $Y^c$ denote the sets of closed points. (For the second statement only $T$ Hausdorff is needed.)
--
--   The proof identifies $Y$ with the closed subspace $\{(t,x) : i(t) = [x]\}$ of $T \times X$. These results are used to show that pulling back a w-local affine along a profinite set over its connected components remains w-local, a step in constructing w-contractible covers.
--
--   **Formalization Note** All spaces `X Y T` live in one universe `Type u`; w-locality is the class `WLocalSpace` and closed points are `closedPoints`. Main declarations: `isClosed_singleton_prod_iff`, `closedPoints_prod`, the instance `WLocalSpace.prod`, `ConnectedComponents.wlocalSpace_of_isPullback` and `ConnectedComponents.preimage_closedPoints_eq_closedPoints_of_isPullback`. The pullback hypothesis is an `IsPullback` square in `TopCat` built from `ofHom g`, `ofHom f`, `ofHom i` and the quotient map `ConnectedComponents.mk`. The second theorem omits the compactness and total disconnectedness assumptions on `T`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 096C. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/SpectralSpace/WLocal/Pullback.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Inseparable
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
import Definitions.Def_ProEtale_Mathlib_Topology_Connected_TotallyDisconnected
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_JacobsonSpace
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Hausdorff
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_ConstructibleTopology
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral
import Definitions.Def_ProEtale_Topology_Preliminaries_Profinite
import Definitions.Def_ProEtale_Topology_Preliminaries_Pullback
import Definitions.Def_ProEtale_Topology_SpectralSpace_ConnectedComponent
import Definitions.Def_ProEtale_Topology_SpectralSpace_Constructible
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_Basic_Lib
import Definitions.Def_ProEtale_Topology_SpectralSpace_WLocal_ClosedPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Pullback of w-local spaces

Stacks Project 096C
-/

open CategoryTheory TopCat Topology

universe u
variable {X Y T : Type u} [TopologicalSpace X] [WLocalSpace X] [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]

section Prod

/-- In a product with a `T1` first factor, a singleton is closed iff the singleton of its
second coordinate is closed. -/
lemma isClosed_singleton_prod_iff {A B : Type*} [TopologicalSpace A] [T1Space A]
    [TopologicalSpace B] {p : A × B} :
    IsClosed ({p} : Set (A × B)) ↔ IsClosed ({p.2} : Set B) := by
  constructor
  · intro h
    have hx : ({p.2} : Set B) = (fun b ↦ (p.1, b)) ⁻¹' {p} := by
      ext b
      simp [Prod.ext_iff]
    rw [hx]
    exact h.preimage (by fun_prop)
  · intro h
    rw [← Prod.mk.eta (p := p), ← Set.singleton_prod_singleton]
    exact isClosed_singleton.prod h

/-- In a product with a `T1` first factor, the closed points are exactly the points whose
second coordinate is a closed point. -/
lemma closedPoints_prod {A B : Type*} [TopologicalSpace A] [T1Space A] [TopologicalSpace B] :
    closedPoints (A × B) = Prod.snd ⁻¹' closedPoints B := by
  ext p
  simp only [mem_closedPoints_iff, Set.mem_preimage]
  exact isClosed_singleton_prod_iff

/-- The product of a profinite space and a w-local space is w-local. -/
instance WLocalSpace.prod : WLocalSpace (T × X) where
  toSpectralSpace := inferInstance
  eq_of_specializes {p c c'} hc hc' hpc hpc' := by
    obtain ⟨h1, h2⟩ := specializes_prod.mp hpc
    obtain ⟨h1', h2'⟩ := specializes_prod.mp hpc'
    refine Prod.ext (h1.eq.symm.trans h1'.eq) ?_
    exact WLocalSpace.eq_of_specializes (isClosed_singleton_prod_iff.mp hc)
      (isClosed_singleton_prod_iff.mp hc') h2 h2'
  isClosed_closedPoints := by
    rw [closedPoints_prod]
    exact WLocalSpace.isClosed_closedPoints.preimage continuous_snd

end Prod

namespace ConnectedComponents

omit [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
/-- The defining equation of the fiber product `T ×_{π₀(X)} X` cuts out a closed subset
of `T × X`, since `π₀(X)` is Hausdorff for spectral `X`. -/
private lemma isClosed_pullbackSet (i : C(T, ConnectedComponents X)) :
    IsClosed {p : T × X | i p.1 = mk p.2} :=
  isClosed_eq (i.continuous.comp continuous_fst) (continuous_coe.comp continuous_snd)

omit [WLocalSpace X] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T] in
/-- A pullback of `i : T → π₀(X)` along `X → π₀(X)` is homeomorphic to the explicit
fiber product inside `T × X`, compatibly with the two projections. -/
private lemma exists_homeomorph_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    ∃ e : Y ≃ₜ {p : T × X | i p.1 = mk p.2}, ∀ y, (e y : T × X) = (g y, f y) := by
  classical
  let mkX : C(X, ConnectedComponents X) := ⟨mk, continuous_coe⟩
  let eY : Y ≃ₜ (Limits.pullback (ofHom i) (ofHom mkX) : TopCat) := homeoOfIso pb.isoPullback
  let eS : (Limits.pullback (ofHom i) (ofHom mkX) : TopCat) ≃ₜ
      {p : T × X // i p.1 = (mkX : X → ConnectedComponents X) p.2} :=
    homeoOfIso (TopCat.pullbackIsoProdSubtype (ofHom i) (ofHom mkX))
  refine ⟨eY.trans eS, fun y ↦ ?_⟩
  have h1 : Limits.pullback.fst (ofHom i) (ofHom mkX) (eY y) = g y :=
    ConcreteCategory.congr_hom pb.isoPullback_hom_fst y
  have h2 : Limits.pullback.snd (ofHom i) (ofHom mkX) (eY y) = f y :=
    ConcreteCategory.congr_hom pb.isoPullback_hom_snd y
  have h3 := TopCat.pullbackIsoProdSubtype_hom_apply (f := ofHom i) (g := ofHom mkX) (eY y)
  calc (eS (eY y) : T × X)
      = (Limits.pullback.fst (ofHom i) (ofHom mkX) (eY y),
          Limits.pullback.snd (ofHom i) (ofHom mkX) (eY y)) := congrArg Subtype.val h3
    _ = (g y, f y) := by rw [h1, h2]

@[stacks 096C "second part"]
theorem wlocalSpace_of_isPullback {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    WLocalSpace Y := by
  obtain ⟨e, -⟩ := exists_homeomorph_of_isPullback pb
  have : WLocalSpace {p : T × X | i p.1 = mk p.2} :=
    (isClosed_pullbackSet i).isClosedEmbedding_subtypeVal.wLocalSpace
  exact e.isClosedEmbedding.wLocalSpace

omit [CompactSpace T] [TotallyDisconnectedSpace T] in
@[stacks 096C "second part"]
theorem preimage_closedPoints_eq_closedPoints_of_isPullback {f : C(Y, X)}
    {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    f ⁻¹' (closedPoints X) = closedPoints Y := by
  obtain ⟨e, he⟩ := exists_homeomorph_of_isPullback pb
  have hclosed := isClosed_pullbackSet i
  have h1 : closedPoints {p : T × X | i p.1 = mk p.2} =
      Subtype.val ⁻¹' closedPoints (T × X) :=
    hclosed.isClosedEmbedding_subtypeVal.isEmbedding.closedPoints_eq_preimage
      (Subtype.range_val ▸ hclosed.stableUnderSpecialization)
  have h2 : closedPoints Y = e ⁻¹' closedPoints {p : T × X | i p.1 = mk p.2} :=
    e.isEmbedding.closedPoints_eq_preimage
      (e.surjective.range_eq ▸ fun _ _ _ _ ↦ Set.mem_univ _)
  have hfeq : (f : Y → X) = Prod.snd ∘ Subtype.val ∘ e := by
    funext y
    exact (congrArg Prod.snd (he y)).symm
  rw [h2, h1, closedPoints_prod, ← Set.preimage_comp, ← Set.preimage_comp, ← hfeq]


end ConnectedComponents


