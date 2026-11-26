-- Prove2me | Definitions.Def_ProEtale_Topology_SpectralSpace_ConnectedComponent
-- name    : ProEtale_Topology_SpectralSpace_ConnectedComponent
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:40:37.116809+00:00
-- url     : https://prove2.me/theorems/100b7b10-9ca1-52b9-afa4-1c2ab449c5f5
-- title:
--   Connected components of compact quasi-separated prespectral spaces and pullbacks along the component map
-- statement:
--   A topological space $X$ is *prespectral* if its compact open subsets form a basis of the topology. For $x \in X$ let $C(x)$ be the connected component of $x$, and let $\pi_0(X)$ be the space of connected components with the quotient topology. A space is *profinite* here if it is compact, Hausdorff and totally disconnected.
--
--   Principal results:
--
--   1. If $X$ is prespectral, $B \subseteq X$ is open and $S \cap B$ is compact, then there is a compact open $U \subseteq B$ with $S \cap U = S \cap B$.
--   2. (Stacks 005F) If $X$ is prespectral, compact and quasi-separated, then for every $x$
--   $$\bigcap_{U \text{ clopen},\ x \in U} U = C(x).$$
--   3. (Stacks 04PL) Under the same hypotheses, a subset $T \subseteq X$ is closed and a union of connected components if and only if it is an intersection of clopen subsets.
--   4. If $X$ is compact then $\pi_0(X)$ is compact; if moreover $X$ is quasi-separated and prespectral then $\pi_0(X)$ is Hausdorff (Stacks 0906).
--   5. Let $X$ be any topological space, $T$ a profinite space, $i : T \to \pi_0(X)$ continuous, and let $Y$ with continuous maps $g : Y \to T$ and $f : Y \to X$ form a pullback square (in the category of topological spaces) of $i$ and the quotient map $X \to \pi_0(X)$. Then $g$ is surjective, every fiber $g^{-1}(t)$ is preconnected, and the induced map $\pi_0(Y) \to T$ is bijective.
--   6. Routine lemmas: if $T$ is the union of the components of the points of some set $I$, then $T$ contains the component of each of its points, and the component of a point outside $T$ is disjoint from $T$.
--
--   These facts describe $\pi_0$ of spectral spaces (such as spectra of rings) as a profinite space. They are used to compare connected components along base change to profinite sets, as in the study of w-local spaces.
--
--   **Formalization Note** Main declarations: `exists_subset_isOpen_isCompact_inter_eq_inter_of_prespectralSpace`, `sInter_isClopen_and_mem_eq_connectedComponent`, `isClosed_and_iUnion_connectedComponent_eq_iff`, the instances `compactSpace_connectedComponent` and `t2Space_connectedComponent`, and `ConnectedComponents.surjective_fst_of_isPullback`, `ConnectedComponents.isPreconnected_fiber_of_isPullback`, `ConnectedComponents.lift_bijective_of_isPullback`. In item 3 the family of clopens is a set $J$ of clopen subsets, and an empty $J$ has intersection $X$. The pullback results in item 5 are stated with `IsPullback` in `TopCat` for spaces in a common universe `u`; they need no spectral hypothesis on $X$. Profiniteness is expressed by the classes `CompactSpace`, `T2Space` and `TotallyDisconnectedSpace`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 005F; Stacks Project, Tag 04PL; Stacks Project, Tag 0906. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/SpectralSpace/ConnectedComponent.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Inseparable
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Sober
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.Prespectral
import Definitions.Def_ProEtale_Mathlib_Topology_Category_TopCat_Limits_Pullbacks
import Definitions.Def_ProEtale_Mathlib_Topology_Connected_TotallyDisconnected
import Definitions.Def_ProEtale_Mathlib_Topology_Inseparable
import Definitions.Def_ProEtale_Mathlib_Topology_QuasiSeparated
import Definitions.Def_ProEtale_Mathlib_Topology_Separation_Hausdorff
import Definitions.Def_ProEtale_Mathlib_Topology_Sober
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Basic
import Definitions.Def_ProEtale_Mathlib_Topology_Spectral_Prespectral
import Definitions.Def_ProEtale_Topology_Preliminaries_Profinite
import Definitions.Def_ProEtale_Topology_Preliminaries_Pullback

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Connected Component in Spectral Space

Profiniteness is expressed as [TopologicalSpace X] [CompactSpace X] [T2Space X]
[TotallyDisconnectedSpace X]

-/

universe u

variable {X : Type u} [TopologicalSpace X]

section

open TopologicalSpace

variable [PrespectralSpace X]

lemma exists_subset_isOpen_isCompact_inter_eq_inter_of_prespectralSpace
    (S : Set X) (B : Set X) (hB : IsOpen B) (h2 : IsCompact (S ∩ B)) :
    ∃ U ⊆ B, IsOpen U ∧ IsCompact U ∧ S ∩ U = S ∩ B := by
  obtain ⟨Us, hUs, hUsC⟩ := Opens.isBasis_iff_cover.mp (PrespectralSpace.isBasis_opens X) ⟨B, hB⟩
  have heq := congr($(hUsC).carrier)
  simp only [Opens.carrier_eq_coe, Opens.coe_sSup] at heq
  obtain ⟨t, ht⟩ := h2.elim_finite_subcover (U := fun i : Us ↦ i.1) (fun i ↦ i.1.2) (by simp [heq])
  use ⋃ i ∈ t, i
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    intro i hi
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop,
      exists_and_right] at hi
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    grind
  · exact isOpen_biUnion (fun i hi ↦ i.1.2)
  · exact t.finite_toSet.isCompact_biUnion fun i hi ↦ hUs i.2
  · refine subset_antisymm ?_ (by simpa using ht)
    rw [heq]
    gcongr
    intro i hi
    simp only [Set.iUnion_coe_set, Set.mem_iUnion, SetLike.mem_coe, exists_prop,
      exists_and_right] at hi
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    grind

variable [CompactSpace X] [QuasiSeparatedSpace X]

@[simp, stacks 005F]
theorem sInter_isClopen_and_mem_eq_connectedComponent {x : X} :
    ⋂ (U : {U : Set X // IsClopen U ∧ x ∈ U}), U = connectedComponent x := by
  set S : Set X := ⋂ (U : {U : Set X // IsClopen U ∧ x ∈ U}), U
  have hx : x ∈ S := by simp [S]
  refine subset_antisymm ?_ connectedComponent_subset_iInter_isClopen
  refine IsConnected.subset_connectedComponent ?_ hx
  by_contra h
  simp only [IsConnected, not_and] at h
  have := h ⟨x, by simp [S]⟩
  simp only [IsPreconnected, not_forall] at this
  have : ∃ (U V : Set X), IsOpen U ∧ IsOpen V ∧ IsCompact U ∧
      IsCompact V ∧ (U ∩ V) ∩ S = ∅ ∧ S ⊆ U ∪ V ∧ (U ∩ S).Nonempty ∧ (V ∩ S).Nonempty := by
    obtain ⟨B, C, hB, hC, hBC, hBn, hCn, h⟩ := this
    push Not at h
    have hS : IsClosed S := isClosed_iInter fun U ↦ U.2.1.1
    obtain ⟨U, hUB, hU, hUc, hUSB⟩ :=
        exists_subset_isOpen_isCompact_inter_eq_inter_of_prespectralSpace S B hB <| by
      apply IsClosed.isCompact
      convert IsClosed.sdiff hS hC using 1
      tauto_set
    obtain ⟨V, hVB, hV, hVc, hVSC⟩ :=
        exists_subset_isOpen_isCompact_inter_eq_inter_of_prespectralSpace S C hC <| by
      apply IsClosed.isCompact
      convert IsClosed.sdiff hS hB using 1
      tauto_set
    use U, V, hU, hV, hUc, hVc
    refine ⟨?_, ?_, ?_⟩
    · grind
    · trans (S ∩ U) ∪ (S ∩ V)
      · rw [hUSB, hVSC, ← Set.inter_union_distrib_left]
        simp [hBC]
      · rw [← Set.inter_union_distrib_left]
        exact Set.inter_subset_right
    · rw [U.inter_comm, V.inter_comm, hUSB, hVSC]
      exact ⟨hBn, hCn⟩
  obtain ⟨U, V, hU, hV, hUc, hVc, hUVS, hSUV, hUSn, hVSn⟩ := this
  have : Nonempty {U // IsClopen U ∧ x ∈ U} := ⟨⟨⊤, by simp [isClopen_univ]⟩⟩
  obtain ⟨W, hxW, hW, hUVW⟩ : ∃ W : Set X, x ∈ W ∧ IsClopen W ∧ U ∩ V ∩ W = ∅ := by
    obtain ⟨W, hW⟩ := IsCompact.elim_directed_family_closed
      (IsCompact.inter_of_isOpen hUc hVc hU hV) _ (·.2.1.1) hUVS
      fun i j ↦ ⟨⟨i.1 ∩ j.1, i.2.1.inter j.2.1, i.2.2, j.2.2⟩, by simp⟩
    use W, W.2.2, W.2.1
  obtain ⟨W', hxW', hW', hW'UV⟩ : ∃ W' : Set X, x ∈ W' ∧ IsClopen W' ∧ W' ⊆ U ∪ V := by
    have : (U ∪ V)ᶜ ∩ S = ∅ := by
      rwa [← Set.diff_eq_compl_inter, Set.diff_eq_empty]
    obtain ⟨W', hW'⟩ := IsCompact.elim_directed_family_closed
      ((hU.union hV).isClosed_compl.isCompact) _ (·.2.1.1) this
      fun i j ↦ ⟨⟨i.1 ∩ j.1, i.2.1.inter j.2.1, i.2.2, j.2.2⟩, by simp⟩
    use W', W'.2.2, W'.2.1
    rwa [← Set.diff_eq_empty, Set.diff_eq_compl_inter]
  set WW := W ∩ W'
  have hUWW : IsClopen (U ∩ WW) := by
    refine ⟨?_, hU.inter (hW.2.inter hW'.2)⟩
    convert IsClosed.sdiff (hW.1.inter hW'.1) hV using 1
    unfold WW
    clear * - hUVW hW'UV
    tauto_set
  have hVWW : IsClopen (V ∩ WW) := by
    refine ⟨?_, hV.inter (hW.2.inter hW'.2)⟩
    convert IsClosed.sdiff (hW.1.inter hW'.1) hU using 1
    unfold WW
    clear * - hUVW hW'UV
    tauto_set
  obtain (hxU | hxV) := hSUV hx
  · refine hVSn.elim fun y hy ↦ ?_
    have hS : S ⊆ U ∩ WW := by
      fapply Set.iInter_subset_of_subset
      · exact ⟨_, hUWW, ⟨hxU, ⟨hxW, hxW'⟩⟩⟩
      · rfl
    have : y ∈ U ∩ V ∩ S := by grind
    grind
  · refine hUSn.elim fun y hy ↦ ?_
    have hS : S ⊆ V ∩ WW := by
      fapply Set.iInter_subset_of_subset
      · exact ⟨_, hVWW, ⟨hxV, ⟨hxW, hxW'⟩⟩⟩
      · rfl
    have : y ∈ U ∩ V ∩ S := by grind
    grind

omit [PrespectralSpace X] [CompactSpace X] [QuasiSeparatedSpace X] in
lemma connectedComponent_subset_of_iUnion_eq {T : Set X} {I : Set X}
    (hI : ⋃ x ∈ I, connectedComponent x = T) {z : X} (hz : z ∈ T) :
    connectedComponent z ⊆ T := by
  have hz' : z ∈ ⋃ x ∈ I, connectedComponent x := by simpa [hI] using hz
  rcases Set.mem_iUnion₂.mp hz' with ⟨w, hwI, hzw⟩
  rw [(connectedComponent_eq hzw).symm]
  intro u hu
  simpa [hI] using (Set.mem_iUnion₂.mpr ⟨w, hwI, hu⟩ : u ∈ ⋃ x ∈ I, connectedComponent x)

omit [PrespectralSpace X] [CompactSpace X] [QuasiSeparatedSpace X] in
lemma disjoint_connectedComponent_of_not_mem {T : Set X} {I : Set X}
    (hI : ⋃ x ∈ I, connectedComponent x = T) {x : X} (hx : x ∉ T) :
    Disjoint (connectedComponent x) T :=
  Set.disjoint_left.2 fun z hz hxz => hx <|
    (connectedComponent_subset_of_iUnion_eq hI hxz) <| by
      simpa [(connectedComponent_eq hz).symm] using mem_connectedComponent (x := x)

@[stacks 04PL]
theorem isClosed_and_iUnion_connectedComponent_eq_iff {T : Set X} :
    (IsClosed T ∧ ∃ I : Set X, ⋃ x ∈ I, connectedComponent x = T) ↔
    ∃ J : Set ({U : Set X // IsClopen U}), ⋂ (U : J), U = T := by
  constructor
  · rintro ⟨hT, ⟨I, hI⟩⟩
    refine ⟨{U | T ⊆ U}, Set.Subset.antisymm ?_ ?_⟩
    · intro x hx
      by_contra hxT
      have hdis := disjoint_connectedComponent_of_not_mem hI hxT
      have hcover : T ⊆ ⋃ U : {U : Set X // IsClopen U ∧ x ∈ U}, (U : Set X)ᶜ := by
        intro z hz
        have : z ∉ ⋂ U : {U : Set X // IsClopen U ∧ x ∈ U}, (U : Set X) := by
          rw [sInter_isClopen_and_mem_eq_connectedComponent]
          exact fun hz' => (Set.disjoint_left.mp hdis) hz' hz
        simp only [Set.mem_iInter, not_forall] at this
        exact Set.mem_iUnion.mpr this
      obtain ⟨s, hs⟩ :=
        hT.isCompact.elim_finite_subcover _ (fun U => U.2.1.1.isOpen_compl) hcover
      have hVcl : IsClopen (⋃ U ∈ s, (U : Set X)ᶜ) :=
        Set.Finite.isClopen_biUnion s.finite_toSet fun U _ => U.2.1.compl
      have hxV : x ∈ (⋃ U ∈ s, (U : Set X)ᶜ) := by
        simpa using Set.mem_iInter.1 hx ⟨⟨_, hVcl⟩, hs⟩
      exact absurd hxV (by
        simp only [Set.mem_iUnion]
        rintro ⟨U, hUs, hxU⟩
        exact hxU U.2.2)
    · intro x hx
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_iInter, Subtype.forall]
      intro U hU hTU
      exact hTU hx
  · rintro ⟨J, hJ⟩
    refine ⟨?_, T, Set.Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)⟩
    · have : IsClosed (⋂ U : J, (U : Set X)) := isClosed_iInter fun U => (U.1.2).1
      simpa [hJ] using this
    · rcases Set.mem_iUnion₂.mp hz with ⟨x, hxT, hzx⟩
      have hxInter : x ∈ ⋂ U : J, (U : Set X) := by simpa [hJ] using hxT
      have hzInter : z ∈ ⋂ U : J, (U : Set X) :=
        Set.mem_iInter.2 fun U =>
          (IsClopen.connectedComponent_subset U.1.2 (Set.mem_iInter.1 hxInter U)) hzx
      simpa [hJ] using hzInter
    · exact Set.mem_iUnion₂.mpr ⟨z, hz, mem_connectedComponent⟩

  -- uses `ConnectedComponents.injective_lift`

instance compactSpace_connectedComponent {X : Type u} [TopologicalSpace X] [CompactSpace X] :
    CompactSpace (ConnectedComponents X) where
  isCompact_univ := by
    let f : X → ConnectedComponents X := ConnectedComponents.mk
    have h1 : Continuous f := ConnectedComponents.continuous_coe
    have h2 : Function.Surjective f := ConnectedComponents.surjective_coe
    have h3 : IsCompact (Set.range f) := isCompact_range h1
    simpa [f, ConnectedComponents.range_coe] using h3


@[stacks 0906]
instance t2Space_connectedComponent {X : Type u} [TopologicalSpace X] [CompactSpace X]
    [QuasiSeparatedSpace X] [PrespectralSpace X] : T2Space (ConnectedComponents X) := by
  rw [t2Space_iff]
  intro a b hab
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
  rw [ConnectedComponents.coe_ne_coe] at hab
  have hy : y ∉ connectedComponent x := fun h => hab (connectedComponent_eq h)
  have hy' : ∃ U, IsClopen U ∧ x ∈ U ∧ y ∉ U := by
    by_contra! habs
    apply hy
    rw [← sInter_isClopen_and_mem_eq_connectedComponent]
    exact Set.mem_iInter.mpr fun ⟨U, hU1, hU2⟩ => habs U hU1 hU2
  obtain ⟨U, hU, hxU, hyU⟩ := hy'
  have hU' : IsClopen ((↑) '' U : Set (ConnectedComponents X)) :=
    hU.connectedComponents_image_isClopen
  refine ⟨(↑) '' U, ((↑) '' U)ᶜ, hU'.2, hU'.1.isOpen_compl, Set.mem_image_of_mem _ hxU, ?_,
    disjoint_compl_right⟩
  simp only [Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
  intro z hzU hzy
  apply hyU
  rw [ConnectedComponents.coe_eq_coe'] at hzy
  exact hU.connectedComponent_subset hzU
    (connectedComponent_eq_iff_mem.mp (connectedComponent_eq hzy))

end

section Spectral

variable [SpectralSpace X]

open CategoryTheory TopCat Continuous Limits


omit [SpectralSpace X] in
/-- The first projection of a pullback along the connected components map is surjective. -/
theorem ConnectedComponents.surjective_fst_of_isPullback {Y T : Type u} [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    Function.Surjective g := by
  classical
  let mkX : C(X, ConnectedComponents X) := ⟨mk, continuous_coe⟩
  intro t
  rcases ConnectedComponents.surjective_coe (i t) with ⟨x, hx⟩
  let p : { p : T × X // i p.1 = (mkX : X → ConnectedComponents X) p.2 } :=
    ⟨⟨t, x⟩, hx.symm⟩
  let q : (pullback (ofHom i) (ofHom mkX) : TopCat) :=
    (TopCat.pullbackIsoProdSubtype (ofHom i) (ofHom mkX)).inv p
  refine ⟨pb.isoPullback.inv q, ?_⟩
  have hq : g (pb.isoPullback.inv q) = pullback.fst (ofHom i) (ofHom mkX) q :=
    ConcreteCategory.congr_hom pb.isoPullback_inv_fst q
  have hfst : pullback.fst (ofHom i) (ofHom mkX) q = t := by
    simpa [q] using TopCat.pullbackIsoProdSubtype_inv_fst_apply (ofHom i) (ofHom mkX) p
  simp [hq, hfst]

omit [SpectralSpace X] in
/-- The fibers of the first projection of a pullback along the connected components map are
preconnected. -/
theorem ConnectedComponents.isPreconnected_fiber_of_isPullback {Y T : Type u}
    [TopologicalSpace Y] [TopologicalSpace T] [CompactSpace T] [T2Space T]
    [TotallyDisconnectedSpace T] {f : C(Y, X)} {g : C(Y, T)}
    {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩))
    (t : T) : IsPreconnected ((g : Y → T) ⁻¹' ({t} : Set T)) := by
  classical
  let mkX : C(X, ConnectedComponents X) := ⟨mk, continuous_coe⟩
  -- Transport to the (concrete) pullback.
  let eY : Y ≃ₜ (pullback (ofHom i) (ofHom mkX) : TopCat) := homeoOfIso pb.isoPullback
  let fiberP : Set (pullback (ofHom i) (ofHom mkX) : TopCat) :=
    (pullback.fst (ofHom i) (ofHom mkX)) ⁻¹' ({t} : Set T)
  have hsetY : ((g : Y → T) ⁻¹' ({t} : Set T)) = eY.symm '' fiberP := by
    ext y
    constructor
    · intro hy
      refine ⟨eY y, ?_, by simp⟩
      have hy' : g y = t := by simpa using hy
      have heq : pullback.fst (ofHom i) (ofHom mkX) (eY y) = g y :=
        ConcreteCategory.congr_hom pb.isoPullback_hom_fst y
      simp [fiberP, heq, hy']
    · rintro ⟨q, hq, rfl⟩
      have hgq : g (eY.symm q) = pullback.fst (ofHom i) (ofHom mkX) q :=
        ConcreteCategory.congr_hom pb.isoPullback_inv_fst q
      simpa [hgq, fiberP] using hq
  -- Work in the explicit subtype pullback `S ⊆ T × X`.
  let eS :
      (pullback (ofHom i) (ofHom mkX) : TopCat) ≃ₜ
        { p : T × X // i p.1 = (mkX : X → ConnectedComponents X) p.2 } :=
    homeoOfIso (TopCat.pullbackIsoProdSubtype (ofHom i) (ofHom mkX))
  let FSt : Set { p : T × X // i p.1 = (mkX : X → ConnectedComponents X) p.2 } :=
    { p | (p : T × X).fst = t }
  -- Show `FSt` is preconnected: it is the continuous image of a connected component in `X`.
  have hFSt : IsPreconnected FSt := by
    rcases ConnectedComponents.surjective_coe (i t) with ⟨x0, hx0⟩
    let A : Set X := ((↑) : X → ConnectedComponents X) ⁻¹' ({i t} : Set (ConnectedComponents X))
    have hA : IsPreconnected A := by
      have hA' : A = connectedComponent x0 := by
        simpa [A, hx0] using (connectedComponents_preimage_singleton (α := X) (x := x0))
      simpa [hA'] using (isPreconnected_connectedComponent (x := x0))
    letI : PreconnectedSpace A := (isPreconnected_iff_preconnectedSpace (s := A)).1 hA
    let φ : A → { p : T × X // i p.1 = (mkX : X → ConnectedComponents X) p.2 } :=
      fun ⟨x, hxA⟩ => ⟨⟨t, x⟩, by simpa [mkX, Set.mem_singleton_iff, A] using hxA.symm⟩
    have hφcont : Continuous φ :=
      (continuous_const.prodMk continuous_subtype_val).subtype_mk fun ⟨x, hxA⟩ => by
        simpa [mkX, Set.mem_singleton_iff, A] using hxA.symm
    have hRange : Set.range φ = FSt := by
      ext p
      constructor
      · rintro ⟨x, rfl⟩
        simp [FSt, φ]
      · intro hp
        have hxmem : p.1.2 ∈ A := by
          have h : i p.1.1 = (p.1.2 : ConnectedComponents X) := by simpa [mkX] using p.2
          have hip : i t = i p.1.1 := by simpa using (congrArg i hp).symm
          simp [A, (hip.trans h).symm]
        exact ⟨⟨p.1.2, hxmem⟩, Subtype.ext (Prod.ext hp.symm rfl)⟩
    simpa [hRange, Set.image_univ] using
      isPreconnected_univ.image (f := φ) (hf := hφcont.continuousOn)
  have hfiberP : IsPreconnected fiberP := by
    have hEq : fiberP = eS.symm '' FSt := by
      ext q
      constructor
      · intro hq
        refine ⟨eS q, ?_, by simp⟩
        have hqt : pullback.fst (ofHom i) (ofHom mkX) q = t := by simpa [fiberP] using hq
        have : (eS q : T × X).fst = pullback.fst (ofHom i) (ofHom mkX) q := by
          exact congrArg Prod.fst <| congrArg Subtype.val <|
            TopCat.pullbackIsoProdSubtype_hom_apply (f := ofHom i) (g := ofHom mkX) (x := q)
        simp [FSt, this, hqt]
      · rintro ⟨p, hp, rfl⟩
        have : pullback.fst (ofHom i) (ofHom mkX) (eS.symm p) = (p : T × X).fst := by
          exact TopCat.pullbackIsoProdSubtype_inv_fst_apply (ofHom i) (ofHom mkX) p
        simp [fiberP, this, show (p : T × X).fst = t by simpa [FSt] using hp]
    simpa [hEq] using hFSt.image (f := eS.symm) (hf := eS.symm.continuous.continuousOn)
  simpa [hsetY] using hfiberP.image (f := eY.symm) (hf := eY.symm.continuous.continuousOn)

omit [SpectralSpace X] in
theorem ConnectedComponents.lift_bijective_of_isPullback {Y T : Type u} [TopologicalSpace Y]
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    {f : C(Y, X)} {g : C(Y, T)} {i : C(T, ConnectedComponents X)}
    (pb : IsPullback (ofHom g) (ofHom f) (ofHom i) (ofHom ⟨mk, continuous_coe⟩)) :
    Function.Bijective (connectedComponentsLift g.2) := by
  refine ⟨?_, ?_⟩
  · exact Continuous.connectedComponentsLift_injective g.2
      (ConnectedComponents.isPreconnected_fiber_of_isPullback pb)
  · intro t
    rcases ConnectedComponents.surjective_fst_of_isPullback pb t with ⟨y, rfl⟩
    exact ⟨(y : ConnectedComponents Y), by simp⟩


end Spectral


