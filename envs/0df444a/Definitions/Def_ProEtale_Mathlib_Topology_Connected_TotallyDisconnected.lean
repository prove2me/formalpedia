-- Prove2me | Definitions.Def_ProEtale_Mathlib_Topology_Connected_TotallyDisconnected
-- name    : ProEtale_Mathlib_Topology_Connected_TotallyDisconnected
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:02.80628+00:00
-- url     : https://prove2.me/theorems/874150a4-d502-5460-a1a6-039d6fd87a98
-- title:
--   Connected components: specialization, fibrewise criteria, products, clopen images, and limits of totally disconnected spaces
-- statement:
--   For a topological space $X$, let $\pi_0(X)$ denote its space of connected components with the quotient topology, and let $X \to \pi_0(X)$, $x \mapsto [x]$, be the quotient map.
--
--   Principal results:
--
--   1. If $a$ specializes to $b$ ($b \in \overline{\{a\}}$), then $a$ and $b$ lie in the same connected component. The preimage in $X$ of any subset of $\pi_0(X)$ is the union of the connected components of its points.
--   2. Let $f\colon X \to Y$ be continuous with $Y$ totally disconnected and every fibre $f^{-1}(y)$ preconnected. Then the induced map $\pi_0(X) \to Y$ is injective.
--   3. The image in $\pi_0(X)$ of a clopen subset of $X$ is clopen.
--   4. For spaces $S, T$ and points $s, t$, the connected component of $(s,t)$ in $S \times T$ is the product of the connected components of $s$ and $t$. Consequently, the natural map $\pi_0(S \times T) \to \pi_0(S) \times \pi_0(T)$ is a bijection, and it is a homeomorphism when $S$ is discrete.
--   5. A totally disconnected space $S$ is homeomorphic to $\pi_0(S)$ via the quotient map.
--   6. The limit, computed by the standard limit cone in $\mathsf{Top}$, of a small diagram of totally disconnected spaces is totally disconnected.
--
--   These topological facts are used to study the profinite spaces $\pi_0(\operatorname{Spec} A)$ attached to rings, notably for w-local rings and their connected components.
--
--   **Formalization Note** The declarations are `Specializes.connectedComponents_mk_eq`, `ConnectedComponents.iUnion_connectedComponent_preimage_mk`, `Continuous.connectedComponentsLift_injective`, `IsClopen.connectedComponents_image_isClopen`, `connectedComponent.prod`, `ConnectedComponents.bijective_connectedComponentsLift_prod`, `ConnectedComponents.isHomeomorph_connectedComponentsLift_prod`, the homeomorphism `ConnectedComponents.prodMap` (for discrete $S$), `ConnectedComponents.mkHomeomorph` and the instance `TopCat.limitCone_pt_totallyDisconnectedSpace` (diagram `J ⥤ TopCat.{max v u}` with `J : Type v` small). The source docstring notes that for general $S$ the bijection $\pi_0(S\times T) \to \pi_0(S)\times\pi_0(T)$ need not be open.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Topology/Connected/TotallyDisconnected.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Inseparable

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
variable {X : Type*} [TopologicalSpace X]

/-- A specialization induces equality of connected components. -/
lemma Specializes.connectedComponents_mk_eq {a b : X} (hab : a ⤳ b) :
    ConnectedComponents.mk a = ConnectedComponents.mk b :=
  ConnectedComponents.coe_eq_coe.mpr <| connectedComponent_eq <|
    isConnected_singleton.closure.subset_connectedComponent
      (subset_closure rfl) hab.mem_closure

/-- Any preimage under `ConnectedComponents.mk` is a union of connected components. -/
lemma ConnectedComponents.iUnion_connectedComponent_preimage_mk
    (T : Set (ConnectedComponents X)) :
    ⋃ x ∈ (ConnectedComponents.mk ⁻¹' T : Set X), connectedComponent x =
      ConnectedComponents.mk ⁻¹' T := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
  refine ⟨?_, fun hx ↦ ⟨x, hx, mem_connectedComponent⟩⟩
  rintro ⟨y, hy, hxy⟩
  exact (ConnectedComponents.coe_eq_coe'.mpr hxy) ▸ hy

-- add `@[stacks 0906]` to `ConnectedComponents.totallyDisconnectedSpace`

-- after `IsPreconnected.eqOn_const_of_mapsTo` if the proof need some lemma of the form
-- `IsPreconnected.foo`
-- `by copilot`
theorem Continuous.connectedComponentsLift_injective {X : Type*} [TopologicalSpace X]
    {Y : Type*} [TopologicalSpace Y] [TotallyDisconnectedSpace Y] {f : X → Y} (hf : Continuous f)
    (h : ∀ y : Y, IsPreconnected (f ⁻¹' {y})) :
    Function.Injective (hf.connectedComponentsLift) := by
  intro a b hEq
  set g := hf.connectedComponentsLift
  have hEq' : g a = g b := hEq
  let y := g a
  have hgb : g b = y := by simpa [y] using hEq'.symm
  -- Consider the fiber t = g ⁻¹' {y}.
  let t : Set (ConnectedComponents X) := g ⁻¹' {y}
  -- We show t is preconnected by identifying it with the image of a preconnected set under the
  -- projection.
  have h_apply_coe : ∀ x : X, g (((↑) : X → ConnectedComponents X) x) = f x := by
    intro x'
    simp [g]
  have ht_eq_image : t = ((↑) : X → ConnectedComponents X) '' (f ⁻¹' {y}) := by
    ext z; constructor
    · intro hz
      have hz' : g z = y := by
        simpa [t, Set.mem_preimage, Set.mem_singleton_iff] using hz
      rcases Quot.exists_rep z with ⟨x', rfl⟩
      have hx' : f x' = y := (h_apply_coe x').symm.trans hz'
      exact ⟨x', by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx', rfl⟩
    · rintro ⟨x', hx', rfl⟩
      have hx'y : f x' = y := by
        simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx'
      have : g (((↑) : X → ConnectedComponents X) x') = y := by
        simp [h_apply_coe x', hx'y]
      simpa [t, Set.mem_preimage, Set.mem_singleton_iff]
  have ht_pre : IsPreconnected t := by
    have : IsPreconnected (((↑) : X → ConnectedComponents X) '' (f ⁻¹' {y})) :=
      IsPreconnected.image (H := h y)
        (f := ((↑) : X → ConnectedComponents X))
        (hf := ConnectedComponents.continuous_coe.continuousOn)
    simpa [ht_eq_image] using this
  have ha : a ∈ t := by
    simp [t, y]
  have hb : b ∈ t := by
    simp [t, hgb]
  have hsubset : t ⊆ connectedComponent a :=
    IsPreconnected.subset_connectedComponent (x := a) (s := t) ht_pre ha
  have hb_in : b ∈ connectedComponent a := hsubset hb
  have hsingle :
      connectedComponent a = ({a} : Set (ConnectedComponents X)) :=
    (totallyDisconnectedSpace_iff_connectedComponent_singleton.mp
      (inferInstance : TotallyDisconnectedSpace (ConnectedComponents X))) a
  have : b ∈ ({a} : Set (ConnectedComponents X)) := by simpa [hsingle] using hb_in
  have hba : b = a := by simpa [Set.mem_singleton_iff] using this
  exact hba.symm

theorem IsClopen.connectedComponents_image_isClopen {U : Set X} (hU : IsClopen U) :
    IsClopen ((↑) '' U : Set (ConnectedComponents X)) := by
  rw [← ConnectedComponents.isQuotientMap_coe.isClopen_preimage,
    connectedComponents_preimage_image, hU.biUnion_connectedComponent_eq]
  exact hU

-- end of the file
variable (S T : Type*) [TopologicalSpace S] [TopologicalSpace T]

-- `by copilot`
theorem connectedComponent.prod (s : S) (t : T) :
    connectedComponent (s, t) = connectedComponent s ×ˢ connectedComponent t := by
  apply Set.Subset.antisymm
  · intro p hp
    have hconn : IsConnected (connectedComponent (s, t) : Set (S × T)) :=
      isConnected_connectedComponent
    have hpst : (s, t) ∈ (connectedComponent (s, t) : Set (S × T)) :=
      mem_connectedComponent
    have hfst :
        (Prod.fst '' (connectedComponent (s, t) : Set (S × T))) ⊆ connectedComponent s :=
      (hconn.image _ (continuous_fst.continuousOn)).subset_connectedComponent <| by
        refine ⟨(s, t), ?_, rfl⟩
        simpa using hpst
    have hs' : p.1 ∈ connectedComponent s := by
      have : p.1 ∈ Prod.fst '' (connectedComponent (s, t) : Set (S × T)) :=
        ⟨p, hp, rfl⟩
      exact hfst this
    have hsnd :
        (Prod.snd '' (connectedComponent (s, t) : Set (S × T))) ⊆ connectedComponent t :=
      (hconn.image _ (continuous_snd.continuousOn)).subset_connectedComponent <| by
        refine ⟨(s, t), ?_, rfl⟩
        simpa using hpst
    have ht' : p.2 ∈ connectedComponent t := by
      have : p.2 ∈ Prod.snd '' (connectedComponent (s, t) : Set (S × T)) :=
        ⟨p, hp, rfl⟩
      exact hsnd this
    exact ⟨hs', ht'⟩
  · intro p hp
    have hs : p.1 ∈ connectedComponent s := hp.1
    have ht : p.2 ∈ connectedComponent t := hp.2
    have hconn_prod :
        IsConnected (connectedComponent s ×ˢ connectedComponent t : Set (S × T)) := by
      exact (isConnected_connectedComponent (x := s)).prod (isConnected_connectedComponent (x := t))
    have hmem : (s, t) ∈ (connectedComponent s ×ˢ connectedComponent t : Set (S × T)) := by
      exact ⟨mem_connectedComponent, mem_connectedComponent⟩
    have hsub :
        (connectedComponent s ×ˢ connectedComponent t : Set (S × T)) ⊆ connectedComponent (s, t) :=
      hconn_prod.subset_connectedComponent hmem
    exact hsub ⟨hs, ht⟩

theorem ConnectedComponents.bijective_connectedComponentsLift_prod :
    Function.Bijective (Continuous.connectedComponentsLift
      (f := fun x : S × T ↦ (mk x.1, mk x.2)) (by continuity)) := by
  refine ⟨Continuous.connectedComponentsLift_injective _ ?_, ?_⟩
  · rintro ⟨c, d⟩
    obtain ⟨s, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨t, rfl⟩ := ConnectedComponents.surjective_coe d
    have heq : (fun x : S × T ↦ (ConnectedComponents.mk x.1, ConnectedComponents.mk x.2)) ⁻¹'
        {(ConnectedComponents.mk s, ConnectedComponents.mk t)} =
        connectedComponent s ×ˢ connectedComponent t := by
      ext ⟨s', t'⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
        Set.mem_prod, ConnectedComponents.coe_eq_coe']
    rw [heq]
    exact isPreconnected_connectedComponent.prod isPreconnected_connectedComponent
  · rintro ⟨c, d⟩
    obtain ⟨s, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨t, rfl⟩ := ConnectedComponents.surjective_coe d
    exact ⟨ConnectedComponents.mk (s, t), rfl⟩

/-- If `S` is discrete, `π₀(S × T) ≃ₜ π₀ S × π₀ T`. (For general spaces the bijection need not
be open, since a product of quotient maps need not be a quotient map.) -/
theorem ConnectedComponents.isHomeomorph_connectedComponentsLift_prod [DiscreteTopology S] :
    IsHomeomorph (Continuous.connectedComponentsLift
    (f := fun x : S × T ↦ (mk x.1, mk x.2)) (by continuity)) where
  continuous := Continuous.connectedComponentsLift_continuous (by continuity)
  isOpenMap := by
    intro U hU
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨⟨s, t⟩, rfl⟩ := ConnectedComponents.surjective_coe u
    -- The slice of `U` through `s` is open and saturated, so its image in `π₀ T` is open.
    let W : Set T := {t' | ConnectedComponents.mk ((s, t') : S × T) ∈ U}
    have hWo : IsOpen W := hU.preimage (continuous_coe.comp (Continuous.prodMk_right s))
    have hWsat : ConnectedComponents.mk ⁻¹' (ConnectedComponents.mk '' W) = W := by
      ext t'
      refine ⟨?_, fun ht' ↦ ⟨t', ht', rfl⟩⟩
      rintro ⟨t'', ht'', he⟩
      have hcc : ((s, t'') : S × T) ∈ connectedComponent ((s, t') : S × T) := by
        rw [connectedComponent.prod]
        exact ⟨mem_connectedComponent, ConnectedComponents.coe_eq_coe'.mp he⟩
      change ConnectedComponents.mk ((s, t') : S × T) ∈ U
      rw [← ConnectedComponents.coe_eq_coe'.mpr hcc]
      exact ht''
    have hV : IsOpen (ConnectedComponents.mk '' W : Set (ConnectedComponents T)) :=
      ConnectedComponents.isQuotientMap_coe.isOpen_preimage.mp (by rw [hWsat]; exact hWo)
    have hs : IsOpen ({ConnectedComponents.mk s} : Set (ConnectedComponents S)) :=
      ConnectedComponents.isQuotientMap_coe.isOpen_preimage.mp (isOpen_discrete _)
    refine ⟨{ConnectedComponents.mk s} ×ˢ (ConnectedComponents.mk '' W), ?_, hs.prod hV,
      ⟨rfl, t, hu, rfl⟩⟩
    rintro ⟨a, b⟩ ⟨ha, t', ht', rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact ⟨ConnectedComponents.mk (s, t'), ht', rfl⟩
  bijective := bijective_connectedComponentsLift_prod S T

variable {S T} in
noncomputable def ConnectedComponents.prodMap [DiscreteTopology S] :
    ConnectedComponents (S × T) ≃ₜ ConnectedComponents S × ConnectedComponents T :=
  IsHomeomorph.homeomorph (Continuous.connectedComponentsLift
    (by continuity)) (isHomeomorph_connectedComponentsLift_prod S T)

-- TODO: unbundle this
def ConnectedComponents.mkHomeomorph [TotallyDisconnectedSpace S] : S ≃ₜ ConnectedComponents S where
  toFun := mk
  invFun := continuous_id.connectedComponentsLift
  left_inv := fun _ => rfl
  right_inv := ConnectedComponents.surjective_coe.forall.2 fun _ => rfl
  continuous_toFun := continuous_coe
  continuous_invFun := continuous_id.connectedComponentsLift_continuous

open CategoryTheory CategoryTheory.Limits

universe v u

/-- The inverse limit of a system of totally disconnected topological spaces is
totally disconnected. -/
instance TopCat.limitCone_pt_totallyDisconnectedSpace
    {J : Type v} [SmallCategory J] (F : J ⥤ TopCat.{max v u})
    [∀ j, TotallyDisconnectedSpace (F.obj j)] :
    TotallyDisconnectedSpace (TopCat.limitCone.{v, u} F).pt := by
  change TotallyDisconnectedSpace ({ u : ∀ j : J, F.obj j | _ } : Type _)
  exact Subtype.totallyDisconnectedSpace


