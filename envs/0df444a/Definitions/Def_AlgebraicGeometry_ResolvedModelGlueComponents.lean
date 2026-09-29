-- Prove2me | Definitions.Def_AlgebraicGeometry_ResolvedModelGlueComponents
-- name    : AlgebraicGeometry_ResolvedModelGlueComponents
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/0af40b44-e36c-54fc-b90c-27c89be2690d
-- title:
--   Components and chain positions of the glued model
-- statement:
--   Working with a `ChartInput` $C$ over a scheme $X$ with node index set $N$ (nodes $x_n\in U_n$, étale charts $f_n\colon U_n\to S_n$, proper $\rho_n\colon \mathrm{Res}_n\to S_n$, thicknesses $e_n=\mathtt{thick}\,n\ge 1$, and the glued scheme $C.\mathtt{toGlueInput.glued}$ with its open immersions $\iota_{X_0}$, $\iota_{Y_n}$ and structure map $\mathtt{toDR}$ to $X$), this module labels the components of the special fibre and their ideal sheaves. The index type is $\mathtt{Comps}=\mathrm{Fin}\,2\sqcup\coprod_{n}\mathrm{Fin}(e_n-1)$. Given that each residue field map of $f_n$ at $x_n$ is an isomorphism, points $\mathtt{gRes}\,n\,k\in\mathrm{Res}_n$ lying over the vertex $\rho_n^{-1}(f_n(x_n))$, and two points $\xi_0,\xi_1$ of $X$ in the open $X_0$ (the complement of the nodes), $\mathtt{ηG}$ sends $\mathrm{inl}\,j$ to $\iota_{X_0}(\xi_j)$ and $\mathrm{inr}\,(n,k)$ to $\mathtt{exPt}$, i.e. $\iota_{Y_n}$ of the unique point of $Y_n=U_n\times_{S_n}\mathrm{Res}_n$ over $x_n$ with second coordinate $\mathtt{gRes}\,n\,k$. Then $\mathtt{compG}\,v$ is the reduced ideal sheaf datum $\mathtt{vanishingIdeal}$ of the closed set $\overline{\{\mathtt{ηG}\,v\}}$, whose support is exactly that closure. Auxiliary definitions: $\mathtt{ξY}\,n\,j$, the point of $Y_n$ coming from $\xi_j\in U_n\cap X_0$; $\mathtt{chainPos}'\,n\,d$, which is $\mathrm{inl}\,0$ for $d=0$, $\mathrm{inr}(n,d-1)$ for $0<d<e_n$ and $\mathrm{inl}\,1$ for $d\ge e_n$, ordering the chain over the node $n$; $\mathtt{dEnd}\,n\,j\in\mathrm{Fin}\,e_n$, equal to $0$ for $j=0$ and $e_n-1$ for $j=1$; and, for a specialisation $a\rightsquigarrow b$ on a scheme $X$, the ideal $X.\mathtt{v3genPrime}$ of the stalk at $b$ obtained by pulling back the maximal ideal of the stalk at $a$ along the specialisation map, together with the facts that it is proper, contained in the maximal ideal, equal to the image of the prime of $a$ under a germ map on an affine open, and compatible with stalk maps. The accompanying theorems compute supports and their images in $X$, identify $\mathtt{comap}$ of $\mathtt{compG}$ along $\iota_{Y_n}$ with the $\mathtt{comap}$ along $g_n$ of an ideal sheaf on $\mathrm{Res}_n$ with the corresponding support, show that a point lying in the supports of two distinct components is one of the points $\mathtt{edgePt}'\,n\,d$ with the two components being the consecutive chain positions $d$ and $d+1$, exhibit at such a point an affine open on which the sum of the two component ideals generates the maximal ideal of the stalk, and characterise the points $\mathtt{ηG}\,v$ by maximality among specialisations satisfying a transferred predicate.
--
--   **Relation to Mathlib.** Built on Mathlib's `Scheme.IdealSheafData` API (`vanishingIdeal`, `support`, `comap`, `subschemeι`) and on stalks, germs and specialisation maps; the ideal `Scheme.v3genPrime` attached to a specialisation, and all the component bookkeeping, are the project's own.
--
--   **Where it is used.** The declarations here describe the special fibre of the glued scheme produced from chart data: its components are indexed by two strict transforms and, over each node, a chain of exceptional components, with the intersection points and the transversality of consecutive components made explicit. This is part of the geometric construction of a resolved model of a curve used in the modular input to the Fermat argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ResolvedModelGlueComponents.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlueFibre

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 200000

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace V3Glue.ChartInput

open V3Glue.Aux

open V3Glue.Aux.Layer0 TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

abbrev Comps : Type := Fin 2 ⊕ (Σ n : N, Fin (C.thick n - 1))

section eta

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))

  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)

  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

def ηG : C.Comps → C.toGlueInput.glued
  | Sum.inl j => C.toGlueInput.ιX0 ⟨ξ j, hξ j⟩
  | Sum.inr ⟨n, k⟩ => C.exPt n (hRF n) (gRes n k) (hgRes n k)

@[simp] theorem ηG_inl (j : Fin 2) : C.ηG hRF gRes hgRes ξ hξ (Sum.inl j) = C.toGlueInput.ιX0 ⟨ξ j, hξ j⟩ := rfl
@[simp] theorem ηG_inr (n : N) (k : Fin (C.thick n - 1)) :
    C.ηG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩) = C.exPt n (hRF n) (gRes n k) (hgRes n k) := rfl

def compG (v : C.Comps) : C.toGlueInput.glued.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure {C.ηG hRF gRes hgRes ξ hξ v}, isClosed_closure⟩

theorem coe_support_compG (v : C.Comps) :
    ((C.compG hRF gRes hgRes ξ hξ v).support : Set C.toGlueInput.glued) = closure {C.ηG hRF gRes hgRes ξ hξ v} := by
  rw [compG, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl

theorem ηG_mem_support_compG (v : C.Comps) :
    C.ηG hRF gRes hgRes ξ hξ v ∈ ((C.compG hRF gRes hgRes ξ hξ v).support : Set C.toGlueInput.glued) := by
  rw [coe_support_compG]; exact subset_closure rfl

theorem toDR_mem_closure_of_mem_support_compG (v : C.Comps) {y : C.toGlueInput.glued}
    (hy : y ∈ ((C.compG hRF gRes hgRes ξ hξ v).support : Set C.toGlueInput.glued)) :
    C.toGlueInput.toDR y ∈ closure {C.toGlueInput.toDR (C.ηG hRF gRes hgRes ξ hξ v)} := by
  rw [coe_support_compG] at hy
  have h := image_closure_subset_closure_image C.toGlueInput.toDR.continuous (s := {C.ηG hRF gRes hgRes ξ hξ v}) ⟨y, hy, rfl⟩
  rwa [Set.image_singleton] at h

theorem toDR_ηG_inl (j : Fin 2) : C.toGlueInput.toDR (C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)) = ξ j := by
  rw [ηG_inl, ← Scheme.Hom.comp_apply, C.toGlueInput.ιX0_toDR]; rfl

theorem toDR_ηG_inr (n : N) (k : Fin (C.thick n - 1)) :
    C.toGlueInput.toDR (C.ηG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)) = C.x n := by
  rw [ηG_inr, toDR_exPt]

theorem exc_image' (hx : ∀ n, IsClosed ({C.x n} : Set X)) (n : N) (k : Fin (C.thick n - 1)) (y : C.toGlueInput.glued)
    (hy : y ∈ ((C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).support : Set C.toGlueInput.glued)) :
    C.toGlueInput.toDR y = C.x n := by
  rw [coe_support_compG, ηG_inr] at hy
  exact C.toDR_eq_of_mem_closure_exPt n (hRF n) (hx n) _ _ hy

variable (oRes : ∀ n, Fin (C.thick n) → C.Res n) (hoRes : ∀ n d, C.ρ n (oRes n d) = C.vertex n)

theorem edgePt'_mem_support_compG_inr (n : N) (d : Fin (C.thick n)) (k : Fin (C.thick n - 1))
    (hcl : oRes n d ∈ closure ({gRes n k} : Set (C.Res n))) :
    C.edgePt' hRF oRes hoRes n d ∈ ((C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).support : Set C.toGlueInput.glued) := by
  rw [coe_support_compG, ηG_inr]
  exact C.exPt_mem_closure_exPt n (hRF n) _ _ _ _ hcl

def ξY (n : N) (j : Fin 2) (hU : ξ j ∈ C.U n) : C.Y n := C.j n ⟨ξ j, hU, hξ j⟩

theorem ιY_ξY (n : N) (j : Fin 2) (hU : ξ j ∈ C.U n) :
    C.toGlueInput.ιY n (C.ξY ξ hξ n j hU) = C.ηG hRF gRes hgRes ξ hξ (Sum.inl j) := by
  rw [ηG_inl, ξY]
  have h := congrArg (fun φ => φ.base ⟨ξ j, hU, hξ j⟩) (C.toGlueInput.homOfLE_ιX0 n)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
  refine (h.symm.trans ?_)
  congr 1
  exact Subtype.ext (by
    have h2 := congrArg (fun φ => φ.base ⟨ξ j, hU, hξ j⟩) (X.homOfLE_ι (inf_le_right : C.U n ⊓ C.X0 ≤ C.X0))
    simpa using h2)

theorem q_ξY (n : N) (j : Fin 2) (hU : ξ j ∈ C.U n) : C.q n (C.ξY ξ hξ n j hU) = ⟨ξ j, hU⟩ := by
  rw [ξY, ← Scheme.Hom.comp_apply, C.j_q]
  exact Subtype.ext (by
    have h2 := congrArg (fun φ => φ.base ⟨ξ j, hU, hξ j⟩) (X.homOfLE_ι (inf_le_left : C.U n ⊓ C.X0 ≤ C.U n))
    simpa using h2)

theorem edgePt'_mem_support_compG_inl (n : N) (j : Fin 2) (d₀ : Fin (C.thick n))
    (hU : ξ j ∈ C.U n) (hxcl : C.xU n ∈ closure ({⟨ξ j, hU⟩} : Set ↥(C.U n)))
    (hspec : ∀ o o' : C.Res n, C.ρ n o = C.f n ⟨ξ j, hU⟩ → o' ∈ closure ({o} : Set (C.Res n)) →
      C.ρ n o' = C.vertex n → o' = oRes n d₀) :
    C.edgePt' hRF oRes hoRes n d₀ ∈ ((C.compG hRF gRes hgRes ξ hξ (Sum.inl j)).support : Set C.toGlueInput.glued) := by
  rw [coe_support_compG, ← C.ιY_ξY hRF gRes hgRes ξ hξ n j hU]

  suffices h : C.liftY n (hRF n) (oRes n d₀) (hoRes n d₀) ∈ closure ({C.ξY ξ hξ n j hU} : Set (C.Y n)) by
    have h' := image_closure_subset_closure_image (C.toGlueInput.ιY n).continuous (s := {C.ξY ξ hξ n j hU}) ⟨_, h, rfl⟩
    rwa [Set.image_singleton] at h'

  have hqcl : IsClosed ((C.q n).base '' closure ({C.ξY ξ hξ n j hU} : Set (C.Y n))) :=
    (C.q n).isClosedMap _ isClosed_closure
  have hx : C.xU n ∈ (C.q n).base '' closure ({C.ξY ξ hξ n j hU} : Set (C.Y n)) := by
    refine closure_minimal ?_ hqcl hxcl
    intro z hz
    have hz' : z = ⟨ξ j, hU⟩ := hz
    subst hz'
    exact ⟨_, subset_closure rfl, C.q_ξY ξ hξ n j hU⟩
  obtain ⟨y', hy', hqy'⟩ := hx

  haveI := hRF n
  have ho' : C.ρ n ((pullback.snd (C.f n) (C.ρ n)) y') = C.vertex n := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact congrArg _ hqy'
  have hy'eq : y' = C.liftY n (hRF n) _ ho' :=
    (W6.existsUnique_snd_eq_of_apply_eq (C.f n) (C.ρ n) (C.xU n) (C.f_apply_eq_iff n) _ ho').unique rfl
      (C.snd_liftY n (hRF n) _ ho')

  have hgo : C.ρ n ((pullback.snd (C.f n) (C.ρ n)) (C.ξY ξ hξ n j hU)) = C.f n ⟨ξ j, hU⟩ := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact congrArg _ (C.q_ξY ξ hξ n j hU)
  have hcl : (pullback.snd (C.f n) (C.ρ n)) y' ∈
      closure ({(pullback.snd (C.f n) (C.ρ n)) (C.ξY ξ hξ n j hU)} : Set (C.Res n)) := by
    have h := image_closure_subset_closure_image (pullback.snd (C.f n) (C.ρ n)).continuous
      (s := {C.ξY ξ hξ n j hU}) ⟨y', hy', rfl⟩
    rwa [Set.image_singleton] at h
  have ho'eq := hspec _ _ hgo hcl ho'

  have : C.liftY n (hRF n) (oRes n d₀) (hoRes n d₀) = y' := by
    rw [hy'eq]
    congr 1
    exact ho'eq.symm
  rw [this]; exact hy'

end eta

end V3Glue.ChartInput

namespace AlgebraicGeometry.Scheme

theorem Hom.v3_ker_eq_vanishingIdeal_closure_range {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] :
    f.ker = IdealSheafData.vanishingIdeal ⟨closure (Set.range f.base), isClosed_closure⟩ := by
  rw [← IdealSheafData.map_bot, ← Scheme.nilradical_eq_bot (X := X), ← IdealSheafData.vanishingIdeal_top,
    IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  simp [Set.image_univ]

theorem IdealSheafData.v3_comap_eq_vanishingIdeal_of_isReduced {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsReduced (Limits.pullback f I.subschemeι)] :
    I.comap f = IdealSheafData.vanishingIdeal ⟨f.base ⁻¹' (I.support : Set Y), (I.support.isClosed).preimage f.continuous⟩ := by
  rw [IdealSheafData.comap, Hom.v3_ker_eq_vanishingIdeal_closure_range]
  congr 1
  ext1
  change closure (Set.range (Limits.pullback.fst f I.subschemeι).base) = f.base ⁻¹' (I.support : Set Y)
  rw [Pullback.range_fst, IdealSheafData.range_subschemeι, ((I.support.isClosed).preimage f.continuous).closure_eq]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

open V3Glue.Aux

theorem v3_isReduced_pullback_subschemeι_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (I : Y.IdealSheafData) [IsReduced I.subscheme] : IsReduced (Limits.pullback f I.subschemeι) :=
  isReduced_of_isOpenImmersion (Limits.pullback.snd f I.subschemeι)

theorem v3_isReduced_pullback_of_isIso_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (i : Y ⟶ Z) [IsReduced Y]
    [IsIso (Limits.pullback.fst i f)] : IsReduced (Limits.pullback f i) :=
  isReduced_of_isOpenImmersion ((Limits.pullbackSymmetry f i).hom ≫ Limits.pullback.fst i f)

end AlgebraicGeometry

namespace V3Glue.ChartInput

open V3Glue.Aux

open V3Glue.Aux.Layer0 TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section bridge

variable (n : N) (hRF : IsIso ((C.f n).residueFieldMap (C.xU n)))

theorem preimage_g_closure_singleton (o : C.Res n) (ho : C.ρ n o = C.vertex n)
    (hcl : closure ({o} : Set (C.Res n)) ⊆ (C.ρ n).base ⁻¹' {C.vertex n}) :
    (C.g n).base ⁻¹' closure ({o} : Set (C.Res n)) = closure {C.liftY n hRF o ho} := by
  apply le_antisymm
  · intro y hy
    have hv : C.ρ n (C.g n y) = C.vertex n := hcl hy
    have : y = C.liftY n hRF (C.g n y) hv := C.eq_liftY_of_g_eq n hRF _ hv y rfl
    rw [this]
    exact C.liftY_mem_closure_liftY n hRF o _ ho hv hy
  · refine closure_minimal ?_ (isClosed_closure.preimage (C.g n).continuous)
    rw [Set.singleton_subset_iff, Set.mem_preimage]
    have : (C.g n).base (C.liftY n hRF o ho) = o := C.g_liftY n hRF o ho
    rw [this]
    exact subset_closure rfl

theorem preimage_ιY_closure_singleton_exPt (o : C.Res n) (ho : C.ρ n o = C.vertex n) :
    (C.toGlueInput.ιY n).base ⁻¹' closure ({C.exPt n hRF o ho} : Set C.toGlueInput.glued) =
      closure {C.liftY n hRF o ho} := by
  rw [(C.toGlueInput.ιY n).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      (C.toGlueInput.ιY n).continuous, exPt_def]
  congr 1
  ext y
  constructor
  · intro h
    exact (C.toGlueInput.ιY n).isOpenEmbedding.injective h
  · rintro rfl
    exact rfl

omit hRF in

theorem support_subset_preimage_vertex (L : (C.Res n).IdealSheafData)
    (t : L.subscheme ⟶ Spec ((C.S n).residueField (C.vertex n)))
    (ht : L.subschemeι ≫ C.ρ n = t ≫ (C.S n).fromSpecResidueField (C.vertex n)) :
    (L.support : Set (C.Res n)) ⊆ (C.ρ n).base ⁻¹' {C.vertex n} := by
  rw [← Scheme.IdealSheafData.range_subschemeι]
  rintro _ ⟨z, rfl⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff]
  change (L.subschemeι ≫ C.ρ n).base z = C.vertex n
  rw [ht, Scheme.Hom.comp_base, TopCat.comp_app]
  have h : ((C.S n).fromSpecResidueField (C.vertex n)).base (t.base z) ∈
      Set.range ((C.S n).fromSpecResidueField (C.vertex n)).base := Set.mem_range_self _
  rw [Scheme.range_fromSpecResidueField] at h
  simpa using h

theorem comap_ιY_vanishingIdeal_closure_exPt
    (hfib : IsIso ((C.f n).fiberToSpecResidueField (C.vertex n)))
    (o : C.Res n) (ho : C.ρ n o = C.vertex n)
    (L : (C.Res n).IdealSheafData) [IsReduced L.subscheme]
    (t : L.subscheme ⟶ Spec ((C.S n).residueField (C.vertex n)))
    (ht : L.subschemeι ≫ C.ρ n = t ≫ (C.S n).fromSpecResidueField (C.vertex n))
    (hLsupp : (L.support : Set (C.Res n)) = closure {o})
    (hred : IsReduced (Scheme.IdealSheafData.vanishingIdeal
        (⟨closure {C.exPt n hRF o ho}, isClosed_closure⟩ : Closeds C.toGlueInput.glued)).subscheme) :
    (Scheme.IdealSheafData.vanishingIdeal
        (⟨closure {C.exPt n hRF o ho}, isClosed_closure⟩ : Closeds C.toGlueInput.glued)).comap (C.toGlueInput.ιY n) =
      L.comap (C.g n) := by
  haveI : IsIso (pullback.fst L.subschemeι (C.g n)) :=
    W6.isIso_pullback_fst_of_over_point (C.f n) (C.ρ n) (C.xU n) hfib L.subschemeι t ht
  haveI : IsReduced (pullback (C.g n) L.subschemeι) := v3_isReduced_pullback_of_isIso_fst (C.g n) L.subschemeι
  haveI := hred
  haveI := v3_isReduced_pullback_subschemeι_of_isOpenImmersion (C.toGlueInput.ιY n)
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨closure {C.exPt n hRF o ho}, isClosed_closure⟩ : Closeds C.toGlueInput.glued))
  rw [Scheme.IdealSheafData.v3_comap_eq_vanishingIdeal_of_isReduced,
    Scheme.IdealSheafData.v3_comap_eq_vanishingIdeal_of_isReduced]
  congr 1
  ext1
  change (C.toGlueInput.ιY n).base ⁻¹' ((Scheme.IdealSheafData.vanishingIdeal
      (⟨closure {C.exPt n hRF o ho}, isClosed_closure⟩ : Closeds C.toGlueInput.glued)).support : Set _) =
    (C.g n).base ⁻¹' (L.support : Set (C.Res n))
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hLsupp]
  change (C.toGlueInput.ιY n).base ⁻¹' closure {C.exPt n hRF o ho} = _
  rw [C.preimage_ιY_closure_singleton_exPt n hRF o ho,
    C.preimage_g_closure_singleton n hRF o ho (hLsupp ▸ C.support_subset_preimage_vertex n L t ht)]

end bridge

section bridgeComp

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

theorem comap_ιY_compG_inr (n : N) (k : Fin (C.thick n - 1))
    (hfib : IsIso ((C.f n).fiberToSpecResidueField (C.vertex n)))
    (L : (C.Res n).IdealSheafData) [IsReduced L.subscheme]
    (t : L.subscheme ⟶ Spec ((C.S n).residueField (C.vertex n)))
    (ht : L.subschemeι ≫ C.ρ n = t ≫ (C.S n).fromSpecResidueField (C.vertex n))
    (hLsupp : (L.support : Set (C.Res n)) = closure {gRes n k})
    (hred : IsReduced (C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).subscheme) :
    (C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).comap (C.toGlueInput.ιY n) = L.comap (C.g n) :=
  C.comap_ιY_vanishingIdeal_closure_exPt n (hRF n) hfib (gRes n k) (hgRes n k) L t ht hLsupp hred

theorem preimage_ιY_support_compG_inr (n : N) (k : Fin (C.thick n - 1))
    (hcl : closure ({gRes n k} : Set (C.Res n)) ⊆ (C.ρ n).base ⁻¹' {C.vertex n}) :
    (C.toGlueInput.ιY n).base ⁻¹' ((C.compG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)).support : Set C.toGlueInput.glued) =
      (C.g n).base ⁻¹' closure ({gRes n k} : Set (C.Res n)) := by
  rw [coe_support_compG, ηG_inr, C.preimage_ιY_closure_singleton_exPt n (hRF n),
    C.preimage_g_closure_singleton n (hRF n) _ _ hcl]

end bridgeComp

end V3Glue.ChartInput

namespace V3Glue.ChartInput

open V3Glue.Aux

open AlgebraicGeometry TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)
  (hRF : ∀ n, CategoryTheory.IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

theorem not_mem_preimage_of_mem_support_compG {T : Scheme.{0}} (b : C.toGlueInput.glued ⟶ T) (V : T.Opens)
    (v : C.Comps) (hη : C.ηG hRF gRes hgRes ξ hξ v ∉ b ⁻¹ᵁ V)
    (y : C.toGlueInput.glued) (hy : y ∈ ((C.compG hRF gRes hgRes ξ hξ v).support : Set C.toGlueInput.glued)) :
    y ∉ b ⁻¹ᵁ V := by
  rw [coe_support_compG] at hy
  have hcl : IsClosed ((b ⁻¹ᵁ V : C.toGlueInput.glued.Opens) : Set C.toGlueInput.glued)ᶜ :=
    (b ⁻¹ᵁ V).isOpen.isClosed_compl
  exact closure_minimal (Set.singleton_subset_iff.mpr hη) hcl hy

theorem apply_not_mem_of_mem_support_compG {T : Scheme.{0}} (b : C.toGlueInput.glued ⟶ T) (V : T.Opens)
    (v : C.Comps) (hη : b (C.ηG hRF gRes hgRes ξ hξ v) ∉ V)
    (y : C.toGlueInput.glued) (hy : y ∈ ((C.compG hRF gRes hgRes ξ hξ v).support : Set C.toGlueInput.glued)) :
    b y ∉ V :=
  C.not_mem_preimage_of_mem_support_compG hRF gRes hgRes ξ hξ b V v hη y hy

end V3Glue.ChartInput

namespace V3Glue.ChartInput

open V3Glue.Aux

open V3Glue.Aux.Layer0 TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

def chainPos' (n : N) (d : ℕ) : C.Comps :=
  if h0 : d = 0 then Sum.inl 0
  else if h : d < C.thick n then Sum.inr ⟨n, ⟨d - 1, by omega⟩⟩
  else Sum.inl 1

theorem chainPos'_zero (n : N) : C.chainPos' n 0 = Sum.inl 0 := by simp [chainPos']

theorem chainPos'_succ (n : N) (k : Fin (C.thick n - 1)) : C.chainPos' n ((k : ℕ) + 1) = Sum.inr ⟨n, k⟩ := by
  have h1 : (k : ℕ) + 1 < C.thick n := by omega
  simp only [chainPos', Nat.add_one_ne_zero, ↓reduceDIte, h1, Nat.add_sub_cancel, Fin.eta]

theorem chainPos'_of_le (n : N) (d : ℕ) (h : C.thick n ≤ d) : C.chainPos' n d = Sum.inl 1 := by
  have h0 : d ≠ 0 := by have := C.one_le_thick n; omega
  simp [chainPos', h0, not_lt.mpr h]

def dEnd (n : N) (j : Fin 2) : Fin (C.thick n) :=
  ⟨if j = 0 then 0 else C.thick n - 1, by have := C.one_le_thick n; split_ifs <;> omega⟩

@[simp] theorem dEnd_zero (n : N) : ((C.dEnd n 0 : Fin (C.thick n)) : ℕ) = 0 := by simp [dEnd]
@[simp] theorem dEnd_one (n : N) : ((C.dEnd n 1 : Fin (C.thick n)) : ℕ) = C.thick n - 1 := by simp [dEnd]

theorem fin_two_eq_zero_or_one (j : Fin 2) : j = 0 ∨ j = 1 := by fin_cases j <;> simp

theorem mem_of_mem_closure_singleton_of_isOpen {α : Type*} [TopologicalSpace α] {a y : α} {V : Set α}
    (hy : y ∈ closure ({a} : Set α)) (hV : IsOpen V) (hyV : y ∈ V) : a ∈ V := by
  obtain ⟨z, hzV, hz⟩ := mem_closure_iff.mp hy V hV hyV
  rw [Set.mem_singleton_iff] at hz
  exact hz ▸ hzV

section exhaust

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)
  (oRes : ∀ n, Fin (C.thick n) → C.Res n) (hoRes : ∀ n d, C.ρ n (oRes n d) = C.vertex n)

theorem exists_ιY_eq_of_toDR_eq (n : N) (y : C.toGlueInput.glued) (hy : C.toGlueInput.toDR y = C.x n) :
    ∃ y' : C.Y n, C.toGlueInput.ιY n y' = y ∧ C.q n y' = C.xU n := by
  have hmem : y ∈ Set.range (C.toGlueInput.ιY n).base := by
    rw [C.toGlueInput.range_ιY C.hq n, Set.mem_preimage]
    have h : C.toGlueInput.toDR.base y = C.x n := hy
    rw [h]
    exact C.x_mem_U n
  obtain ⟨y', rfl⟩ := hmem
  have h : C.toGlueInput.toDR (C.toGlueInput.ιY n y') = (C.q n y').1 := by
    rw [← Scheme.Hom.comp_apply, C.toGlueInput.ιY_toDR]; rfl
  exact ⟨y', rfl, Subtype.ext (h.symm.trans hy)⟩

theorem ρ_g_eq_vertex_of_q_eq (n : N) (y' : C.Y n) (hq : C.q n y' = C.xU n) : C.ρ n (C.g n y') = C.vertex n := by
  change C.ρ n (pullback.snd (C.f n) (C.ρ n) y') = C.f n (C.xU n)
  rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  exact congrArg _ hq

theorem g_mem_closure_of_ιY_mem_closure_exPt (n : N) (o : C.Res n) (ho : C.ρ n o = C.vertex n) (y' : C.Y n)
    (hy : C.toGlueInput.ιY n y' ∈ closure ({C.exPt n (hRF n) o ho} : Set C.toGlueInput.glued)) :
    C.g n y' ∈ closure ({o} : Set (C.Res n)) := by
  have h1 : y' ∈ closure ({C.liftY n (hRF n) o ho} : Set (C.Y n)) := by
    rw [← C.preimage_ιY_closure_singleton_exPt n (hRF n) o ho]; exact hy
  have h2 := image_closure_subset_closure_image (C.g n).continuous (s := {C.liftY n (hRF n) o ho}) ⟨y', h1, rfl⟩
  rw [Set.image_singleton] at h2
  have h3 : (C.g n).base (C.liftY n (hRF n) o ho) = o := C.g_liftY n (hRF n) o ho
  rw [h3] at h2
  exact h2

theorem ξ_mem_U_of_ιY_mem_closure (n : N) (j : Fin 2) (y' : C.Y n)
    (hy : C.toGlueInput.ιY n y' ∈ closure ({C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)} : Set C.toGlueInput.glued)) :
    ξ j ∈ C.U n := by
  have hopen : IsOpen (Set.range (C.toGlueInput.ιY n).base) := (C.toGlueInput.ιY n).isOpenEmbedding.isOpen_range
  have hmem := mem_of_mem_closure_singleton_of_isOpen hy hopen ⟨y', rfl⟩
  rw [C.toGlueInput.range_ιY C.hq n, Set.mem_preimage] at hmem
  have : C.toGlueInput.toDR.base (C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)) = ξ j := C.toDR_ηG_inl hRF gRes hgRes ξ hξ j
  rw [this] at hmem
  exact hmem

theorem mem_closure_ξY_of_ιY_mem_closure (n : N) (j : Fin 2) (y' : C.Y n) (hU : ξ j ∈ C.U n)
    (hy : C.toGlueInput.ιY n y' ∈ closure ({C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)} : Set C.toGlueInput.glued)) :
    y' ∈ closure ({C.ξY ξ hξ n j hU} : Set (C.Y n)) := by
  rw [← C.ιY_ξY hRF gRes hgRes ξ hξ n j hU] at hy
  have h := (C.toGlueInput.ιY n).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      (C.toGlueInput.ιY n).continuous {C.toGlueInput.ιY n (C.ξY ξ hξ n j hU)}
  have hy' : y' ∈ (C.toGlueInput.ιY n).base ⁻¹' closure {C.toGlueInput.ιY n (C.ξY ξ hξ n j hU)} := hy
  rw [h] at hy'
  have hs : (C.toGlueInput.ιY n).base ⁻¹' ({C.toGlueInput.ιY n (C.ξY ξ hξ n j hU)} : Set C.toGlueInput.glued) =
      {C.ξY ξ hξ n j hU} := by
    ext z
    constructor
    · intro hz
      exact (C.toGlueInput.ιY n).isOpenEmbedding.injective hz
    · rintro rfl
      exact rfl
  rw [hs] at hy'
  exact hy'

theorem eq_liftY_of_mem_closure_ξY (n : N) (j : Fin 2) (hU : ξ j ∈ C.U n) (d₀ : Fin (C.thick n))
    (hspec : ∀ o o' : C.Res n, C.ρ n o = C.f n ⟨ξ j, hU⟩ → o' ∈ closure ({o} : Set (C.Res n)) →
      C.ρ n o' = C.vertex n → o' = oRes n d₀)
    (y' : C.Y n) (hq : C.q n y' = C.xU n) (hy : y' ∈ closure ({C.ξY ξ hξ n j hU} : Set (C.Y n))) :
    y' = C.liftY n (hRF n) (oRes n d₀) (hoRes n d₀) := by
  have ho' := C.ρ_g_eq_vertex_of_q_eq n y' hq
  have hgo : C.ρ n (C.g n (C.ξY ξ hξ n j hU)) = C.f n ⟨ξ j, hU⟩ := by
    change C.ρ n (pullback.snd (C.f n) (C.ρ n) _) = _
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact congrArg _ (C.q_ξY ξ hξ n j hU)
  have hcl : C.g n y' ∈ closure ({C.g n (C.ξY ξ hξ n j hU)} : Set (C.Res n)) := by
    have h := image_closure_subset_closure_image (C.g n).continuous (s := {C.ξY ξ hξ n j hU}) ⟨y', hy, rfl⟩
    rwa [Set.image_singleton] at h
  have heq := hspec _ _ hgo hcl ho'
  rw [C.eq_liftY_of_g_eq n (hRF n) (C.g n y') ho' y' rfl]
  congr 1

theorem edgePt'_exhaust
    (hx : ∀ n, IsClosed ({C.x n} : Set X))
    (hinjO : ∀ n, Function.Injective (oRes n))
    (hM1 : ∀ n (k k' : Fin (C.thick n - 1)) (o : C.Res n), (k : ℕ) < k' →
      o ∈ closure ({gRes n k} : Set (C.Res n)) → o ∈ closure ({gRes n k'} : Set (C.Res n)) → C.ρ n o = C.vertex n →
      ∃ d : Fin (C.thick n), (d : ℕ) = k + 1 ∧ (k' : ℕ) = k + 1 ∧ o = oRes n d)
    (hM2 : ∀ n (j : Fin 2) (hU : ξ j ∈ C.U n) (o o' : C.Res n), C.ρ n o = C.f n ⟨ξ j, hU⟩ →
      o' ∈ closure ({o} : Set (C.Res n)) → C.ρ n o' = C.vertex n → o' = oRes n (C.dEnd n j))
    (hM3 : ∀ n (d : Fin (C.thick n)) (k : Fin (C.thick n - 1)),
      oRes n d ∈ closure ({gRes n k} : Set (C.Res n)) → (d : ℕ) = k ∨ (d : ℕ) = k + 1)
    (hW0 : ∀ x : X, x ∈ closure ({ξ 0} : Set X) → x ∈ closure ({ξ 1} : Set X) → x ∉ C.X0)
    (v w : C.Comps) (hvw : v ≠ w) (y : C.toGlueInput.glued)
    (hy : y ∈ ((C.compG hRF gRes hgRes ξ hξ v).support : Set C.toGlueInput.glued) ∩
      ((C.compG hRF gRes hgRes ξ hξ w).support : Set C.toGlueInput.glued)) :
    ∃ (n : N) (d : Fin (C.thick n)), y = C.edgePt' hRF oRes hoRes n d ∧
      ((v = C.chainPos' n d ∧ w = C.chainPos' n ((d : ℕ) + 1)) ∨
        (w = C.chainPos' n d ∧ v = C.chainPos' n ((d : ℕ) + 1))) := by
  obtain ⟨hv, hw⟩ := hy
  rw [coe_support_compG] at hv hw

  have caseA : ∀ (j : Fin 2) (n : N) (k : Fin (C.thick n - 1)),
      y ∈ closure ({C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)} : Set C.toGlueInput.glued) →
      y ∈ closure ({C.ηG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)} : Set C.toGlueInput.glued) →
      ∃ d : Fin (C.thick n), y = C.edgePt' hRF oRes hoRes n d ∧
        Sum.inl j = C.chainPos' n (if j = 0 then (d : ℕ) else (d : ℕ) + 1) ∧
        Sum.inr ⟨n, k⟩ = C.chainPos' n (if j = 0 then (d : ℕ) + 1 else (d : ℕ)) := by
    intro j n k hj hk
    have hyn : C.toGlueInput.toDR y = C.x n := by
      rw [ηG_inr] at hk
      exact C.toDR_eq_of_mem_closure_exPt n (hRF n) (hx n) _ _ hk
    obtain ⟨y', rfl, hq⟩ := C.exists_ιY_eq_of_toDR_eq n y hyn
    have hU := C.ξ_mem_U_of_ιY_mem_closure hRF gRes hgRes ξ hξ n j y' hj
    have hy' := C.eq_liftY_of_mem_closure_ξY hRF ξ hξ oRes hoRes n j hU (C.dEnd n j) (hM2 n j hU) y' hq
      (C.mem_closure_ξY_of_ιY_mem_closure hRF gRes hgRes ξ hξ n j y' hU hj)
    have hgk : C.g n y' ∈ closure ({gRes n k} : Set (C.Res n)) := by
      rw [ηG_inr] at hk
      exact C.g_mem_closure_of_ιY_mem_closure_exPt hRF n _ _ y' hk
    rw [hy', show C.g n (C.liftY n (hRF n) (oRes n (C.dEnd n j)) (hoRes n (C.dEnd n j))) = oRes n (C.dEnd n j) from
      C.g_liftY n (hRF n) _ _] at hgk
    have hdk := hM3 n _ k hgk
    refine ⟨C.dEnd n j, by rw [hy']; rfl, ?_⟩
    rcases fin_two_eq_zero_or_one j with rfl | rfl
    ·
      simp only [dEnd_zero] at hdk
      have hk0 : (k : ℕ) = 0 := by omega
      refine ⟨by simp [chainPos'_zero], ?_⟩
      simp only [↓reduceIte, dEnd_zero]
      rw [show (0 : ℕ) + 1 = (k : ℕ) + 1 by omega, chainPos'_succ]
    ·
      simp only [dEnd_one] at hdk
      have hk1 : (k : ℕ) + 1 = C.thick n - 1 := by omega
      refine ⟨?_, ?_⟩
      · simp only [one_ne_zero, ↓reduceIte, dEnd_one]
        rw [chainPos'_of_le _ _ _ (by omega)]
      · simp only [one_ne_zero, ↓reduceIte, dEnd_one]
        rw [← hk1, chainPos'_succ]
  rcases v with j | ⟨n, k⟩ <;> rcases w with j' | ⟨m, k'⟩
  ·
    have hjj : j ≠ j' := fun h => hvw (by rw [h])
    have h0 : y ∈ closure ({C.ηG hRF gRes hgRes ξ hξ (Sum.inl 0)} : Set C.toGlueInput.glued) ∧
        y ∈ closure ({C.ηG hRF gRes hgRes ξ hξ (Sum.inl 1)} : Set C.toGlueInput.glued) := by
      rcases fin_two_eq_zero_or_one j with rfl | rfl <;> rcases fin_two_eq_zero_or_one j' with rfl | rfl
      · exact absurd rfl hjj
      · exact ⟨hv, hw⟩
      · exact ⟨hw, hv⟩
      · exact absurd rfl hjj
    obtain ⟨h0, h1⟩ := h0

    have hcl : ∀ j : Fin 2, y ∈ closure ({C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)} : Set C.toGlueInput.glued) →
        C.toGlueInput.toDR y ∈ closure ({ξ j} : Set X) := fun j h => by
      have := image_closure_subset_closure_image C.toGlueInput.toDR.continuous
        (s := {C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)}) ⟨y, h, rfl⟩
      rw [Set.image_singleton] at this
      have h2 : C.toGlueInput.toDR.base (C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)) = ξ j := C.toDR_ηG_inl hRF gRes hgRes ξ hξ j
      rw [h2] at this
      exact this
    have hnot : C.toGlueInput.toDR y ∉ C.X0 := hW0 _ (hcl 0 h0) (hcl 1 h1)
    rw [C.mem_X0] at hnot
    push Not at hnot
    obtain ⟨n, hyn⟩ := hnot
    obtain ⟨y', rfl, hq⟩ := C.exists_ιY_eq_of_toDR_eq n y hyn
    have hU0 := C.ξ_mem_U_of_ιY_mem_closure hRF gRes hgRes ξ hξ n 0 y' h0
    have hU1 := C.ξ_mem_U_of_ιY_mem_closure hRF gRes hgRes ξ hξ n 1 y' h1
    have hy0 := C.eq_liftY_of_mem_closure_ξY hRF ξ hξ oRes hoRes n 0 hU0 (C.dEnd n 0) (hM2 n 0 hU0) y' hq
      (C.mem_closure_ξY_of_ιY_mem_closure hRF gRes hgRes ξ hξ n 0 y' hU0 h0)
    have hy1 := C.eq_liftY_of_mem_closure_ξY hRF ξ hξ oRes hoRes n 1 hU1 (C.dEnd n 1) (hM2 n 1 hU1) y' hq
      (C.mem_closure_ξY_of_ιY_mem_closure hRF gRes hgRes ξ hξ n 1 y' hU1 h1)

    have hends : C.dEnd n 0 = C.dEnd n 1 := by
      apply hinjO n
      rw [← C.g_liftY n (hRF n) (oRes n (C.dEnd n 0)) (hoRes n _), ← C.g_liftY n (hRF n) (oRes n (C.dEnd n 1)) (hoRes n _),
        ← hy0, ← hy1]
    have hthick : C.thick n = 1 := by
      have := congrArg Fin.val hends
      simp only [dEnd_zero, dEnd_one] at this
      have := C.one_le_thick n
      omega
    refine ⟨n, C.dEnd n 0, by rw [hy0]; rfl, ?_⟩
    have hp0 : C.chainPos' n (C.dEnd n 0) = Sum.inl 0 := by simp [chainPos'_zero]
    have hp1 : C.chainPos' n ((C.dEnd n 0 : ℕ) + 1) = Sum.inl 1 := by
      rw [dEnd_zero, chainPos'_of_le _ _ _ (by omega)]
    rw [hp0, hp1]
    rcases fin_two_eq_zero_or_one j with rfl | rfl <;> rcases fin_two_eq_zero_or_one j' with rfl | rfl
    · exact absurd rfl hjj
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd rfl hjj
  ·
    obtain ⟨d, hyd, h1, h2⟩ := caseA j m k' hv hw
    refine ⟨m, d, hyd, ?_⟩
    rcases fin_two_eq_zero_or_one j with rfl | rfl
    · left; exact ⟨by simpa using h1, by simpa using h2⟩
    · right; exact ⟨by simpa using h2, by simpa using h1⟩
  ·
    obtain ⟨d, hyd, h1, h2⟩ := caseA j' n k hw hv
    refine ⟨n, d, hyd, ?_⟩
    rcases fin_two_eq_zero_or_one j' with rfl | rfl
    · right; exact ⟨by simpa using h1, by simpa using h2⟩
    · left; exact ⟨by simpa using h2, by simpa using h1⟩
  ·
    have hyn : C.toGlueInput.toDR y = C.x n := by
      rw [ηG_inr] at hv; exact C.toDR_eq_of_mem_closure_exPt n (hRF n) (hx n) _ _ hv
    have hym : C.toGlueInput.toDR y = C.x m := by
      rw [ηG_inr] at hw; exact C.toDR_eq_of_mem_closure_exPt m (hRF m) (hx m) _ _ hw
    obtain rfl : n = m := C.x_injective (hyn.symm.trans hym)
    have hkk : k ≠ k' := fun h => hvw (by rw [h])
    obtain ⟨y', rfl, hq⟩ := C.exists_ιY_eq_of_toDR_eq n y hyn
    have ho' := C.ρ_g_eq_vertex_of_q_eq n y' hq
    have hgk : C.g n y' ∈ closure ({gRes n k} : Set (C.Res n)) := by
      rw [ηG_inr] at hv; exact C.g_mem_closure_of_ιY_mem_closure_exPt hRF n _ _ y' hv
    have hgk' : C.g n y' ∈ closure ({gRes n k'} : Set (C.Res n)) := by
      rw [ηG_inr] at hw; exact C.g_mem_closure_of_ιY_mem_closure_exPt hRF n _ _ y' hw
    have hy'eq : ∀ (d : Fin (C.thick n)), C.g n y' = oRes n d →
        C.toGlueInput.ιY n y' = C.edgePt' hRF oRes hoRes n d := fun d hd => by
      rw [C.eq_liftY_of_g_eq n (hRF n) (oRes n d) (hoRes n d) y' hd]; rfl
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hkk) with hlt | hlt
    · obtain ⟨d, hd, hk', hgo⟩ := hM1 n k k' _ hlt hgk hgk' ho'
      refine ⟨n, d, hy'eq d hgo, Or.inl ⟨?_, ?_⟩⟩
      · rw [show (d : ℕ) = (k : ℕ) + 1 from hd, chainPos'_succ]
      · rw [show (d : ℕ) + 1 = (k' : ℕ) + 1 by omega, chainPos'_succ]
    · obtain ⟨d, hd, hk', hgo⟩ := hM1 n k' k _ hlt hgk' hgk ho'
      refine ⟨n, d, hy'eq d hgo, Or.inr ⟨?_, ?_⟩⟩
      · rw [show (d : ℕ) = (k' : ℕ) + 1 from hd, chainPos'_succ]
      · rw [show (d : ℕ) + 1 = (k : ℕ) + 1 by omega, chainPos'_succ]

end exhaust

end V3Glue.ChartInput

namespace V3Glue.Aux.Layer0.W6a

variable {Y : Scheme.{u}}

theorem vanishingIdeal_closure_singleton_ideal (U : Y.affineOpens) (x : Y) (hx : x ∈ (U : Y.Opens)) :
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).ideal U =
      (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  have h𝔭 : U.2.fromSpec.base (U.2.primeIdealOf ⟨x, hx⟩) = x := U.2.fromSpec_primeIdealOf ⟨x, hx⟩
  apply le_antisymm
  · intro f hf
    rw [PrimeSpectrum.mem_vanishingIdeal] at hf
    refine hf (U.2.primeIdealOf ⟨x, hx⟩) ?_
    show U.2.fromSpec.base (U.2.primeIdealOf ⟨x, hx⟩) ∈ closure {x}
    rw [h𝔭]
    exact subset_closure rfl
  · intro f hf
    rw [PrimeSpectrum.mem_vanishingIdeal]
    intro q hq
    have hq' : U.2.fromSpec.base q ∈ closure {x} := hq
    have hsp : U.2.fromSpec.base (U.2.primeIdealOf ⟨x, hx⟩) ⤳ U.2.fromSpec.base q := by
      rw [h𝔭]
      exact specializes_iff_mem_closure.mpr hq'
    have hle : U.2.primeIdealOf ⟨x, hx⟩ ≤ q :=
      (PrimeSpectrum.le_iff_specializes _ q).mpr (U.2.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp hsp)
    exact hle hf

theorem map_germ_vanishingIdeal_closure_singleton (U : Y.affineOpens) (x : Y) (hx : x ∈ (U : Y.Opens)) :
    Ideal.map (Y.presheaf.germ (U : Y.Opens) x hx).hom
        ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩).ideal U) =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk x) := by
  rw [vanishingIdeal_closure_singleton_ideal U x hx]
  letI := Y.presheaf.algebra_section_stalk (⟨x, hx⟩ : (U : Y.Opens))
  haveI := U.2.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.AtPrime.map_eq_maximalIdeal (U.2.primeIdealOf ⟨x, hx⟩).asIdeal (Y.presheaf.stalk x)

theorem map_germ_vanishingIdeal_closure_singleton_eq_top (U : Y.affineOpens) (x x' : Y) (hx : x ∈ (U : Y.Opens))
    (h : x ∉ closure {x'}) :
    Ideal.map (Y.presheaf.germ (U : Y.Opens) x hx).hom
        ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {x'}, isClosed_closure⟩).ideal U) = ⊤ := by
  letI := Y.presheaf.algebra_section_stalk (⟨x, hx⟩ : (U : Y.Opens))
  haveI := U.2.isLocalization_stalk ⟨x, hx⟩
  by_contra hne
  have hdisj := (IsLocalization.map_algebraMap_ne_top_iff_disjoint (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Y.presheaf.stalk x) _).mp hne
  have hle : (Scheme.IdealSheafData.vanishingIdeal ⟨closure {x'}, isClosed_closure⟩).ideal U ≤
      (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := by
    intro f hf
    by_contra hf𝔭
    exact Set.disjoint_left.mp hdisj hf𝔭 hf
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal] at hle
  have hmem : U.2.primeIdealOf ⟨x, hx⟩ ∈
      PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal (U.2.fromSpec.base ⁻¹' closure {x'}) : Set _) := hle
  rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure] at hmem
  have hcl : IsClosed (U.2.fromSpec.base ⁻¹' closure {x'}) := isClosed_closure.preimage U.2.fromSpec.continuous
  have hmem' : U.2.fromSpec.base (U.2.primeIdealOf ⟨x, hx⟩) ∈ closure {x'} := hcl.closure_subset hmem
  apply h
  rwa [U.2.fromSpec_primeIdealOf ⟨x, hx⟩] at hmem'

theorem exists_affineOpens_map_germ_vanishingIdeal_closure {ι : Type*} (η : ι → Y)
    (hdist : ∀ v w, v ≠ w → η v ∉ closure {η w}) (v : ι) :
    ∃ (U : Y.affineOpens) (hU : η v ∈ (U : Y.Opens)),
      Ideal.map (Y.presheaf.germ (U : Y.Opens) (η v) hU).hom
          ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {η v}, isClosed_closure⟩).ideal U) =
        IsLocalRing.maximalIdeal (Y.presheaf.stalk (η v)) ∧
      ∀ w, w ≠ v → Ideal.map (Y.presheaf.germ (U : Y.Opens) (η v) hU).hom
          ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {η w}, isClosed_closure⟩).ideal U) = ⊤ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (η v)) isOpen_univ
  exact ⟨⟨U, hU⟩, hxU, map_germ_vanishingIdeal_closure_singleton ⟨U, hU⟩ (η v) hxU,
    fun w hw => map_germ_vanishingIdeal_closure_singleton_eq_top ⟨U, hU⟩ (η v) (η w) hxU (hdist v w (Ne.symm hw))⟩

end V3Glue.Aux.Layer0.W6a

section v3genPrimeAlgebra

open IsLocalRing

theorem V3Glue.Aux.comap_maximalIdeal_eq_map_of_isLocalization_atPrime
    {A Sp Sq : Type*} [CommRing A] [CommRing Sp] [CommRing Sq] [Algebra A Sp] [Algebra A Sq]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] [IsLocalization.AtPrime Sp p] [IsLocalization.AtPrime Sq q]
    [IsLocalRing Sq] (φ : Sp →+* Sq) (hφ : ∀ a, φ (algebraMap A Sp a) = algebraMap A Sq a) :
    (maximalIdeal Sq).comap φ = q.map (algebraMap A Sp) := by
  apply le_antisymm
  · intro z hz
    rw [Ideal.mem_comap] at hz
    set a : A := (IsLocalization.sec p.primeCompl z).1
    set s : p.primeCompl := (IsLocalization.sec p.primeCompl z).2
    have hz' : IsLocalization.mk' Sp a s = z := IsLocalization.mk'_sec Sp z
    rw [← hz'] at hz ⊢
    have h1 : IsLocalization.mk' Sp a s * algebraMap A Sp s = algebraMap A Sp a := IsLocalization.mk'_spec Sp a s
    have h2 : φ (IsLocalization.mk' Sp a s) * algebraMap A Sq s = algebraMap A Sq a := by
      rw [← hφ, ← hφ, ← map_mul, h1]
    have ha : a ∈ q := by
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff Sq q, ← h2]
      exact Ideal.mul_mem_right _ _ hz
    have hu : IsUnit (algebraMap A Sp s) := IsLocalization.map_units Sp s
    rw [← Ideal.mul_unit_mem_iff_mem _ hu, h1]
    exact Ideal.mem_map_of_mem _ ha
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, hφ]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Sq q a).mpr ha

end v3genPrimeAlgebra

namespace AlgebraicGeometry

open V3Glue.Aux

open IsLocalRing TopologicalSpace

def Scheme.v3genPrime (X : Scheme.{u}) {a b : X} (h : a ⤳ b) : Ideal (X.presheaf.stalk b) :=
  (maximalIdeal (X.presheaf.stalk a)).comap (X.presheaf.stalkSpecializes h).hom

theorem Scheme.mem_genPrime_iff (X : Scheme.{u}) {a b : X} (h : a ⤳ b) (z : X.presheaf.stalk b) :
    z ∈ X.v3genPrime h ↔ (X.presheaf.stalkSpecializes h).hom z ∈ maximalIdeal (X.presheaf.stalk a) := Iff.rfl

theorem Scheme.v3genPrime_ne_top (X : Scheme.{u}) {a b : X} (h : a ⤳ b) : X.v3genPrime h ≠ ⊤ :=
  Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top

theorem Scheme.v3genPrime_le_maximalIdeal (X : Scheme.{u}) {a b : X} (h : a ⤳ b) :
    X.v3genPrime h ≤ maximalIdeal (X.presheaf.stalk b) :=
  IsLocalRing.le_maximalIdeal (X.v3genPrime_ne_top h)

theorem IsAffineOpen.map_germ_primeIdealOf_eq_genPrime {X : Scheme.{u}} (U : X.affineOpens) {a b : X} (h : a ⤳ b)
    (hb : b ∈ (U : X.Opens)) (ha : a ∈ (U : X.Opens)) :
    ((U.2.primeIdealOf ⟨a, ha⟩).asIdeal).map (X.presheaf.germ (U : X.Opens) b hb).hom = X.v3genPrime h := by
  letI := X.presheaf.algebra_section_stalk (⟨b, hb⟩ : (U : X.Opens))
  letI := X.presheaf.algebra_section_stalk (⟨a, ha⟩ : (U : X.Opens))
  haveI := U.2.isLocalization_stalk ⟨b, hb⟩
  haveI := U.2.isLocalization_stalk ⟨a, ha⟩
  symm
  refine V3Glue.Aux.comap_maximalIdeal_eq_map_of_isLocalization_atPrime (U.2.primeIdealOf ⟨b, hb⟩).asIdeal
    (U.2.primeIdealOf ⟨a, ha⟩).asIdeal (X.presheaf.stalkSpecializes h).hom (fun s => ?_)
  change (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ (U : X.Opens) b hb).hom s) =
    (X.presheaf.germ (U : X.Opens) a ha).hom s
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]

theorem map_germ_vanishingIdeal_closure_singleton_of_specializes {X : Scheme.{u}} (U : X.affineOpens) {a b : X}
    (h : a ⤳ b) (hb : b ∈ (U : X.Opens)) :
    ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {a}, isClosed_closure⟩).ideal U).map
        (X.presheaf.germ (U : X.Opens) b hb).hom = X.v3genPrime h := by
  have ha : a ∈ (U : X.Opens) := h.mem_open U.1.isOpen hb
  rw [Layer0.W6a.vanishingIdeal_closure_singleton_ideal U a ha, IsAffineOpen.map_germ_primeIdealOf_eq_genPrime U h hb ha]

theorem Scheme.Hom.map_stalkMap_genPrime_le {X Y : Scheme.{u}} (f : X ⟶ Y) {a b : X} (h : a ⤳ b) :
    (Y.v3genPrime (h.map f.continuous)).map (f.stalkMap b).hom ≤ X.v3genPrime h := by
  rw [Ideal.map_le_iff_le_comap]
  intro z hz
  rw [Ideal.mem_comap]
  change (X.presheaf.stalkSpecializes h).hom ((f.stalkMap b).hom z) ∈ maximalIdeal _
  have key : (X.presheaf.stalkSpecializes h).hom ((f.stalkMap b).hom z) =
      (f.stalkMap a).hom ((Y.presheaf.stalkSpecializes (h.map f.continuous)).hom z) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.stalkSpecializes_stalkMap]
  rw [key]
  exact map_nonunit _ _ hz

theorem Scheme.Hom.v3genPrime_le_map_stalkMap_genPrime {X Y : Scheme.{u}} (f : X ⟶ Y) {a b : X} (h : a ⤳ b)
    (hsurj : Function.Surjective (f.stalkMap b).hom) :
    X.v3genPrime h ≤ (Y.v3genPrime (h.map f.continuous)).map (f.stalkMap b).hom := by
  intro z' hz'
  obtain ⟨z, rfl⟩ := hsurj z'
  apply Ideal.mem_map_of_mem
  change (Y.presheaf.stalkSpecializes (h.map f.continuous)).hom z ∈ maximalIdeal _
  have hz : (X.presheaf.stalkSpecializes h).hom ((f.stalkMap b).hom z) ∈ maximalIdeal _ := hz'
  have key : (X.presheaf.stalkSpecializes h).hom ((f.stalkMap b).hom z) =
      (f.stalkMap a).hom ((Y.presheaf.stalkSpecializes (h.map f.continuous)).hom z) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.stalkSpecializes_stalkMap]
  rw [key, mem_maximalIdeal, mem_nonunits_iff] at hz
  rw [mem_maximalIdeal, mem_nonunits_iff]
  exact fun hu => hz (hu.map _)

theorem v3genPrime_sup_genPrime_eq_maximalIdeal_of_map_maximalIdeal {X Y : Scheme.{u}} (g : Y ⟶ X)
    {a₁ a₂ b : Y} (h₁ : a₁ ⤳ b) (h₂ : a₂ ⤳ b)
    {μ₁ μ₂ o : X} (e₁ : g a₁ = μ₁) (e₂ : g a₂ = μ₂) (e : g b = o) (hμ₁ : μ₁ ⤳ o) (hμ₂ : μ₂ ⤳ o)
    (hmax : (maximalIdeal (X.presheaf.stalk (g b))).map (g.stalkMap b).hom = maximalIdeal (Y.presheaf.stalk b))
    (hX : maximalIdeal (X.presheaf.stalk o) ≤ X.v3genPrime hμ₁ ⊔ X.v3genPrime hμ₂) :
    Y.v3genPrime h₁ ⊔ Y.v3genPrime h₂ = maximalIdeal (Y.presheaf.stalk b) := by
  subst e₁ e₂ e
  apply le_antisymm (sup_le (Y.v3genPrime_le_maximalIdeal h₁) (Y.v3genPrime_le_maximalIdeal h₂))
  rw [← hmax, Ideal.map_le_iff_le_comap]
  refine hX.trans ?_
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_sup]
  exact sup_le_sup (g.map_stalkMap_genPrime_le h₁) (g.map_stalkMap_genPrime_le h₂)

theorem v3genPrime_sup_genPrime_eq_maximalIdeal_of_stalkMap_bijective {Y G : Scheme.{u}} (ι : Y ⟶ G)
    {a₁ a₂ b : Y} (h₁ : a₁ ⤳ b) (h₂ : a₂ ⤳ b) {η₁ η₂ y : G} (e₁ : ι a₁ = η₁) (e₂ : ι a₂ = η₂) (e : ι b = y)
    (hη₁ : η₁ ⤳ y) (hη₂ : η₂ ⤳ y)
    (hbij : Function.Bijective (ι.stalkMap b).hom)
    (hY : Y.v3genPrime h₁ ⊔ Y.v3genPrime h₂ = maximalIdeal (Y.presheaf.stalk b)) :
    G.v3genPrime hη₁ ⊔ G.v3genPrime hη₂ = maximalIdeal (G.presheaf.stalk y) := by
  subst e₁ e₂ e
  apply le_antisymm (sup_le (G.v3genPrime_le_maximalIdeal _) (G.v3genPrime_le_maximalIdeal _))
  have h1 : (maximalIdeal (G.presheaf.stalk (ι b))).map (ι.stalkMap b).hom ≤
      (G.v3genPrime hη₁ ⊔ G.v3genPrime hη₂).map (ι.stalkMap b).hom := by
    rw [Ideal.map_sup]
    calc (maximalIdeal (G.presheaf.stalk (ι b))).map (ι.stalkMap b).hom
        ≤ maximalIdeal (Y.presheaf.stalk b) := Ideal.map_le_iff_le_comap.mpr (fun z hz => map_nonunit _ z hz)
      _ = Y.v3genPrime h₁ ⊔ Y.v3genPrime h₂ := hY.symm
      _ ≤ _ := sup_le_sup (ι.v3genPrime_le_map_stalkMap_genPrime h₁ hbij.2) (ι.v3genPrime_le_map_stalkMap_genPrime h₂ hbij.2)
  have h2 := Ideal.comap_mono (f := (ι.stalkMap b).hom) h1
  rwa [Ideal.comap_map_of_bijective _ hbij, Ideal.comap_map_of_bijective _ hbij] at h2

theorem IsOpenImmersion.v3_stalkMap_bijective {Y G : Scheme.{u}} (ι : Y ⟶ G) [IsOpenImmersion ι] (b : Y) :
    Function.Bijective (ι.stalkMap b).hom :=
  (asIso (ι.stalkMap b)).commRingCatIsoToRingEquiv.bijective

theorem map_germ_vanishingIdeal_sup_eq_maximalIdeal {G : Scheme.{u}} {η₁ η₂ y : G} (h₁ : η₁ ⤳ y) (h₂ : η₂ ⤳ y)
    (hgen : G.v3genPrime h₁ ⊔ G.v3genPrime h₂ = maximalIdeal (G.presheaf.stalk y))
    (U : G.affineOpens) (hU : y ∈ (U : G.Opens)) :
    Ideal.map (G.presheaf.germ (U : G.Opens) y hU).hom
      ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {η₁}, isClosed_closure⟩).ideal U ⊔
        (Scheme.IdealSheafData.vanishingIdeal ⟨closure {η₂}, isClosed_closure⟩).ideal U) =
      maximalIdeal (G.presheaf.stalk y) := by
  rw [Ideal.map_sup, map_germ_vanishingIdeal_closure_singleton_of_specializes U h₁ hU,
    map_germ_vanishingIdeal_closure_singleton_of_specializes U h₂ hU, hgen]

theorem exists_affineOpens_map_germ_vanishingIdeal_sup_eq_maximalIdeal {G : Scheme.{u}} {η₁ η₂ y : G}
    (h₁ : η₁ ⤳ y) (h₂ : η₂ ⤳ y) (hgen : G.v3genPrime h₁ ⊔ G.v3genPrime h₂ = maximalIdeal (G.presheaf.stalk y)) :
    ∃ (U : G.affineOpens) (hU : y ∈ (U : G.Opens)),
      Ideal.map (G.presheaf.germ (U : G.Opens) y hU).hom
        ((Scheme.IdealSheafData.vanishingIdeal ⟨closure {η₁}, isClosed_closure⟩).ideal U ⊔
          (Scheme.IdealSheafData.vanishingIdeal ⟨closure {η₂}, isClosed_closure⟩).ideal U) =
        maximalIdeal (G.presheaf.stalk y) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := G.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  exact ⟨⟨U, hU⟩, hyU, map_germ_vanishingIdeal_sup_eq_maximalIdeal h₁ h₂ hgen ⟨U, hU⟩ hyU⟩

end AlgebraicGeometry

namespace V3Glue.ChartInput

open V3Glue.Aux

open AlgebraicGeometry V3Glue.Aux.Layer0 TopologicalSpace IsLocalRing

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section transversalY

variable (n : N) (hRF : IsIso ((C.f n).residueFieldMap (C.xU n)))

theorem liftY_specializes_liftY (o o' : C.Res n) (ho : C.ρ n o = C.vertex n) (ho' : C.ρ n o' = C.vertex n)
    (hcl : o' ∈ closure ({o} : Set (C.Res n))) : C.liftY n hRF o ho ⤳ C.liftY n hRF o' ho' :=
  specializes_iff_mem_closure.mpr (C.liftY_mem_closure_liftY n hRF o o' ho ho' hcl)

end transversalY

section transversal

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)
  (oRes : ∀ n, Fin (C.thick n) → C.Res n) (hoRes : ∀ n d, C.ρ n (oRes n d) = C.vertex n)

theorem ξY_specializes_liftY (n : N) (j : Fin 2) (d₀ : Fin (C.thick n))
    (hU : ξ j ∈ C.U n) (hxcl : C.xU n ∈ closure ({⟨ξ j, hU⟩} : Set ↥(C.U n)))
    (hspec : ∀ o o' : C.Res n, C.ρ n o = C.f n ⟨ξ j, hU⟩ → o' ∈ closure ({o} : Set (C.Res n)) →
      C.ρ n o' = C.vertex n → o' = oRes n d₀) :
    C.ξY ξ hξ n j hU ⤳ C.liftY n (hRF n) (oRes n d₀) (hoRes n d₀) := by
  rw [specializes_iff_mem_closure]

  have hqcl : IsClosed ((C.q n).base '' closure ({C.ξY ξ hξ n j hU} : Set (C.Y n))) :=
    (C.q n).isClosedMap _ isClosed_closure
  have hx : C.xU n ∈ (C.q n).base '' closure ({C.ξY ξ hξ n j hU} : Set (C.Y n)) := by
    refine closure_minimal ?_ hqcl hxcl
    intro z hz
    have hz' : z = ⟨ξ j, hU⟩ := hz
    subst hz'
    exact ⟨_, subset_closure rfl, C.q_ξY ξ hξ n j hU⟩
  obtain ⟨y', hy', hqy'⟩ := hx
  have := C.eq_liftY_of_mem_closure_ξY hRF ξ hξ oRes hoRes n j hU d₀ hspec y' hqy' hy'
  rw [← this]
  exact hy'

theorem edgePt'_transversal (n : N) (d : Fin (C.thick n)) (v w : C.Comps)
    (a₁ a₂ : C.Y n)
    (ha₁ : C.toGlueInput.ιY n a₁ = C.ηG hRF gRes hgRes ξ hξ v) (ha₂ : C.toGlueInput.ιY n a₂ = C.ηG hRF gRes hgRes ξ hξ w)
    (h₁ : a₁ ⤳ C.liftY n (hRF n) (oRes n d) (hoRes n d)) (h₂ : a₂ ⤳ C.liftY n (hRF n) (oRes n d) (hoRes n d))
    (μ₁ μ₂ : C.Res n) (e₁ : C.g n a₁ = μ₁) (e₂ : C.g n a₂ = μ₂) (hμ₁ : μ₁ ⤳ oRes n d) (hμ₂ : μ₂ ⤳ oRes n d)
    (hmax : (maximalIdeal ((C.Res n).presheaf.stalk ((C.g n).base (C.liftY n (hRF n) (oRes n d) (hoRes n d))))).map
        ((C.g n).stalkMap (C.liftY n (hRF n) (oRes n d) (hoRes n d))).hom =
      maximalIdeal ((C.Y n).presheaf.stalk (C.liftY n (hRF n) (oRes n d) (hoRes n d))))
    (hM4 : maximalIdeal ((C.Res n).presheaf.stalk (oRes n d)) ≤ (C.Res n).v3genPrime hμ₁ ⊔ (C.Res n).v3genPrime hμ₂) :
    ∃ (U : C.toGlueInput.glued.affineOpens) (hU : C.edgePt' hRF oRes hoRes n d ∈ (U : C.toGlueInput.glued.Opens)),
      Ideal.map (C.toGlueInput.glued.presheaf.germ (U : C.toGlueInput.glued.Opens) (C.edgePt' hRF oRes hoRes n d) hU).hom
        ((C.compG hRF gRes hgRes ξ hξ v).ideal U ⊔ (C.compG hRF gRes hgRes ξ hξ w).ideal U) =
      maximalIdeal (C.toGlueInput.glued.presheaf.stalk (C.edgePt' hRF oRes hoRes n d)) := by

  have hY := v3genPrime_sup_genPrime_eq_maximalIdeal_of_map_maximalIdeal (C.g n) h₁ h₂ e₁ e₂
    (C.g_liftY n (hRF n) (oRes n d) (hoRes n d)) hμ₁ hμ₂ hmax hM4

  have hv : C.ηG hRF gRes hgRes ξ hξ v ⤳ C.edgePt' hRF oRes hoRes n d := by
    rw [← ha₁]; exact h₁.map (C.toGlueInput.ιY n).continuous
  have hw : C.ηG hRF gRes hgRes ξ hξ w ⤳ C.edgePt' hRF oRes hoRes n d := by
    rw [← ha₂]; exact h₂.map (C.toGlueInput.ιY n).continuous
  have hG := v3genPrime_sup_genPrime_eq_maximalIdeal_of_stalkMap_bijective (C.toGlueInput.ιY n) h₁ h₂ ha₁ ha₂
    (rfl : C.toGlueInput.ιY n (C.liftY n (hRF n) (oRes n d) (hoRes n d)) = C.edgePt' hRF oRes hoRes n d) hv hw
    (IsOpenImmersion.v3_stalkMap_bijective _ _) hY
  exact exists_affineOpens_map_germ_vanishingIdeal_sup_eq_maximalIdeal hv hw hG

theorem edgePt'_transversal_of_mem (n : N) (d : Fin (C.thick n)) (v w : C.Comps)
    (a₁ a₂ : C.Y n)
    (ha₁ : C.toGlueInput.ιY n a₁ = C.ηG hRF gRes hgRes ξ hξ v) (ha₂ : C.toGlueInput.ιY n a₂ = C.ηG hRF gRes hgRes ξ hξ w)
    (h₁ : a₁ ⤳ C.liftY n (hRF n) (oRes n d) (hoRes n d)) (h₂ : a₂ ⤳ C.liftY n (hRF n) (oRes n d) (hoRes n d))
    (μ₁ μ₂ : C.Res n) (e₁ : C.g n a₁ = μ₁) (e₂ : C.g n a₂ = μ₂) (hμ₁ : μ₁ ⤳ oRes n d) (hμ₂ : μ₂ ⤳ oRes n d)
    (hmax : (maximalIdeal ((C.Res n).presheaf.stalk ((C.g n).base (C.liftY n (hRF n) (oRes n d) (hoRes n d))))).map
        ((C.g n).stalkMap (C.liftY n (hRF n) (oRes n d) (hoRes n d))).hom =
      maximalIdeal ((C.Y n).presheaf.stalk (C.liftY n (hRF n) (oRes n d) (hoRes n d))))
    (hM4 : maximalIdeal ((C.Res n).presheaf.stalk (oRes n d)) ≤ (C.Res n).v3genPrime hμ₁ ⊔ (C.Res n).v3genPrime hμ₂)
    (U : C.toGlueInput.glued.affineOpens) (hU : C.edgePt' hRF oRes hoRes n d ∈ (U : C.toGlueInput.glued.Opens)) :
    Ideal.map (C.toGlueInput.glued.presheaf.germ (U : C.toGlueInput.glued.Opens) (C.edgePt' hRF oRes hoRes n d) hU).hom
        ((C.compG hRF gRes hgRes ξ hξ v).ideal U ⊔ (C.compG hRF gRes hgRes ξ hξ w).ideal U) =
      maximalIdeal (C.toGlueInput.glued.presheaf.stalk (C.edgePt' hRF oRes hoRes n d)) := by
  have hY := v3genPrime_sup_genPrime_eq_maximalIdeal_of_map_maximalIdeal (C.g n) h₁ h₂ e₁ e₂
    (C.g_liftY n (hRF n) (oRes n d) (hoRes n d)) hμ₁ hμ₂ hmax hM4
  have hv : C.ηG hRF gRes hgRes ξ hξ v ⤳ C.edgePt' hRF oRes hoRes n d := by
    rw [← ha₁]; exact h₁.map (C.toGlueInput.ιY n).continuous
  have hw : C.ηG hRF gRes hgRes ξ hξ w ⤳ C.edgePt' hRF oRes hoRes n d := by
    rw [← ha₂]; exact h₂.map (C.toGlueInput.ιY n).continuous
  have hG := v3genPrime_sup_genPrime_eq_maximalIdeal_of_stalkMap_bijective (C.toGlueInput.ιY n) h₁ h₂ ha₁ ha₂
    (rfl : C.toGlueInput.ιY n (C.liftY n (hRF n) (oRes n d) (hoRes n d)) = C.edgePt' hRF oRes hoRes n d) hv hw
    (IsOpenImmersion.v3_stalkMap_bijective _ _) hY
  exact map_germ_vanishingIdeal_sup_eq_maximalIdeal hv hw hG U hU

end transversal

end V3Glue.ChartInput

namespace Topology.IsOpenEmbedding

theorem v3_eq_of_specializes_of_forall {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {i : α → β}
    (hi : Topology.IsOpenEmbedding i) (w : α) (P : β → Prop) (Q : α → Prop) (hPQ : ∀ a, P (i a) → Q a)
    (hmax : ∀ a, a ⤳ w → Q a → a = w) (y : β) (hy : y ⤳ i w) (hPy : P y) : y = i w := by
  have hmem : y ∈ Set.range i := by
    have h := hy.mem_open hi.isOpen_range ⟨w, rfl⟩
    exact h
  obtain ⟨a, rfl⟩ := hmem
  rw [hmax a (hi.isInducing.specializes_iff.mp hy) (hPQ a hPy)]

end Topology.IsOpenEmbedding

namespace V3Glue.ChartInput

open V3Glue.Aux

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section maximal

variable (n : N) (hRF : IsIso ((C.f n).residueFieldMap (C.xU n)))

theorem liftY_eq_of_specializes (o : C.Res n) (ho : C.ρ n o = C.vertex n) (Q : C.Res n → Prop)
    (hM : ∀ o' : C.Res n, o' ⤳ o → Q o' → o' = o)
    (y' : C.Y n) (hy : y' ⤳ C.liftY n hRF o ho) (hQ : Q (C.g n y')) : y' = C.liftY n hRF o ho := by
  have h1 : C.g n y' ⤳ o := by
    have h := hy.map (C.g n).continuous
    rwa [show (C.g n).base (C.liftY n hRF o ho) = o from C.g_liftY n hRF o ho] at h
  have h2 : C.g n y' = o := hM _ h1 hQ
  exact C.eq_of_g_eq n hRF y' _ (h2.trans (C.g_liftY n hRF o ho).symm) (by rw [h2]; exact ho)

theorem exPt_eq_of_specializes (o : C.Res n) (ho : C.ρ n o = C.vertex n) (P : C.toGlueInput.glued → Prop)
    (Q : C.Res n → Prop) (hPQ : ∀ y' : C.Y n, P (C.toGlueInput.ιY n y') → Q (C.g n y'))
    (hM : ∀ o' : C.Res n, o' ⤳ o → Q o' → o' = o)
    (y : C.toGlueInput.glued) (hy : y ⤳ C.exPt n hRF o ho) (hP : P y) : y = C.exPt n hRF o ho := by
  rw [exPt_def] at hy ⊢
  exact (C.toGlueInput.ιY n).isOpenEmbedding.v3_eq_of_specializes_of_forall _ P (fun y' => Q (C.g n y')) hPQ
    (fun y' hy' hQ => C.liftY_eq_of_specializes n hRF o ho Q hM y' hy' hQ) y hy hP

end maximal

section maximalEta

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (gRes : ∀ n, Fin (C.thick n - 1) → C.Res n) (hgRes : ∀ n k, C.ρ n (gRes n k) = C.vertex n)
  (ξ : Fin 2 → X) (hξ : ∀ j, ξ j ∈ C.X0)

theorem ηG_inr_eq_of_specializes (n : N) (k : Fin (C.thick n - 1)) (P : C.toGlueInput.glued → Prop)
    (Q : C.Res n → Prop) (hPQ : ∀ y' : C.Y n, P (C.toGlueInput.ιY n y') → Q (C.g n y'))
    (hM : ∀ o' : C.Res n, o' ⤳ gRes n k → Q o' → o' = gRes n k)
    (y : C.toGlueInput.glued) (hy : y ⤳ C.ηG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩)) (hP : P y) :
    y = C.ηG hRF gRes hgRes ξ hξ (Sum.inr ⟨n, k⟩) := by
  rw [ηG_inr] at hy ⊢
  exact C.exPt_eq_of_specializes n (hRF n) (gRes n k) (hgRes n k) P Q hPQ hM y hy hP

theorem ηG_inl_eq_of_specializes (j : Fin 2) (P : C.toGlueInput.glued → Prop) (Q : C.X0 → Prop)
    (hPQ : ∀ x' : C.X0, P (C.toGlueInput.ιX0 x') → Q x')
    (hM : ∀ x' : C.X0, x' ⤳ ⟨ξ j, hξ j⟩ → Q x' → x' = ⟨ξ j, hξ j⟩)
    (y : C.toGlueInput.glued) (hy : y ⤳ C.ηG hRF gRes hgRes ξ hξ (Sum.inl j)) (hP : P y) :
    y = C.ηG hRF gRes hgRes ξ hξ (Sum.inl j) := by
  rw [ηG_inl] at hy ⊢
  exact C.toGlueInput.ιX0.isOpenEmbedding.v3_eq_of_specializes_of_forall _ P Q hPQ hM y hy hP

end maximalEta

end V3Glue.ChartInput

end


