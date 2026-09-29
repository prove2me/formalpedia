-- Prove2me | Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
-- name    : AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/e20765b8-46b0-5639-a2f2-deb02d89e3a5
-- title:
--   Morphisms over a ring map of two-affine-cover schemes; H¹ functoriality
-- statement:
--   Throughout, $c\colon X\to\operatorname{Spec}R$ is a scheme over an affine base equipped with a `TwoAffineOpenCover` $\mathcal V$, that is a pair of affine opens $U_0,U_1$ with affine intersection covering $X$; the associated two-chart Čech data have $A_0=\Gamma(X,U_0)$, $A_1=\Gamma(X,U_1)$, $A_{01}=\Gamma(X,U_0\cap U_1)$ as $R$-algebras via $c$, and $H^1$ of the structure-sheaf sections is $A_{01}$ modulo the image of the differential $(s_0,s_1)\mapsto s_1|_{U_0\cap U_1}-s_0|_{U_0\cap U_1}$. The structure `HomOver τ 𝒱 c 𝒲 c'`, for a ring homomorphism $\tau\colon R\to S$ and data $c'\colon Y\to\operatorname{Spec}S$ with cover $\mathcal W$, bundles a morphism $\varphi\colon Y\to X$ together with the commutation $c\circ\varphi=\operatorname{Spec}(\tau)\circ c'$ and the two containments $W_i\subseteq\varphi^{-1}(U_i)$ ($i=0,1$); the induced containment on intersections is `inf_le`. Pull-back of sections along $\varphi$ over such an inclusion of opens is shown to carry $\tau$ on scalars (`appLE_algebraMap`), so it is recorded as the $\tau$-semilinear maps `sectionsMap`, and in particular `map0`, `map1`, `map01` on the three chart algebras. These commute with the two restrictions and hence with the Čech differential, so that the image of the differential on $X$ lands in the preimage of the image on $Y$, and `H1map` is the resulting $\tau$-semilinear map on $H^1$, sending the class of $y$ to the class of $\varphi^{*}y$. Identity and composite morphisms over $\operatorname{id}_R$ and over $\upsilon\circ\tau$ are provided (`HomOver.id`, `HomOver.comp`, whose underlying morphism is the composite of the two underlying morphisms), with `id_H1map`, `comp_H1map` and `H1map_congr`, the last saying that `H1map` depends on the underlying scheme morphism alone, not on $\tau$ or on the containment proofs.
--
--   Two families of such morphisms are then singled out. For an $R$-algebra $A$, `HomOver.baseChange` is the first projection $X\times_{\operatorname{Spec}R}\operatorname{Spec}A\to X$ viewed as a morphism over $\operatorname{algebraMap} R A$, the cover on the source being the pulled-back cover $\mathcal V_A$ (whose charts are by definition the preimages of $U_0,U_1$, so the containments hold as equalities); `H1baseChangeMap` is its `H1map`. For an $R$-algebra map $g\colon A\to B$, `HomOver.stage` is the morphism $X_B\to X_A$ obtained as `RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R g)`, i.e. the identity on $X$ crossed with $\operatorname{Spec}(g)$, regarded as a morphism over the underlying ring map of $g$; `H1stageMap` is its `H1map`. The accompanying identities compute these maps on classes of sections over the intersection chart and record that the stage maps form a functor in the $R$-algebra variable: $\mathrm{H1stageMap}(g)\circ\mathrm{H1baseChangeMap}_A=\mathrm{H1baseChangeMap}_B$, $\mathrm{H1stageMap}(\operatorname{id}_A)=\operatorname{id}$, and $\mathrm{H1stageMap}(g')\circ\mathrm{H1stageMap}(g)=\mathrm{H1stageMap}(g'\circ g)$.
--
--   **Relation to Mathlib.** Mathlib has no two-chart Čech complex of a scheme covered by two affine opens, nor a notion of morphism of such covered schemes over a ring map; both are the project's own, built on Mathlib's scheme pullbacks, preimages of opens and the `appLE` sections maps.
--
--   **Where it is used.** These maps supply the functoriality and base-change behaviour of the two-chart Čech $H^1$ of the structure sheaf used in the project's treatment of the relative Picard functor and Néron models: the stage maps are taken along the same morphisms $X_B\to X_A$ along which rigidified line bundles are pulled back, so that classes of line bundles in $H^1$ can be compared across base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange.lean

import Definitions.Def_AlgebraicGeometry_RelPicardStageHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] {T : Type u} [CommRing T]

structure HomOver (τ : R →+* S) {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {Y : Scheme.{u}} (𝒲 : Y.TwoAffineOpenCover) (c' : Y ⟶ Spec (.of S)) where

  hom : Y ⟶ X
  comm : hom ≫ c = c' ≫ Spec.map (CommRingCat.ofHom τ)
  U0_le : 𝒲.U0 ≤ hom ⁻¹ᵁ 𝒱.U0
  U1_le : 𝒲.U1 ≤ hom ⁻¹ᵁ 𝒱.U1

namespace HomOver

variable {τ : R →+* S} {X : Scheme.{u}} {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)}
  {Y : Scheme.{u}} {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ Spec (.of S)} (f : HomOver τ 𝒱 c 𝒲 c')

theorem inf_le : 𝒲.U0 ⊓ 𝒲.U1 ≤ f.hom ⁻¹ᵁ (𝒱.U0 ⊓ 𝒱.U1) := by
  rw [Scheme.Hom.preimage_inf]; exact inf_le_inf f.U0_le f.U1_le

theorem appLE_algebraMap {U : X.Opens} {V : Y.Opens} (h : V ≤ f.hom ⁻¹ᵁ U) (r : R) :
    (f.hom.appLE U V h).hom ((algebraOfHom c U).algebraMap r) = (algebraOfHom c' V).algebraMap (τ r) := by
  change (c.appLE ⊤ U le_top ≫ f.hom.appLE U V h).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) =
    (c'.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (.of S)).inv.hom (τ r))
  rw [Scheme.Hom.appLE_comp_appLE]
  have h4 : (Scheme.ΓSpecIso (.of S)).inv.hom (τ r) =
      (Spec.map (CommRingCat.ofHom τ)).appTop.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) := by
    change (CommRingCat.ofHom τ ≫ (Scheme.ΓSpecIso (.of S)).inv).hom r = _
    rw [Scheme.ΓSpecIso_inv_naturality]
    rfl
  rw [h4, ← CategoryTheory.ConcreteCategory.comp_apply]
  suffices key : ∀ (φ : Y ⟶ Spec (.of R)), φ = c' ≫ Spec.map (CommRingCat.ofHom τ) → ∀ (e : V ≤ φ ⁻¹ᵁ ⊤),
      φ.appLE ⊤ V e = (Spec.map (CommRingCat.ofHom τ)).appTop ≫ c'.appLE ⊤ V le_top by
    rw [key _ f.comm]
    rfl
  rintro φ rfl e
  have happ : (Spec.map (CommRingCat.ofHom τ)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom τ)).appTop :=
    (Scheme.Hom.app_eq_appLE _).symm
  rw [← happ, Scheme.Hom.appLE_comp_appLE]

def sectionsMap {U : X.Opens} {V : Y.Opens} (h : V ≤ f.hom ⁻¹ᵁ U) :
    letI := algebraOfHom c U; letI := algebraOfHom c' V
    Γ(X, U) →ₛₗ[τ] Γ(Y, V) :=
  letI := algebraOfHom c U; letI := algebraOfHom c' V
  { toFun := (f.hom.appLE U V h).hom
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => by
      change (f.hom.appLE U V h).hom ((algebraOfHom c U).algebraMap r * x) =
        (algebraOfHom c' V).algebraMap (τ r) * (f.hom.appLE U V h).hom x
      rw [map_mul, appLE_algebraMap] }

def map0 : (𝒱.cover c).A0 →ₛₗ[τ] (𝒲.cover c').A0 := f.sectionsMap f.U0_le

def map1 : (𝒱.cover c).A1 →ₛₗ[τ] (𝒲.cover c').A1 := f.sectionsMap f.U1_le

def map01 : (𝒱.cover c).A01 →ₛₗ[τ] (𝒲.cover c').A01 := f.sectionsMap f.inf_le

theorem map0_apply (x : (𝒱.cover c).A0) : f.map0 x = (f.hom.appLE 𝒱.U0 𝒲.U0 f.U0_le).hom x := rfl
theorem map1_apply (x : (𝒱.cover c).A1) : f.map1 x = (f.hom.appLE 𝒱.U1 𝒲.U1 f.U1_le).hom x := rfl
theorem map01_apply (x : (𝒱.cover c).A01) :
    f.map01 x = (f.hom.appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒲.U0 ⊓ 𝒲.U1) f.inf_le).hom x := rfl

theorem map01_ρ0 (x : (𝒱.cover c).A0) : f.map01 ((𝒱.cover c).ρ0 x) = (𝒲.cover c').ρ0 (f.map0 x) := by
  rw [map01_apply, map0_apply, cover_ρ0_apply, cover_ρ0_apply, ← CategoryTheory.ConcreteCategory.comp_apply,
    ← CategoryTheory.ConcreteCategory.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem map01_ρ1 (x : (𝒱.cover c).A1) : f.map01 ((𝒱.cover c).ρ1 x) = (𝒲.cover c').ρ1 (f.map1 x) := by
  rw [map01_apply, map1_apply, cover_ρ1_apply, cover_ρ1_apply, ← CategoryTheory.ConcreteCategory.comp_apply,
    ← CategoryTheory.ConcreteCategory.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem map01_cechDiff (s : (𝒱.cover c).A0 × (𝒱.cover c).A1) :
    f.map01 ((𝒱.structureSheafSections c).cechDiff s) =
      (𝒲.structureSheafSections c').cechDiff (f.map0 s.1, f.map1 s.2) := by
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply, map_sub]
  change f.map01 ((1 : (𝒱.cover c).A01) * (𝒱.cover c).ρ1 s.2) - f.map01 ((𝒱.cover c).ρ0 s.1) =
    (1 : (𝒲.cover c').A01) * (𝒲.cover c').ρ1 (f.map1 s.2) - (𝒲.cover c').ρ0 (f.map0 s.1)
  rw [one_mul, one_mul, map01_ρ0, map01_ρ1]

theorem range_cechDiff_le_comap :
    LinearMap.range (𝒱.structureSheafSections c).cechDiff ≤
      (LinearMap.range (𝒲.structureSheafSections c').cechDiff).comap f.map01 := by
  rintro _ ⟨s, rfl⟩
  rw [Submodule.mem_comap, map01_cechDiff]
  exact LinearMap.mem_range_self _ _

def H1map : (𝒱.structureSheafSections c).H1 →ₛₗ[τ] (𝒲.structureSheafSections c').H1 :=
  Submodule.mapQ _ _ f.map01 f.range_cechDiff_le_comap

theorem H1map_mk (y : (𝒱.cover c).A01) :
    f.H1map (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f.map01 y) := rfl

theorem H1map_congr {τ' : R →+* S} {f : HomOver τ 𝒱 c 𝒲 c'} {g : HomOver τ' 𝒱 c 𝒲 c'} (h : f.hom = g.hom)
    (x : (𝒱.structureSheafSections c).H1) : f.H1map x = g.H1map x := by
  obtain ⟨fh, _, _, _⟩ := f
  obtain ⟨gh, _, _, _⟩ := g
  cases h
  induction x using Submodule.Quotient.induction_on with
  | H y => rfl

protected def id (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) : HomOver (RingHom.id R) 𝒱 c 𝒱 c where
  hom := 𝟙 X
  comm := by
    change 𝟙 X ≫ c = c ≫ Spec.map (𝟙 _)
    rw [Spec.map_id, Category.id_comp, Category.comp_id]
  U0_le := le_rfl
  U1_le := le_rfl

theorem id_H1map (x : (𝒱.structureSheafSections c).H1) : (HomOver.id 𝒱 c).H1map x = x := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    have key : (HomOver.id 𝒱 c).hom.appLE (𝒱.U0 ⊓ 𝒱.U1) (𝒱.U0 ⊓ 𝒱.U1) (HomOver.id 𝒱 c).inf_le = 𝟙 _ := by
      change (𝟙 X : X ⟶ X).app _ ≫ X.presheaf.map _ = _
      rw [Scheme.Hom.id_app]
      erw [Category.id_comp]
      exact (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_id _)
    rw [H1map_mk, map01_apply, key]
    rfl

def comp {υ : S →+* T} {Z : Scheme.{u}} {𝒳 : Z.TwoAffineOpenCover} {c'' : Z ⟶ Spec (.of T)}
    (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') : HomOver (υ.comp τ) 𝒱 c 𝒳 c'' where
  hom := g.hom ≫ f.hom
  comm := by
    rw [Category.assoc, f.comm, ← Category.assoc, g.comm, Category.assoc, ← Spec.map_comp]
    rfl
  U0_le := g.U0_le.trans (by rw [Scheme.Hom.comp_preimage]; exact Scheme.Hom.preimage_mono _ f.U0_le)
  U1_le := g.U1_le.trans (by rw [Scheme.Hom.comp_preimage]; exact Scheme.Hom.preimage_mono _ f.U1_le)

theorem comp_H1map {υ : S →+* T} {Z : Scheme.{u}} {𝒳 : Z.TwoAffineOpenCover} {c'' : Z ⟶ Spec (.of T)}
    (g : HomOver υ 𝒲 c' 𝒳 c'') (f : HomOver τ 𝒱 c 𝒲 c') (x : (𝒱.structureSheafSections c).H1) :
    (g.comp f).H1map x = g.H1map (f.H1map x) := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    rw [H1map_mk, H1map_mk, H1map_mk, map01_apply, map01_apply, map01_apply,
      ← CategoryTheory.ConcreteCategory.comp_apply, Scheme.Hom.appLE_comp_appLE]
    rfl

end HomOver

section BaseChange

variable {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
  {A : Type u} [CommRing A] [Algebra R A] {B : Type u} [CommRing B] [Algebra R B]
  {B' : Type u} [CommRing B'] [Algebra R B']

variable (A) in

def HomOver.baseChange :
    HomOver (algebraMap R A) 𝒱 c (𝒱.pullback c A) (pullback.snd c (specMap R A)) where
  hom := pullback.fst c (specMap R A)
  comm := pullback.condition
  U0_le := le_rfl
  U1_le := le_rfl

def HomOver.stage (g : A →ₐ[R] B) :
    HomOver g.toRingHom (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒱.pullback c B) (pullback.snd c (specMap R B)) where
  hom := RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R g)
  comm := pullback.lift_snd _ _ _
  U0_le := (baseChangeSnd_preimage_U0 𝒱 c (RelPicard.LFP.stageHom R g)).ge
  U1_le := (baseChangeSnd_preimage_U1 𝒱 c (RelPicard.LFP.stageHom R g)).ge

variable (A) in

def H1baseChangeMap : (𝒱.structureSheafSections c).H1 →ₛₗ[algebraMap R A]
    ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1 :=
  (HomOver.baseChange 𝒱 c A).H1map

def H1stageMap (g : A →ₐ[R] B) :
    ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1 →ₛₗ[g.toRingHom]
      ((𝒱.pullback c B).structureSheafSections (pullback.snd c (specMap R B))).H1 :=
  (HomOver.stage 𝒱 c g).H1map

theorem baseChange_map01_apply (y : (𝒱.cover c).A01) :
    (HomOver.baseChange 𝒱 c A).map01 y = ((pullback.fst c (specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom y := by
  rw [HomOver.map01_apply, Scheme.Hom.app_eq_appLE]
  rfl

theorem H1baseChangeMap_mk (y : (𝒱.cover c).A01) :
    H1baseChangeMap 𝒱 c A (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((HomOver.baseChange 𝒱 c A).map01 y) := rfl

theorem stage_map01_apply (g : A →ₐ[R] B) (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    (HomOver.stage 𝒱 c g).map01 f =
      ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R g)).appLE
        ((𝒱.pullback c A).U0 ⊓ (𝒱.pullback c A).U1) ((𝒱.pullback c B).U0 ⊓ (𝒱.pullback c B).U1)
        (HomOver.stage 𝒱 c g).inf_le).hom f := rfl

theorem H1stageMap_mk (g : A →ₐ[R] B) (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    H1stageMap 𝒱 c g (Submodule.Quotient.mk f) = Submodule.Quotient.mk ((HomOver.stage 𝒱 c g).map01 f) := rfl

theorem H1stageMap_H1baseChangeMap (g : A →ₐ[R] B) (x : (𝒱.structureSheafSections c).H1) :
    H1stageMap 𝒱 c g (H1baseChangeMap 𝒱 c A x) = H1baseChangeMap 𝒱 c B x := by
  rw [H1stageMap, H1baseChangeMap, H1baseChangeMap, ← HomOver.comp_H1map]
  exact HomOver.H1map_congr (baseChangeSnd_fst c (RelPicard.LFP.stageHom R g)) x

theorem H1stageMap_id (x : ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1) :
    H1stageMap 𝒱 c (AlgHom.id R A) x = x := by
  refine (HomOver.H1map_congr (f := HomOver.stage 𝒱 c (AlgHom.id R A))
    (g := HomOver.id (𝒱.pullback c A) (pullback.snd c (specMap R A))) ?_ x).trans (HomOver.id_H1map x)
  change RelPicard.baseChangeSnd c _ = 𝟙 _
  rw [← RelPicard.baseChangeSnd_id c (specMap R A)]
  congr 1
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom (RingHom.id A)) = 𝟙 _
  exact Spec.map_id _

theorem H1stageMap_comp (g : A →ₐ[R] B) (g' : B →ₐ[R] B')
    (x : ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1) :
    H1stageMap 𝒱 c g' (H1stageMap 𝒱 c g x) = H1stageMap 𝒱 c (g'.comp g) x := by
  rw [H1stageMap, H1stageMap, H1stageMap, ← HomOver.comp_H1map]
  refine HomOver.H1map_congr ?_ x
  change RelPicard.baseChangeSnd c _ ≫ RelPicard.baseChangeSnd c _ = RelPicard.baseChangeSnd c _
  rw [RelPicard.baseChangeSnd_comp]
  congr 1
  apply Subtype.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

end BaseChange

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end


