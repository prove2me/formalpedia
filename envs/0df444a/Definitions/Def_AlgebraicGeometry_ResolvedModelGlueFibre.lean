-- Prove2me | Definitions.Def_AlgebraicGeometry_ResolvedModelGlueFibre
-- name    : AlgebraicGeometry_ResolvedModelGlueFibre
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/2d250a29-be0a-567c-8f4f-e409c5ce9abd
-- title:
--   Fibres of chart pullbacks and exceptional points of the glue
-- statement:
--   The first group of declarations concerns a pullback square of schemes $U \times_S C$ attached to $f : U \to S$ and $\rho : C \to S$ and a point $x \in U$. For the Mathlib notion of scheme-theoretic fibre (the pullback along $\operatorname{Spec}$ of the residue field at a point), `fiberMap f ρ x` is the canonical morphism from the fibre of $\mathrm{pr}_1 : U\times_S C \to U$ over $x$ to the fibre of $\rho$ over $f(x)$; `isPullback_fiberMap` exhibits it as the base change of $\operatorname{Spec}$ of the residue-field map $\kappa(f(x)) \to \kappa(x)$, whence `isIso_fiberMap` and `fiberIso`: when that residue-field map is an isomorphism, the two fibres are isomorphic, compatibly with the inclusions into $U\times_S C$ and $C$ and with the maps to $\operatorname{Spec}\kappa$. Under the extra hypothesis that $x$ is the only point of $U$ with image $f(x)$, `existsUnique_snd_eq_of_apply_eq` shows every $o \in C$ with $\rho(o) = f(x)$ has a unique preimage in $U\times_S C$; `liftPt` names it, with its projections computed, its injectivity in $o$, and a homeomorphism between the set-theoretic fibres $\mathrm{pr}_1^{-1}(x)$ and $\rho^{-1}(f(x))$ compatible with $\mathrm{pr}_2$. Also included: a criterion for $\mathrm{pr}_1$ of a further base change along a morphism factoring through $\operatorname{Spec}\kappa(f(x))$ to be an isomorphism.
--
--   The second group specialises this to a `ChartInput` $C$ over $X$, where $Y_n = U_n \times_{S_n} \mathrm{Res}_n$, $q_n, g_n$ are the two projections and $\mathrm{glued}$ is the colimit scheme with structure morphism $\mathrm{toDR}$. Here `xU n` is $x_n$ viewed in $U_n$, `vertex n` $= f_n(x_n)$, and `f_apply_eq_iff` deduces from the clause $f_n(y)\in V^c_n \iff y \ne x_n$ that $x_n$ is the unique point over the vertex. Given that $f_n$ induces an isomorphism of residue fields at $x_n$ (a clause of `f_node`), `ε` is the resulting isomorphism of fibres, `liftY` the unique point of $Y_n$ with prescribed image $o$ in $\mathrm{Res}_n$ over the vertex, and `exPt`, `edgePt'` its images in $\mathrm{glued}$, indexed in the latter case by $\mathrm{Fin}(\mathrm{thick}\ n)$; these are injective in $o$, lie over $x_n$, and differ for differing $n$. Specialisation is transported: if $o'$ lies in the closure of $o$ in $\mathrm{Res}_n$ then `liftY` and `exPt` of $o'$ lie in the closures of those of $o$, with a corollary about membership in the support of an ideal sheaf whose support is the closure of a single exceptional point. Further lemmas identify $g_n^{-1}(\rho_n^{-1}(\mathrm{vertex}))$ with $q_n^{-1}(x_n)$, give the range of the composite fibre inclusion, show $q_n$'s fibre inclusion at $x_n$ is a closed immersion when $\{x_n\}$ is closed in $X$, and prove $n \mapsto x_n$ injective. Finally, a group of commutative-algebra lemmas: for an étale morphism the stalk map sends the maximal ideal onto the maximal ideal, hence carries a pair of ideals with sum the maximal ideal, and a pair of germs generating the maximal ideal, to data with the same property upstairs.
--
--   **Relation to Mathlib.** The fibre apparatus used throughout (`Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`, `fiberHomeo`, `residueFieldMap`) is Mathlib's; `ChartInput`, `GlueInput` and their derived objects are the project's own. The statement that an étale morphism's stalk maps carry maximal ideal onto maximal ideal is derived from Mathlib's formal unramifiedness and essential finite type for stalk maps.
--
--   **Where it is used.** These lemmas serve the construction, by gluing étale-local charts, of a resolved model of a curve with node-like points: they identify the exceptional fibre of the glued scheme above each marked point $x_n$ with the fibre of the chosen model $\rho_n : \mathrm{Res}_n \to S_n$ over the vertex, and provide the named points above the nodes together with their specialisation behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ResolvedModelGlueFibre.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ResolvedModelGlue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 200000

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace V3Glue.Aux.Layer0.W6

variable {U C S : Scheme.{u}} (f : U ⟶ S) (ρ : C ⟶ S) (x : U)

noncomputable def fiberMap : (pullback.fst f ρ).fiber x ⟶ ρ.fiber (f x) :=
  pullback.map _ _ _ _ (pullback.snd f ρ) (Spec.map (f.residueFieldMap x)) f
    (IsPullback.of_hasPullback f ρ).w (by simp)

theorem isPullback_fiberMap :
    IsPullback (fiberMap f ρ x) ((pullback.fst f ρ).fiberToSpecResidueField x)
      (ρ.fiberToSpecResidueField (f x)) (Spec.map (f.residueFieldMap x)) :=
  isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f ρ).flip x

theorem isIso_fiberMap [IsIso (f.residueFieldMap x)] : IsIso (fiberMap f ρ x) :=
  (isPullback_fiberMap f ρ x).isIso_fst_of_isIso

theorem fiberMap_fiberι :
    fiberMap f ρ x ≫ ρ.fiberι (f x) = (pullback.fst f ρ).fiberι x ≫ pullback.snd f ρ :=
  pullback.lift_fst _ _ _

theorem fiberMap_fiberToSpecResidueField :
    fiberMap f ρ x ≫ ρ.fiberToSpecResidueField (f x) =
      (pullback.fst f ρ).fiberToSpecResidueField x ≫ Spec.map (f.residueFieldMap x) :=
  (isPullback_fiberMap f ρ x).w

theorem preimage_snd_preimage_eq_preimage_fst_singleton (hiii : ∀ y : U, f y = f x ↔ y = x) :
    (pullback.snd f ρ) ⁻¹' (ρ ⁻¹' {f x}) = (pullback.fst f ρ) ⁻¹' ({x} : Set U) := by
  ext z
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  have hz : f (pullback.fst f ρ z) = ρ (pullback.snd f ρ z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  rw [← hz]
  exact hiii _

theorem existsUnique_snd_eq_of_apply_eq [IsIso (f.residueFieldMap x)] (hiii : ∀ y : U, f y = f x ↔ y = x)
    (o : C) (ho : ρ o = f x) :
    ∃! y : ↥(pullback f ρ), pullback.snd f ρ y = o := by
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := ρ) x o ho.symm
  refine ⟨z, hz2, fun z' hz' => ?_⟩

  have hx' : pullback.fst f ρ z' = x := (hiii _).mp (by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hz', ho])
  have hmem : ∀ w : ↥(pullback f ρ), pullback.fst f ρ w = x → w ∈ Set.range ((pullback.fst f ρ).fiberι x) := fun w hw => by
    rw [Scheme.Hom.range_fiberι]; exact hw
  obtain ⟨w, rfl⟩ := hmem z hz1
  obtain ⟨w', rfl⟩ := hmem z' hx'
  haveI := isIso_fiberMap f ρ x

  have key : ∀ v, pullback.snd f ρ ((pullback.fst f ρ).fiberι x v) = ρ.fiberι (f x) (fiberMap f ρ x v) := fun v => by
    rw [← Scheme.Hom.comp_apply, ← fiberMap_fiberι, Scheme.Hom.comp_apply]
  have h2 : fiberMap f ρ x w' = fiberMap f ρ x w := by
    apply (ρ.fiberι (f x)).isEmbedding.injective
    rw [← key, ← key, hz', hz2]
  have h3 : w' = w := by
    have := congrArg (fun v => (inv (fiberMap f ρ x)) v) h2
    simpa [← Scheme.Hom.comp_apply] using this
  rw [h3]

noncomputable def liftPt [IsIso (f.residueFieldMap x)] (hiii : ∀ y : U, f y = f x ↔ y = x)
    (o : C) (ho : ρ o = f x) : ↥(pullback f ρ) :=
  (existsUnique_snd_eq_of_apply_eq f ρ x hiii o ho).choose

theorem snd_liftPt [IsIso (f.residueFieldMap x)] (hiii : ∀ y : U, f y = f x ↔ y = x) (o : C) (ho : ρ o = f x) :
    pullback.snd f ρ (liftPt f ρ x hiii o ho) = o :=
  (existsUnique_snd_eq_of_apply_eq f ρ x hiii o ho).choose_spec.1

theorem fst_liftPt [IsIso (f.residueFieldMap x)] (hiii : ∀ y : U, f y = f x ↔ y = x) (o : C) (ho : ρ o = f x) :
    pullback.fst f ρ (liftPt f ρ x hiii o ho) = x :=
  (hiii _).mp (by rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, snd_liftPt, ho])

theorem liftPt_injective [IsIso (f.residueFieldMap x)] (hiii : ∀ y : U, f y = f x ↔ y = x)
    {ι : Type*} (o : ι → C) (ho : ∀ i, ρ (o i) = f x) (hinj : Function.Injective o) :
    Function.Injective (fun i => liftPt f ρ x hiii (o i) (ho i)) := by
  intro i j h
  apply hinj
  have := congrArg (fun y => pullback.snd f ρ y) h
  simpa only [snd_liftPt] using this

theorem isIso_pullback_fst_of_over_point
    (hfib : IsIso (f.fiberToSpecResidueField (f x)))
    {F : Scheme.{u}} (i : F ⟶ C) (t : F ⟶ Spec (S.residueField (f x)))
    (ht : i ≫ ρ = t ≫ S.fromSpecResidueField (f x)) :
    IsIso (pullback.fst i (pullback.snd f ρ)) := by

  have hbig : IsPullback (pullback.snd i (pullback.snd f ρ) ≫ pullback.fst f ρ) (pullback.fst i (pullback.snd f ρ)) f (i ≫ ρ) :=
    (IsPullback.of_hasPullback i (pullback.snd f ρ)).flip.paste_horiz (IsPullback.of_hasPullback f ρ)
  rw [ht] at hbig

  let h₁₁ : pullback i (pullback.snd f ρ) ⟶ pullback f (S.fromSpecResidueField (f x)) :=
    pullback.lift (pullback.snd i (pullback.snd f ρ) ≫ pullback.fst f ρ) (pullback.fst i (pullback.snd f ρ) ≫ t)
      (by simpa only [Category.assoc] using hbig.w)
  have s : IsPullback (h₁₁ ≫ pullback.fst f (S.fromSpecResidueField (f x))) (pullback.fst i (pullback.snd f ρ)) f
      (t ≫ S.fromSpecResidueField (f x)) := by
    simp only [h₁₁, pullback.lift_fst]
    exact hbig
  have hsq : IsPullback h₁₁ (pullback.fst i (pullback.snd f ρ)) (f.fiberToSpecResidueField (f x)) t :=
    s.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (S.fromSpecResidueField (f x)))
  exact hsq.isIso_snd_of_isIso hfib

theorem fst_apply_eq_of_snd_mem_range (hiii : ∀ y : U, f y = f x ↔ y = x)
    {F : Scheme.{u}} (i : F ⟶ C) (hF : ∀ z : F, ρ (i z) = f x) (y : ↥(pullback f ρ))
    (hy : pullback.snd f ρ y ∈ Set.range i) : pullback.fst f ρ y = x := by
  obtain ⟨z, hz⟩ := hy
  apply (hiii _).mp
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← hz, hF]

theorem exists_homeomorph_preimage_singleton [IsIso (f.residueFieldMap x)] :
    ∃ h : ↥((pullback.fst f ρ) ⁻¹' ({x} : Set U)) ≃ₜ ↥(ρ ⁻¹' ({f x} : Set S)),
      ∀ y, ((h y : ↥(ρ ⁻¹' ({f x} : Set S))) : C) = pullback.snd f ρ (y : ↥(pullback f ρ)) := by
  haveI := isIso_fiberMap f ρ x
  refine ⟨((pullback.fst f ρ).fiberHomeo x).symm.trans
    ((Scheme.homeoOfIso (asIso (fiberMap f ρ x))).trans (ρ.fiberHomeo (f x))), fun y => ?_⟩
  simp only [Homeomorph.trans_apply, Scheme.Hom.fiberHomeo_apply, Scheme.coe_homeoOfIso, asIso_hom]
  rw [← Scheme.Hom.comp_apply, fiberMap_fiberι, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_fiberHomeo_symm]

noncomputable def fiberIso [IsIso (f.residueFieldMap x)] : (pullback.fst f ρ).fiber x ≅ ρ.fiber (f x) :=
  haveI := isIso_fiberMap f ρ x
  asIso (fiberMap f ρ x)

@[simp] theorem fiberIso_hom [IsIso (f.residueFieldMap x)] : (fiberIso f ρ x).hom = fiberMap f ρ x := rfl

end V3Glue.Aux.Layer0.W6

noncomputable section

namespace V3Glue.ChartInput

open V3Glue.Aux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry V3Glue.Aux.Layer0

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

def xU (n : N) : ↥(C.U n) := ⟨C.x n, C.x_mem_U n⟩

@[simp] theorem xU_coe (n : N) : ((C.xU n : ↥(C.U n)) : X) = C.x n := rfl

def vertex (n : N) : C.S n := (C.f n).base (C.xU n)

theorem vertex_def (n : N) : C.vertex n = C.f n (C.xU n) := rfl

theorem f_apply_eq_iff (n : N) (y : ↥(C.U n)) : C.f n y = C.f n (C.xU n) ↔ y = C.xU n := by
  constructor
  · intro h
    have hx : (C.f n).base (C.xU n) ∉ C.Vc n := fun hm => ((C.f_mem_Vc_iff n (C.xU n)).mp hm) rfl
    have hy : ¬ ((y : X) ≠ C.x n) := fun hne => hx (by
      have := (C.f_mem_Vc_iff n y).mpr hne
      change (C.f n).base y ∈ C.Vc n at this
      rwa [show (C.f n).base y = (C.f n).base (C.xU n) from h] at this)
    exact Subtype.ext (not_not.mp hy)
  · rintro rfl; rfl

theorem f_xU_not_mem_Vc (n : N) : (C.f n).base (C.xU n) ∉ C.Vc n :=
  fun hm => ((C.f_mem_Vc_iff n (C.xU n)).mp hm) rfl

theorem setOf_q_eq_preimage_xU (n : N) :
    {y : C.Y n | ((C.q n).base y).1 = C.x n} = (C.q n).base ⁻¹' {C.xU n} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem f_apply_eq_vertex_iff (n : N) (y : ↥(C.U n)) : C.f n y = C.vertex n ↔ y = C.xU n :=
  C.f_apply_eq_iff n y

section fibre

variable (n : N) (hRF : IsIso ((C.f n).residueFieldMap (C.xU n)))

include hRF in

theorem eq_of_g_eq (y y' : C.Y n) (h : C.g n y = C.g n y') (hv : C.ρ n (C.g n y) = C.vertex n) : y = y' := by
  haveI := hRF
  obtain ⟨w, -, huniq⟩ := W6.existsUnique_snd_eq_of_apply_eq (C.f n) (C.ρ n) (C.xU n) (C.f_apply_eq_iff n) _ hv
  exact (huniq y rfl).trans (huniq y' h.symm).symm

def ε : (C.q n).fiber (C.xU n) ≅ (C.ρ n).fiber (C.vertex n) :=
  haveI := hRF
  W6.fiberIso (C.f n) (C.ρ n) (C.xU n)

theorem ε_hom : (C.ε n hRF).hom = W6.fiberMap (C.f n) (C.ρ n) (C.xU n) := rfl

@[reassoc]
theorem ε_hom_fiberι :
    (C.ε n hRF).hom ≫ (C.ρ n).fiberι (C.vertex n) = (C.q n).fiberι (C.xU n) ≫ C.g n :=
  W6.fiberMap_fiberι (C.f n) (C.ρ n) (C.xU n)

@[reassoc]
theorem ε_inv_fiberι :
    (C.ε n hRF).inv ≫ (C.q n).fiberι (C.xU n) ≫ C.g n = (C.ρ n).fiberι (C.vertex n) := by
  rw [← C.ε_hom_fiberι n hRF, Iso.inv_hom_id_assoc]

@[reassoc]
theorem ε_hom_fiberToSpecResidueField :
    (C.ε n hRF).hom ≫ (C.ρ n).fiberToSpecResidueField (C.vertex n) =
      (C.q n).fiberToSpecResidueField (C.xU n) ≫ Spec.map ((C.f n).residueFieldMap (C.xU n)) :=
  W6.fiberMap_fiberToSpecResidueField (C.f n) (C.ρ n) (C.xU n)

theorem isPullback_ε :
    IsPullback (C.ε n hRF).hom ((C.q n).fiberToSpecResidueField (C.xU n))
      ((C.ρ n).fiberToSpecResidueField (C.vertex n)) (Spec.map ((C.f n).residueFieldMap (C.xU n))) :=
  W6.isPullback_fiberMap (C.f n) (C.ρ n) (C.xU n)

omit hRF in

theorem ρ_fiberι_apply (z : ↥((C.ρ n).fiber (C.vertex n))) :
    C.ρ n ((C.ρ n).fiberι (C.vertex n) z) = C.vertex n := by
  have h : (C.ρ n).fiberι (C.vertex n) z ∈ (C.ρ n) ⁻¹' {C.vertex n} := by
    rw [← Scheme.Hom.range_fiberι]; exact Set.mem_range_self z
  simpa using h

theorem fiberι_ε_inv_apply (z : ↥((C.ρ n).fiber (C.vertex n))) :
    (C.q n).fiberι (C.xU n) ((C.ε n hRF).inv z) =
      haveI := hRF
      W6.liftPt (C.f n) (C.ρ n) (C.xU n) (C.f_apply_eq_iff n) ((C.ρ n).fiberι (C.vertex n) z)
        (C.ρ_fiberι_apply n z) := by
  haveI := hRF
  have hρ := C.ρ_fiberι_apply n z
  obtain ⟨y, hy, huniq⟩ := W6.existsUnique_snd_eq_of_apply_eq (C.f n) (C.ρ n) (C.xU n) (C.f_apply_eq_iff n) _ hρ
  have h1 : pullback.snd (C.f n) (C.ρ n) ((C.q n).fiberι (C.xU n) ((C.ε n hRF).inv z)) =
      (C.ρ n).fiberι (C.vertex n) z := by
    change (C.g n) _ = _
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, C.ε_inv_fiberι n hRF]
  have h2 := W6.snd_liftPt (C.f n) (C.ρ n) (C.xU n) (C.f_apply_eq_iff n) _ hρ
  exact (huniq _ h1).trans (huniq _ h2).symm

theorem preimage_g_preimage_ρ_eq :
    (C.g n).base ⁻¹' ((C.ρ n).base ⁻¹' {C.vertex n}) = (C.q n).base ⁻¹' {C.xU n} :=
  W6.preimage_snd_preimage_eq_preimage_fst_singleton (C.f n) (C.ρ n) (C.xU n) (C.f_apply_eq_iff n)

include hRF in

theorem exists_homeomorph_exc :
    ∃ h : ↥((C.q n).base ⁻¹' ({C.xU n} : Set ↥(C.U n))) ≃ₜ ↥((C.ρ n).base ⁻¹' ({C.vertex n} : Set (C.S n))),
      ∀ y, ((h y : ↥((C.ρ n).base ⁻¹' ({C.vertex n} : Set (C.S n)))) : C.Res n) = C.g n (y : C.Y n) :=
  haveI := hRF
  W6.exists_homeomorph_preimage_singleton (C.f n) (C.ρ n) (C.xU n)

include hRF in

theorem range_fiberι_g :
    Set.range ((C.q n).fiberι (C.xU n) ≫ C.g n).base = (C.ρ n).base ⁻¹' {C.vertex n} := by
  rw [← C.ε_hom_fiberι n hRF, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (C.ε n hRF).hom.surjective, Set.image_univ]
  exact (C.ρ n).range_fiberι _

omit hRF in

theorem isClosedImmersion_fiberι_q (hx : IsClosed ({C.x n} : Set X)) :
    IsClosedImmersion ((C.q n).fiberι (C.xU n)) := by
  have hx' : IsClosed ({C.xU n} : Set ((C.U n : X.Opens) : Scheme.{0})) := by
    have : ({C.xU n} : Set ((C.U n : X.Opens) : Scheme.{0})) = (C.U n).ι.base ⁻¹' {C.x n} := by
      ext y
      change y = C.xU n ↔ (C.U n).ι y ∈ ({C.x n} : Set X)
      rw [Scheme.Opens.ι_apply, Set.mem_singleton_iff]
      exact ⟨fun h => h ▸ rfl, fun h => Subtype.ext h⟩
    rw [this]; exact hx.preimage (C.U n).ι.continuous
  haveI := (isClosed_singleton_iff_isClosedImmersion (X := ((C.U n : X.Opens) : Scheme.{0})) (x := C.xU n)).mp hx'
  delta Scheme.Hom.fiberι Scheme.Hom.fiber
  infer_instance

end fibre

end V3Glue.ChartInput

end

noncomputable section

namespace V3Glue.ChartInput

open V3Glue.Aux

open V3Glue.Aux.Layer0

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

theorem x_injective : Function.Injective C.x := by
  intro n m h
  by_contra hnm
  exact C.x_not_mem_U n m (Ne.symm hnm) (h ▸ C.x_mem_U n)

section lift

variable (n : N) (hRF : IsIso ((C.f n).residueFieldMap (C.xU n)))

def liftY (o : C.Res n) (ho : C.ρ n o = C.vertex n) : C.Y n :=
  haveI := hRF
  W6.liftPt (C.f n) (C.ρ n) (C.xU n) (C.f_apply_eq_iff n) o ho

theorem snd_liftY (o : C.Res n) (ho : C.ρ n o = C.vertex n) :
    (pullback.snd (C.f n) (C.ρ n)) (C.liftY n hRF o ho) = o := by
  haveI := hRF
  exact W6.snd_liftPt (C.f n) (C.ρ n) (C.xU n) (C.f_apply_eq_iff n) o ho

theorem q_liftY (o : C.Res n) (ho : C.ρ n o = C.vertex n) :
    C.q n (C.liftY n hRF o ho) = C.xU n := by
  haveI := hRF
  exact W6.fst_liftPt (C.f n) (C.ρ n) (C.xU n) (C.f_apply_eq_iff n) o ho

theorem liftY_injective {ι : Type*} (o : ι → C.Res n) (ho : ∀ i, C.ρ n (o i) = C.vertex n)
    (hinj : Function.Injective o) : Function.Injective (fun i => C.liftY n hRF (o i) (ho i)) := by
  haveI := hRF
  exact W6.liftPt_injective (C.f n) (C.ρ n) (C.xU n) (C.f_apply_eq_iff n) o ho hinj

theorem g_liftY (o : C.Res n) (ho : C.ρ n o = C.vertex n) : C.g n (C.liftY n hRF o ho) = o :=
  C.snd_liftY n hRF o ho

theorem eq_liftY_of_g_eq (o : C.Res n) (ho : C.ρ n o = C.vertex n) (y : C.Y n) (hy : C.g n y = o) :
    y = C.liftY n hRF o ho :=
  C.eq_of_g_eq n hRF y _ (hy.trans (C.g_liftY n hRF o ho).symm) (by rw [hy]; exact ho)

theorem liftY_fiberι_eq_ε_inv (z : ↥((C.ρ n).fiber (C.vertex n))) :
    C.liftY n hRF ((C.ρ n).fiberι (C.vertex n) z) (C.ρ_fiberι_apply n z) =
      (C.q n).fiberι (C.xU n) ((C.ε n hRF).inv z) :=
  (C.fiberι_ε_inv_apply n hRF z).symm

def exPt (o : C.Res n) (ho : C.ρ n o = C.vertex n) : C.toGlueInput.glued :=
  C.toGlueInput.ιY n (C.liftY n hRF o ho)

theorem exPt_def (o : C.Res n) (ho : C.ρ n o = C.vertex n) :
    C.exPt n hRF o ho = C.toGlueInput.ιY n (C.liftY n hRF o ho) := rfl

theorem toDR_exPt (o : C.Res n) (ho : C.ρ n o = C.vertex n) :
    C.toGlueInput.toDR (C.exPt n hRF o ho) = C.x n := by
  rw [exPt_def, ← Scheme.Hom.comp_apply, C.toGlueInput.ιY_toDR]
  change ((C.U n).ι) (C.q n (C.liftY n hRF o ho)) = C.x n
  rw [q_liftY]
  rfl

theorem exPt_mem_range_ιY (o : C.Res n) (ho : C.ρ n o = C.vertex n) :
    C.exPt n hRF o ho ∈ Set.range (C.toGlueInput.ιY n) := ⟨_, rfl⟩

theorem exPt_injective {ι : Type*} (o : ι → C.Res n) (ho : ∀ i, C.ρ n (o i) = C.vertex n)
    (hinj : Function.Injective o) : Function.Injective (fun i => C.exPt n hRF (o i) (ho i)) := by
  intro i j h
  exact C.liftY_injective n hRF o ho hinj ((C.toGlueInput.ιY n).isOpenEmbedding.injective h)

theorem toDR_eq_of_mem_closure_exPt (hx : IsClosed ({C.x n} : Set X))
    (o : C.Res n) (ho : C.ρ n o = C.vertex n) {y : C.toGlueInput.glued}
    (hy : y ∈ closure ({C.exPt n hRF o ho} : Set C.toGlueInput.glued)) : C.toGlueInput.toDR y = C.x n := by
  have hsub : closure ({C.exPt n hRF o ho} : Set C.toGlueInput.glued) ⊆ C.toGlueInput.toDR.base ⁻¹' {C.x n} :=
    closure_minimal (by rw [Set.singleton_subset_iff]; exact C.toDR_exPt n hRF o ho)
      (hx.preimage C.toGlueInput.toDR.continuous)
  exact hsub hy

end lift

theorem exPt_ne_of_ne {n m : N} (h : n ≠ m) (hn : IsIso ((C.f n).residueFieldMap (C.xU n)))
    (hm : IsIso ((C.f m).residueFieldMap (C.xU m)))
    (o : C.Res n) (ho : C.ρ n o = C.vertex n) (o' : C.Res m) (ho' : C.ρ m o' = C.vertex m) :
    C.exPt n hn o ho ≠ C.exPt m hm o' ho' := by
  intro heq
  have := congrArg (fun y => C.toGlueInput.toDR y) heq
  simp only [toDR_exPt] at this
  exact h (C.x_injective this)

section edge

variable (hRF : ∀ n, IsIso ((C.f n).residueFieldMap (C.xU n)))
  (oRes : ∀ n, Fin (C.thick n) → C.Res n) (hoRes : ∀ n d, C.ρ n (oRes n d) = C.vertex n)

def edgePt' (n : N) (d : Fin (C.thick n)) : C.toGlueInput.glued := C.exPt n (hRF n) (oRes n d) (hoRes n d)

theorem toDR_edgePt' (n : N) (d : Fin (C.thick n)) : C.toGlueInput.toDR (C.edgePt' hRF oRes hoRes n d) = C.x n :=
  C.toDR_exPt n (hRF n) _ _

theorem edgePt'_injective (hinj : ∀ n, Function.Injective (oRes n)) :
    Function.Injective (fun e : Σ n, Fin (C.thick n) => C.edgePt' hRF oRes hoRes e.1 e.2) := by
  rintro ⟨n, d⟩ ⟨m, d'⟩ h
  dsimp only at h
  by_cases hnm : n = m
  · subst hnm
    have := C.exPt_injective n (hRF n) (oRes n) (hoRes n) (hinj n) h
    subst this
    rfl
  · exact absurd h (C.exPt_ne_of_ne hnm (hRF n) (hRF m) _ _ _ _)

theorem edgePt'_mem_range_ιY (n : N) (d : Fin (C.thick n)) : C.edgePt' hRF oRes hoRes n d ∈ Set.range (C.toGlueInput.ιY n) :=
  ⟨_, rfl⟩

end edge

end V3Glue.ChartInput

namespace V3Glue.ChartInput

open V3Glue.Aux

open V3Glue.Aux.Layer0

variable {X : Scheme.{0}} {N : Type} (C : ChartInput X N)

section closure

variable (n : N) (hRF : IsIso ((C.f n).residueFieldMap (C.xU n)))

theorem liftY_mem_closure_liftY (o o' : C.Res n)
    (ho : C.ρ n o = C.vertex n) (ho' : C.ρ n o' = C.vertex n)
    (hcl : o' ∈ closure ({o} : Set (C.Res n))) :
    C.liftY n hRF o' ho' ∈ closure ({C.liftY n hRF o ho} : Set (C.Y n)) := by
  haveI := hRF

  obtain ⟨h, hh⟩ := W6.exists_homeomorph_preimage_singleton (C.f n) (C.ρ n) (C.xU n)

  have hmem : ∀ (o₁ : C.Res n) (ho₁ : C.ρ n o₁ = C.vertex n),
      (C.liftY n hRF o₁ ho₁ : ↥(pullback (C.f n) (C.ρ n))) ∈ (pullback.fst (C.f n) (C.ρ n)) ⁻¹' ({C.xU n} : Set _) :=
    fun o₁ ho₁ => C.q_liftY n hRF o₁ ho₁
  have himg : ∀ (o₁ : C.Res n) (ho₁ : C.ρ n o₁ = C.vertex n),
      h ⟨C.liftY n hRF o₁ ho₁, hmem o₁ ho₁⟩ = ⟨o₁, ho₁⟩ := fun o₁ ho₁ =>
    Subtype.ext ((hh _).trans (C.snd_liftY n hRF o₁ ho₁))

  have h1 : (⟨o', ho'⟩ : ↥((C.ρ n) ⁻¹' ({C.f n (C.xU n)} : Set _))) ∈
      closure ({⟨o, ho⟩} : Set ↥((C.ρ n) ⁻¹' ({C.f n (C.xU n)} : Set _))) := by
    rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage, Set.image_singleton]
    exact hcl

  have h2 : (⟨C.liftY n hRF o' ho', hmem o' ho'⟩ : ↥((pullback.fst (C.f n) (C.ρ n)) ⁻¹' ({C.xU n} : Set _))) ∈
      closure ({⟨C.liftY n hRF o ho, hmem o ho⟩} : Set _) := by
    rw [← himg o' ho', ← himg o ho, ← Set.image_singleton (f := h), ← h.image_closure] at h1
    obtain ⟨z, hz, hzeq⟩ := h1
    have hz' := h.injective hzeq
    subst hz'
    exact hz

  have := h2
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.mem_preimage, Set.image_singleton] at this
  exact this

theorem exPt_mem_closure_exPt (o o' : C.Res n)
    (ho : C.ρ n o = C.vertex n) (ho' : C.ρ n o' = C.vertex n)
    (hcl : o' ∈ closure ({o} : Set (C.Res n))) :
    C.exPt n hRF o' ho' ∈ closure ({C.exPt n hRF o ho} : Set C.toGlueInput.glued) := by
  have h4 := image_closure_subset_closure_image (C.toGlueInput.ιY n).continuous (s := {C.liftY n hRF o ho})
    ⟨_, C.liftY_mem_closure_liftY n hRF o o' ho ho' hcl, rfl⟩
  rwa [Set.image_singleton] at h4

theorem exPt_mem_support_of_support_eq_closure (o o' : C.Res n)
    (ho : C.ρ n o = C.vertex n) (ho' : C.ρ n o' = C.vertex n)
    (hcl : o' ∈ closure ({o} : Set (C.Res n)))
    (I : C.toGlueInput.glued.IdealSheafData)
    (hI : (I.support : Set C.toGlueInput.glued) = closure {C.exPt n hRF o ho}) :
    C.exPt n hRF o' ho' ∈ (I.support : Set C.toGlueInput.glued) := by
  rw [hI]; exact C.exPt_mem_closure_exPt n hRF o o' ho ho' hcl

end closure

end V3Glue.ChartInput

namespace V3Glue.Aux

open IsLocalRing

theorem Ideal.map_sup_eq_maximalIdeal_of_map_maximalIdeal_eq {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) (h : (maximalIdeal A).map φ = maximalIdeal B)
    {I J : Ideal A} (hIJ : I ⊔ J = maximalIdeal A) : I.map φ ⊔ J.map φ = maximalIdeal B := by
  rw [← Ideal.map_sup, hIJ, h]

theorem Etale.map_stalkMap_maximalIdeal {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] (y : Y) :
    (maximalIdeal (X.presheaf.stalk (g.base y))).map (g.stalkMap y).hom = maximalIdeal (Y.presheaf.stalk y) := by
  letI := (g.stalkMap y).hom.toAlgebra
  haveI : Algebra.FormallyUnramified (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y) :=
    FormallyUnramified.stalkMap g y
  haveI : Algebra.EssFiniteType (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y) :=
    LocallyOfFiniteType.stalkMap g y
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk (g.base y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap y).hom)
  exact Algebra.FormallyUnramified.map_maximalIdeal

theorem Etale.map_stalkMap_sup_eq_maximalIdeal {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] (y : Y)
    {I J : Ideal (X.presheaf.stalk (g.base y))} (hIJ : I ⊔ J = maximalIdeal (X.presheaf.stalk (g.base y))) :
    I.map (g.stalkMap y).hom ⊔ J.map (g.stalkMap y).hom = maximalIdeal (Y.presheaf.stalk y) :=
  Ideal.map_sup_eq_maximalIdeal_of_map_maximalIdeal_eq _ (Etale.map_stalkMap_maximalIdeal g y) hIJ

theorem map_stalkMap_sup_eq_maximalIdeal_of_map_maximalIdeal_eq {X Y : Scheme.{u}} (g : Y ⟶ X) (y : Y)
    (hmax : (maximalIdeal (X.presheaf.stalk (g.base y))).map (g.stalkMap y).hom = maximalIdeal (Y.presheaf.stalk y))
    {I J : Ideal (X.presheaf.stalk (g.base y))} (hIJ : I ⊔ J = maximalIdeal (X.presheaf.stalk (g.base y))) :
    I.map (g.stalkMap y).hom ⊔ J.map (g.stalkMap y).hom = maximalIdeal (Y.presheaf.stalk y) :=
  Ideal.map_sup_eq_maximalIdeal_of_map_maximalIdeal_eq _ hmax hIJ

theorem Etale.span_germ_app_eq_maximalIdeal {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] (y : Y)
    (V : X.Opens) (hV : g.base y ∈ V) (a b : Γ(X, V))
    (hab : Ideal.span {(X.presheaf.germ V (g.base y) hV).hom a, (X.presheaf.germ V (g.base y) hV).hom b} =
      maximalIdeal (X.presheaf.stalk (g.base y))) :
    Ideal.span {(Y.presheaf.germ (g ⁻¹ᵁ V) y hV).hom ((g.app V).hom a), (Y.presheaf.germ (g ⁻¹ᵁ V) y hV).hom ((g.app V).hom b)} =
      maximalIdeal (Y.presheaf.stalk y) := by
  have key : ∀ c : Γ(X, V), (Y.presheaf.germ (g ⁻¹ᵁ V) y hV).hom ((g.app V).hom c) =
      (g.stalkMap y).hom ((X.presheaf.germ V (g.base y) hV).hom c) := fun c => by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap]
  rw [key, key, ← Etale.map_stalkMap_maximalIdeal g y, ← hab, Ideal.map_span, Set.image_pair]

end V3Glue.Aux

end


