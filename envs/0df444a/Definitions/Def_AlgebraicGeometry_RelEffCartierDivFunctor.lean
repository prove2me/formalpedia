-- Prove2me | Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
-- name    : AlgebraicGeometry_RelEffCartierDivFunctor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/9aa013b8-7fc0-543b-915d-770bb409a91f
-- title:
--   Functor of relative effective divisors and universal divisors
-- statement:
--   Fix a morphism of schemes $f \colon \mathcal{C} \to S$ and an integer $r \ge 0$. Recall that a `RelEffCartierDiv f r g`, for $g \colon T \to S$, is a quasi-coherent ideal sheaf datum $I$ on the fibre product $\mathcal{C} \times_S T$ whose associated closed subscheme, composed with the projection to $T$, is finite, flat and locally of finite presentation and has flat rank exactly $r$ at every point of $T$; and that `PullsBackOver D φ hφ D'` asserts the equality of ideal sheaf data $(\varphi^{*})^{-1}$-style, namely that the comap of $D.I$ along the induced map $1_{\mathcal{C}} \times \varphi$ of fibre products equals $D'.I$, `pullbackAlong` being the canonical such pullback. This module assembles these data into a presheaf $\mathbf{Sch}^{\mathrm{op}} \to \mathbf{Type}$, `RelEffCartierDiv.functor f r`, whose value at $T$ is the type of pairs $(g, D)$ with $g \colon T \to S$ and $D$ a degree-$r$ relative divisor over $g$, and which sends $\varphi \colon T \to T'$ to $(g', D') \mapsto (\varphi \circ g'$ in diagrammatic order, the pullback of $D'$ along $\varphi)$; the functoriality rests on the identity and composition laws for `pullbackAlong`, together with a heterogeneous-equality lemma saying that the pullback along $\varphi$ does not depend on the chosen proof that $\varphi$ followed by $g'$ equals the structure morphism.
--
--   The predicate `IsUniversal Duniv`, for $y \colon Y \to S$ and $D_{\mathrm{univ}}$ of degree $r$ over $y$, says that for every $g \colon T \to S$ and every degree-$r$ divisor $D$ over $g$ there is a unique pair consisting of $\varphi \colon T \to Y$ and a witness that $\varphi$ followed by $y$ is $g$, such that $D_{\mathrm{univ}}$ pulls back to $D$ along $\varphi$. From this come the classifying morphism `lift` with its defining properties, an extensionality lemma for maps to $Y$ agreeing over $S$ and having equal pulled-back ideals, stability of universality under an isomorphism $Y'' \cong Y$ over $S$, the bijection $(T \to Y) \simeq \Sigma_g\, \mathrm{Div}^r(T,g)$, and hence a `RepresentableBy Y` structure. Conversely the value of any representation at $1_Y$ is universal, giving the equivalence: `functor f r` is representable iff some $S$-scheme carries a universal degree-$r$ divisor.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients used here — `Scheme.IdealSheafData` with its comap, the morphism properties `IsFinite`, `Flat`, `LocallyOfFinitePresentation` and flat rank, and the representability interfaces `Functor.RepresentableBy` and `Functor.IsRepresentable` — but has no functor of relative effective divisors of a morphism of schemes; that functor and the predicate `IsUniversal` are the project's own.
--
--   **Where it is used.** This is the functor-of-points formulation, over an arbitrary base $S$ and with arbitrary test schemes, of the degree-$r$ divisor problem for a relative curve $\mathcal{C} \to S$; no existence is asserted here. It lets statements about the scheme of degree-$r$ divisors be made for an arbitrary universal pair $(Y, D_{\mathrm{univ}})$, which the uniqueness clause pins down up to unique isomorphism over $S$, and it connects that formulation with the representability of the presheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelEffCartierDivFunctor.lean

import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ)

variable {f r} in

lemma pullbackAlong_heq {T T' : Scheme.{u}} {g' : T' ⟶ S} (D : RelEffCartierDiv f r g')
    (φ : T ⟶ T') {g₁ g₂ : T ⟶ S} (h₁ : φ ≫ g' = g₁) (h₂ : φ ≫ g' = g₂) :
    HEq (D.pullbackAlong φ h₁) (D.pullbackAlong φ h₂) := by
  obtain rfl : g₁ = g₂ := h₁.symm.trans h₂
  rfl

noncomputable def functor : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := Σ g : unop T ⟶ S, RelEffCartierDiv f r g
  map φ := TypeCat.ofHom fun D => ⟨φ.unop ≫ D.1, D.2.pullbackAlong φ.unop rfl⟩
  map_id T := by
    refine ConcreteCategory.hom_ext _ _ fun D => ?_
    obtain ⟨g, D⟩ := D
    change (⟨𝟙 _ ≫ g, D.pullbackAlong (𝟙 _) rfl⟩ : Σ g : unop T ⟶ S, RelEffCartierDiv f r g) = ⟨g, D⟩
    exact Sigma.ext (Category.id_comp g)
      ((D.pullbackAlong_heq (𝟙 _) rfl (Category.id_comp g)).trans (heq_of_eq D.pullbackAlong_id))
  map_comp {T T' T''} φ ψ := by
    refine ConcreteCategory.hom_ext _ _ fun D => ?_
    obtain ⟨g, D⟩ := D
    change (⟨(ψ.unop ≫ φ.unop) ≫ g, D.pullbackAlong (ψ.unop ≫ φ.unop) rfl⟩ :
        Σ g : unop T'' ⟶ S, RelEffCartierDiv f r g) =
      ⟨ψ.unop ≫ φ.unop ≫ g, (D.pullbackAlong φ.unop rfl).pullbackAlong ψ.unop rfl⟩
    exact Sigma.ext (Category.assoc _ _ _)
      ((D.pullbackAlong_heq (ψ.unop ≫ φ.unop) rfl (Category.assoc _ _ _)).trans
        (heq_of_eq (D.pullbackAlong_comp φ.unop rfl ψ.unop rfl).symm))

@[simp] lemma functor_map_fst {T T' : Scheme.{u}ᵒᵖ} (φ : T ⟶ T') (D : (RelEffCartierDiv.functor f r).obj T) :
    ((RelEffCartierDiv.functor f r).map φ D).1 = φ.unop ≫ D.1 := rfl

lemma functor_map_snd {T T' : Scheme.{u}ᵒᵖ} (φ : T ⟶ T') (D : (RelEffCartierDiv.functor f r).obj T) :
    ((RelEffCartierDiv.functor f r).map φ D).2 = D.2.pullbackAlong φ.unop rfl := rfl

lemma functor_map_apply {T T' : Scheme.{u}ᵒᵖ} (φ : T ⟶ T')
    (D : (RelEffCartierDiv.functor f r).obj T) :
    (RelEffCartierDiv.functor f r).map φ D = ⟨φ.unop ≫ D.1, D.2.pullbackAlong φ.unop rfl⟩ := rfl

variable {f r}

def IsUniversal {Y : Scheme.{u}} {y : Y ⟶ S} (Duniv : RelEffCartierDiv f r y) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (D : RelEffCartierDiv f r g),
    ∃! φ : {φ : T ⟶ Y // φ ≫ y = g}, PullsBackOver Duniv φ.1 φ.2 D

section Representability

variable {Y : Scheme.{u}} {y : Y ⟶ S}

variable {Duniv : RelEffCartierDiv f r y}

noncomputable def IsUniversal.lift (hU : Duniv.IsUniversal) {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f r g) : T ⟶ Y :=
  (hU g D).exists.choose.1

@[reassoc (attr := simp)]
lemma IsUniversal.lift_comp (hU : Duniv.IsUniversal) {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f r g) : hU.lift D ≫ y = g :=
  (hU g D).exists.choose.2

lemma IsUniversal.pullsBackOver_lift (hU : Duniv.IsUniversal) {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f r g) : PullsBackOver Duniv (hU.lift D) (hU.lift_comp D) D :=
  (hU g D).exists.choose_spec

lemma IsUniversal.pullbackAlong_lift (hU : Duniv.IsUniversal) {T : Scheme.{u}} {g : T ⟶ S}
    (D : RelEffCartierDiv f r g) : Duniv.pullbackAlong (hU.lift D) (hU.lift_comp D) = D :=
  (PullsBackOver.eq_pullbackAlong (hU.pullsBackOver_lift D)).symm

lemma IsUniversal.eq_lift (hU : Duniv.IsUniversal) {T : Scheme.{u}} {g : T ⟶ S}
    {D : RelEffCartierDiv f r g} {φ : T ⟶ Y} (hφ : φ ≫ y = g) (h : PullsBackOver Duniv φ hφ D) :
    φ = hU.lift D :=
  congrArg Subtype.val ((hU g D).unique (y₁ := ⟨φ, hφ⟩) h (hU.pullsBackOver_lift D))

@[simp] lemma IsUniversal.lift_pullbackAlong (hU : Duniv.IsUniversal) {T : Scheme.{u}}
    (φ : T ⟶ Y) : hU.lift (Duniv.pullbackAlong φ rfl) = φ :=
  (hU.eq_lift rfl (pullsBackOver_pullbackAlong Duniv φ rfl)).symm

lemma IsUniversal.hom_ext (hU : Duniv.IsUniversal) {T : Scheme.{u}} {φ ψ : T ⟶ Y}
    (hy : φ ≫ y = ψ ≫ y)
    (h : Duniv.I.comap (mapOnProdOver f φ rfl) = Duniv.I.comap (mapOnProdOver f ψ hy.symm)) :
    φ = ψ := by
  rw [← hU.lift_pullbackAlong φ]
  exact (hU.eq_lift (D := Duniv.pullbackAlong φ rfl) hy.symm h.symm).symm

theorem IsUniversal.of_iso {Y'' : Scheme.{u}} {y'' : Y'' ⟶ S} (hU : Duniv.IsUniversal) (e : Y'' ≅ Y)
    (he : e.hom ≫ y = y'') : (Duniv.pullbackAlong e.hom he).IsUniversal := by
  intro T g D

  have key : ∀ (φ : T ⟶ Y'') (hφ : φ ≫ y'' = g),
      PullsBackOver (Duniv.pullbackAlong e.hom he) φ hφ D ↔
        PullsBackOver Duniv (φ ≫ e.hom) (by rw [Category.assoc, he, hφ]) D := by
    intro φ hφ
    change ((Duniv.pullbackAlong e.hom he).pullbackAlong φ hφ).I = D.I ↔
      (Duniv.pullbackAlong (φ ≫ e.hom) _).I = D.I
    rw [Duniv.pullbackAlong_comp]
  refine ⟨⟨hU.lift D ≫ e.inv, by rw [Category.assoc, ← he, e.inv_hom_id_assoc, hU.lift_comp]⟩,
    ?_, ?_⟩
  · change PullsBackOver _ (hU.lift D ≫ e.inv) _ D
    rw [key]
    change (Duniv.pullbackAlong ((hU.lift D ≫ e.inv) ≫ e.hom) _).I = D.I
    have h : (hU.lift D ≫ e.inv) ≫ e.hom = hU.lift D := by simp
    have hc : ∀ {φ₁ φ₂ : T ⟶ Y} (_ : φ₁ = φ₂) (h₁ : φ₁ ≫ y = g) (h₂ : φ₂ ≫ y = g),
        Duniv.pullbackAlong φ₁ h₁ = Duniv.pullbackAlong φ₂ h₂ := by
      rintro _ _ rfl _ _; rfl
    rw [hc h _ (hU.lift_comp D)]
    exact hU.pullsBackOver_lift D
  · rintro ⟨ψ, hψ⟩ hPB
    apply Subtype.ext
    change ψ = hU.lift D ≫ e.inv
    rw [← hU.eq_lift _ ((key ψ hψ).1 hPB), Category.assoc, e.hom_inv_id, Category.comp_id]

noncomputable def IsUniversal.homEquiv (hU : Duniv.IsUniversal) (T : Scheme.{u}) :
    (T ⟶ Y) ≃ Σ g : T ⟶ S, RelEffCartierDiv f r g where
  toFun φ := ⟨φ ≫ y, Duniv.pullbackAlong φ rfl⟩
  invFun D := hU.lift D.2
  left_inv φ := hU.lift_pullbackAlong φ
  right_inv D := Sigma.ext (hU.lift_comp D.2)
    ((Duniv.pullbackAlong_heq _ rfl (hU.lift_comp D.2)).trans (heq_of_eq (hU.pullbackAlong_lift D.2)))

@[simp] lemma IsUniversal.homEquiv_apply (hU : Duniv.IsUniversal) {T : Scheme.{u}} (φ : T ⟶ Y) :
    hU.homEquiv T φ = ⟨φ ≫ y, Duniv.pullbackAlong φ rfl⟩ := rfl

@[simp] lemma IsUniversal.homEquiv_symm_apply (hU : Duniv.IsUniversal) {T : Scheme.{u}}
    (D : Σ g : T ⟶ S, RelEffCartierDiv f r g) : (hU.homEquiv T).symm D = hU.lift D.2 := rfl

noncomputable def IsUniversal.representableBy (hU : Duniv.IsUniversal) :
    (RelEffCartierDiv.functor f r).RepresentableBy Y where
  homEquiv {T} := hU.homEquiv T
  homEquiv_comp {T T'} φ ψ := by
    change (⟨(φ ≫ ψ) ≫ y, Duniv.pullbackAlong (φ ≫ ψ) rfl⟩ : Σ g : T ⟶ S, RelEffCartierDiv f r g) =
      ⟨φ ≫ ψ ≫ y, (Duniv.pullbackAlong ψ rfl).pullbackAlong φ rfl⟩
    exact Sigma.ext (Category.assoc _ _ _)
      ((Duniv.pullbackAlong_heq (φ ≫ ψ) rfl (Category.assoc _ _ _)).trans
        (heq_of_eq (Duniv.pullbackAlong_comp ψ rfl φ rfl).symm))

lemma IsUniversal.representableBy_homEquiv_apply (hU : Duniv.IsUniversal) {T : Scheme.{u}}
    (φ : T ⟶ Y) :
    hU.representableBy.homEquiv φ = ⟨φ ≫ y, Duniv.pullbackAlong φ rfl⟩ := rfl

theorem isUniversal_of_representableBy (e : (RelEffCartierDiv.functor f r).RepresentableBy Y) :
    (e.homEquiv (𝟙 Y)).2.IsUniversal := by
  intro T g D
  have key : ∀ φ : T ⟶ Y, e.homEquiv φ =
      ⟨φ ≫ (e.homEquiv (𝟙 Y)).1, (e.homEquiv (𝟙 Y)).2.pullbackAlong φ rfl⟩ := fun φ => by
    have h := e.homEquiv_comp φ (𝟙 Y)
    rw [Category.comp_id] at h
    exact h
  have H : (⟨e.homEquiv.symm ⟨g, D⟩ ≫ (e.homEquiv (𝟙 Y)).1,
      (e.homEquiv (𝟙 Y)).2.pullbackAlong (e.homEquiv.symm ⟨g, D⟩) rfl⟩ :
        Σ g : T ⟶ S, RelEffCartierDiv f r g) = ⟨g, D⟩ :=
    (key _).symm.trans (e.homEquiv.apply_symm_apply _)
  have h1 : e.homEquiv.symm ⟨g, D⟩ ≫ (e.homEquiv (𝟙 Y)).1 = g := congrArg Sigma.fst H
  refine ⟨⟨e.homEquiv.symm ⟨g, D⟩, h1⟩, ?_, ?_⟩
  · have h3 : (e.homEquiv (𝟙 Y)).2.pullbackAlong (e.homEquiv.symm ⟨g, D⟩) h1 = D :=
      eq_of_heq (((e.homEquiv (𝟙 Y)).2.pullbackAlong_heq _ h1 rfl).trans (Sigma.ext_iff.1 H).2)
    exact congrArg RelEffCartierDiv.I h3
  · rintro ⟨ψ, hψ⟩ hPB
    apply Subtype.ext
    apply e.homEquiv.injective
    rw [Equiv.apply_symm_apply, key ψ]
    exact Sigma.ext hψ (((e.homEquiv (𝟙 Y)).2.pullbackAlong_heq ψ rfl hψ).trans
      (heq_of_eq (PullsBackOver.eq_pullbackAlong hPB).symm))

variable (f r) in

theorem isRepresentable_functor_iff :
    (RelEffCartierDiv.functor f r).IsRepresentable ↔
      ∃ (Y : Scheme.{u}) (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y), Duniv.IsUniversal := by
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    exact ⟨Y, _, _, isUniversal_of_representableBy e⟩
  · rintro ⟨Y, y, Duniv, hU⟩
    exact ⟨Y, ⟨hU.representableBy⟩⟩

end Representability

end RelEffCartierDiv

end AlgebraicGeometry


