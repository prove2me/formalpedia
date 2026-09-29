-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/522cfd05-7e43-5a46-baa5-cd8481f091a8

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct TopologicalSpace Opposite

noncomputable section

namespace P2mPullbackSectionsSol

section Res

variable {X : Scheme.{u}} (M : X.Modules)

theorem map_map {W₁ W₂ W₃ : X.Opens} (i : W₁ ⟶ W₂) (j : W₂ ⟶ W₃) (k : W₁ ⟶ W₃) (y : Γ(M, W₃)) :
    M.presheaf.map i.op (M.presheaf.map j.op y) = M.presheaf.map k.op y := by
  rw [Subsingleton.elim k (i ≫ j), op_comp, M.presheaf.map_comp]; rfl

theorem map_self {W : X.Opens} (i : W ⟶ W) (y : Γ(M, W)) : M.presheaf.map i.op y = y := by
  rw [Subsingleton.elim i (𝟙 W), op_id, M.presheaf.map_id]; rfl

theorem fmap_map {W₁ W₂ W₃ : X.Opens} (i : W₁ ⟶ W₂) (j : W₂ ⟶ W₃) (k : W₁ ⟶ W₃) (g : Γ(X, W₃)) :
    X.presheaf.map i.op (X.presheaf.map j.op g) = X.presheaf.map k.op g := by
  rw [Subsingleton.elim k (i ≫ j), op_comp, X.presheaf.map_comp]; rfl

theorem fmap_self {W : X.Opens} (i : W ⟶ W) (g : Γ(X, W)) : X.presheaf.map i.op g = g := by
  rw [Subsingleton.elim i (𝟙 W), op_id, X.presheaf.map_id]; rfl

theorem bijective_map_of_eq {W₁ W₂ : X.Opens} (h : W₁ = W₂) (i : W₁ ⟶ W₂) :
    Function.Bijective (M.presheaf.map i.op) := by
  subst h
  rw [Subsingleton.elim i (𝟙 _), op_id, M.presheaf.map_id]
  exact Function.bijective_id

theorem app_map {N : X.Modules} (φ : M ⟶ N) {W₁ W₂ : X.Opens} (i : W₁ ⟶ W₂) (x : Γ(M, W₂)) :
    φ.app W₁ (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app W₂ x) :=
  PresheafOfModules.naturality_apply φ.val i.op x

end Res

section EvalFrame

variable {X : Scheme.{u}} {L P : X.Modules} {V : X.Opens} {s : Γ(L, V)}

theorem eval_injective (hs : Scheme.Modules.IsFrameOn s V)
    (hP : ∀ W : X.Opens, Function.Injective (P.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op)) :
    Function.Injective fun f : L ⟶ P => f.app V s := by

  suffices h0 : ∀ f : L ⟶ P, f.app V s = 0 → f = 0 by
    intro f₁ f₂ h
    have := h0 (f₁ - f₂) (by
      rw [Scheme.Modules.Hom.sub_app]
      exact sub_eq_zero.mpr h)
    exact sub_eq_zero.mp this
  intro f hf
  apply Scheme.Modules.hom_ext
  intro W
  ext x
  change f.app W x = 0
  apply hP W
  rw [map_zero, ← app_map]
  obtain ⟨g, hg⟩ := (hs.bijective (inf_le_right : W ⊓ V ≤ V) inf_le_right).2
    (L.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op x)
  rw [← hg, Scheme.Modules.Hom.app_smul, app_map, hf, map_zero, smul_zero]

variable (P s) in

def liftFun (hs : Scheme.Modules.IsFrameOn s V)
    (hP : ∀ W : X.Opens, Function.Bijective (P.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op))
    (y : Γ(P, V)) (W : X.Opens) (x : Γ(L, W)) : Γ(P, W) :=
  (Equiv.ofBijective _ (hP W)).symm
    ((Equiv.ofBijective _ (hs.bijective (inf_le_right : W ⊓ V ≤ V) inf_le_right)).symm
        (L.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op x) •
      P.presheaf.map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op y)

def coef (hs : Scheme.Modules.IsFrameOn s V) (W : X.Opens) (x : Γ(L, W)) : Γ(X, W ⊓ V) :=
  (Equiv.ofBijective _ (hs.bijective (inf_le_right : W ⊓ V ≤ V) inf_le_right)).symm
    (L.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op x)

theorem coef_spec (hs : Scheme.Modules.IsFrameOn s V) (W : X.Opens) (x : Γ(L, W)) :
    coef hs W x • L.presheaf.map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op s =
      L.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op x :=
  Equiv.ofBijective_apply_symm_apply _ (hs.bijective (inf_le_right : W ⊓ V ≤ V) inf_le_right) _

theorem coef_unique (hs : Scheme.Modules.IsFrameOn s V) (W : X.Opens) (x : Γ(L, W)) (g : Γ(X, W ⊓ V))
    (hg : g • L.presheaf.map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op s =
      L.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op x) :
    g = coef hs W x :=
  (hs.bijective (inf_le_right : W ⊓ V ≤ V) inf_le_right).1 (hg.trans (coef_spec hs W x).symm)

theorem coef_add (hs : Scheme.Modules.IsFrameOn s V) (W : X.Opens) (x₁ x₂ : Γ(L, W)) :
    coef hs W (x₁ + x₂) = coef hs W x₁ + coef hs W x₂ := by
  refine (coef_unique hs W _ _ ?_).symm
  rw [add_smul, coef_spec, coef_spec, map_add]

theorem coef_smul (hs : Scheme.Modules.IsFrameOn s V) (W : X.Opens) (a : Γ(X, W)) (x : Γ(L, W)) :
    coef hs W (a • x) = X.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op a * coef hs W x := by
  refine (coef_unique hs W _ _ ?_).symm
  rw [mul_smul, coef_spec, Scheme.Modules.map_smul]

theorem map_coef (hs : Scheme.Modules.IsFrameOn s V) {W₁ W₂ : X.Opens} (i : W₁ ⟶ W₂) (x : Γ(L, W₂)) :
    X.presheaf.map (homOfLE (inf_le_inf_right V i.le : W₁ ⊓ V ≤ W₂ ⊓ V)).op (coef hs W₂ x) =
      coef hs W₁ (L.presheaf.map i.op x) := by
  refine coef_unique hs W₁ _ _ ?_
  have h := congrArg (L.presheaf.map (homOfLE (inf_le_inf_right V i.le : W₁ ⊓ V ≤ W₂ ⊓ V)).op)
    (coef_spec hs W₂ x)
  rw [Scheme.Modules.map_smul, map_map, map_map L _ _ (homOfLE inf_le_left ≫ i)] at h
  rw [h, op_comp, L.presheaf.map_comp]
  rfl

theorem liftFun_spec (hs : Scheme.Modules.IsFrameOn s V)
    (hP : ∀ W : X.Opens, Function.Bijective (P.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op))
    (y : Γ(P, V)) (W : X.Opens) (x : Γ(L, W)) :
    P.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op (liftFun P s hs hP y W x) =
      coef hs W x • P.presheaf.map (homOfLE (inf_le_right : W ⊓ V ≤ V)).op y :=
  Equiv.ofBijective_apply_symm_apply _ (hP W) _

theorem liftFun_add (hs : Scheme.Modules.IsFrameOn s V)
    (hP : ∀ W : X.Opens, Function.Bijective (P.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op))
    (y : Γ(P, V)) (W : X.Opens) (x₁ x₂ : Γ(L, W)) :
    liftFun P s hs hP y W (x₁ + x₂) = liftFun P s hs hP y W x₁ + liftFun P s hs hP y W x₂ := by
  apply (hP W).1
  rw [map_add, liftFun_spec, liftFun_spec, liftFun_spec, coef_add, add_smul]

theorem liftFun_smul (hs : Scheme.Modules.IsFrameOn s V)
    (hP : ∀ W : X.Opens, Function.Bijective (P.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op))
    (y : Γ(P, V)) (W : X.Opens) (a : Γ(X, W)) (x : Γ(L, W)) :
    liftFun P s hs hP y W (a • x) = a • liftFun P s hs hP y W x := by
  apply (hP W).1
  rw [Scheme.Modules.map_smul, liftFun_spec, liftFun_spec, coef_smul, mul_smul]

theorem liftFun_map (hs : Scheme.Modules.IsFrameOn s V)
    (hP : ∀ W : X.Opens, Function.Bijective (P.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op))
    (y : Γ(P, V)) {W₁ W₂ : X.Opens} (i : W₁ ⟶ W₂) (x : Γ(L, W₂)) :
    liftFun P s hs hP y W₁ (L.presheaf.map i.op x) = P.presheaf.map i.op (liftFun P s hs hP y W₂ x) := by
  apply (hP W₁).1
  rw [liftFun_spec, map_map P _ _ (homOfLE (inf_le_left.trans i.le)),
    ← map_map P (homOfLE (inf_le_inf_right V i.le : W₁ ⊓ V ≤ W₂ ⊓ V))
    (homOfLE (inf_le_left : W₂ ⊓ V ≤ W₂)) (homOfLE (inf_le_left.trans i.le)), liftFun_spec,
    Scheme.Modules.map_smul, map_map, map_coef]

variable (P s) in

private def _root_.P2mPullbackSectionsSol.lift (hs : Scheme.Modules.IsFrameOn s V)
    (hP : ∀ W : X.Opens, Function.Bijective (P.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op))
    (y : Γ(P, V)) : L ⟶ P :=
  ⟨{ app := fun W => ModuleCat.ofHom
        { toFun := liftFun P s hs hP y W.unop
          map_add' := liftFun_add hs hP y W.unop
          map_smul' := liftFun_smul hs hP y W.unop }
     naturality := fun {W₁ W₂} i => by
        ext x
        exact liftFun_map hs hP y i.unop x }⟩

p2m_export "P2mPullbackSectionsSol" "lift"
theorem lift_app (hs : Scheme.Modules.IsFrameOn s V)
    (hP : ∀ W : X.Opens, Function.Bijective (P.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op))
    (y : Γ(P, V)) (W : X.Opens) (x : Γ(L, W)) :
    (lift P s hs hP y).app W x = liftFun P s hs hP y W x := rfl

theorem lift_app_self (hs : Scheme.Modules.IsFrameOn s V)
    (hP : ∀ W : X.Opens, Function.Bijective (P.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op))
    (y : Γ(P, V)) : (lift P s hs hP y).app V s = y := by
  rw [lift_app]
  apply (hP V).1
  rw [liftFun_spec]
  have h1 : coef hs V s = 1 := (coef_unique hs V s 1 (by rw [one_smul])).symm
  rw [h1, one_smul]

theorem eval_bijective (hs : Scheme.Modules.IsFrameOn s V)
    (hP : ∀ W : X.Opens, Function.Bijective (P.presheaf.map (homOfLE (inf_le_left : W ⊓ V ≤ W)).op)) :
    Function.Bijective fun f : L ⟶ P => f.app V s :=
  ⟨eval_injective hs fun W => (hP W).1, fun y => ⟨lift P s hs hP y, lift_app_self hs hP y⟩⟩

end EvalFrame

section Pull

variable {X Z : Scheme.{u}} (p : Z ⟶ X) (L : X.Modules)

abbrev pb : Z.Modules := (Scheme.Modules.pullback p).obj L

abbrev unitHom : L ⟶ (Scheme.Modules.pushforward p).obj (pb p L) :=
  (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app L

def eta (V : X.Opens) (s : Γ(L, V)) : Γ(pb p L, p ⁻¹ᵁ V) := (unitHom p L).app V s

theorem eta_add (V : X.Opens) (s₁ s₂ : Γ(L, V)) : eta p L V (s₁ + s₂) = eta p L V s₁ + eta p L V s₂ :=
  map_add _ s₁ s₂

theorem eta_smul (V : X.Opens) (a : Γ(X, V)) (s : Γ(L, V)) : eta p L V (a • s) = p.app V a • eta p L V s := by
  unfold eta
  rw [Scheme.Modules.Hom.app_smul]
  rfl

theorem map_eta {V₁ V₂ : X.Opens} (i : V₁ ⟶ V₂) (k : p ⁻¹ᵁ V₁ ⟶ p ⁻¹ᵁ V₂) (s : Γ(L, V₂)) :
    (pb p L).presheaf.map k.op (eta p L V₂ s) = eta p L V₁ (L.presheaf.map i.op s) := by
  rw [Subsingleton.elim k ((Opens.map p.base).map i)]
  exact (app_map L (unitHom p L) i s).symm

theorem evalPull_eq (Q : Z.Modules) (F : pb p L ⟶ Q) (V : X.Opens) (s : Γ(L, V)) :
    F.app (p ⁻¹ᵁ V) (eta p L V s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv L Q F).app V s := rfl

theorem evalPull_bijective {V : X.Opens} {s : Γ(L, V)} (hs : Scheme.Modules.IsFrameOn s V) (Q : Z.Modules)
    (hQ : ∀ W : X.Opens, Function.Bijective
      (Q.presheaf.map ((Opens.map p.base).map (homOfLE (inf_le_left : W ⊓ V ≤ W))).op)) :
    Function.Bijective fun F : pb p L ⟶ Q => F.app (p ⁻¹ᵁ V) (eta p L V s) := by
  have h := eval_bijective (P := (Scheme.Modules.pushforward p).obj Q) hs hQ
  exact h.comp ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv L Q).bijective

variable (O : Z.Opens)

abbrev OO : Z.Modules :=
  (Scheme.Modules.pushforward O.ι).obj (SheafOfModules.unit (O : Scheme.{u}).ringCatSheaf)

def toFun' (W : Z.Opens) (x : Γ(OO O, W)) : Γ((O : Scheme.{u}), O.ι ⁻¹ᵁ W) := x

def ofFun' (W : Z.Opens) (x : Γ((O : Scheme.{u}), O.ι ⁻¹ᵁ W)) : Γ(OO O, W) := x

@[scoped simp] theorem toFun'_ofFun' (W : Z.Opens) (x : Γ((O : Scheme.{u}), O.ι ⁻¹ᵁ W)) :
    toFun' O W (ofFun' O W x) = x := rfl

theorem toFun'_injective (W : Z.Opens) : Function.Injective (toFun' O W) := fun _ _ h => h

theorem toFun'_smul (W : Z.Opens) (g : Γ(Z, W)) (x : Γ(OO O, W)) :
    toFun' O W (g • x) = O.ι.app W g * toFun' O W x := rfl

theorem toFun'_zero (W : Z.Opens) : toFun' O W 0 = 0 := rfl

theorem toFun'_map {W₁ W₂ : Z.Opens} (i : W₁ ⟶ W₂) (x : Γ(OO O, W₂)) :
    toFun' O W₁ ((OO O).presheaf.map i.op x) =
      (O : Scheme.{u}).presheaf.map ((Opens.map O.ι.base).map i).op (toFun' O W₂ x) := rfl

theorem OO_map_bijective {W₁ W₂ : Z.Opens} (i : W₁ ⟶ W₂) (h : O.ι ⁻¹ᵁ W₁ = O.ι ⁻¹ᵁ W₂) :
    Function.Bijective ((OO O).presheaf.map i.op) :=
  bijective_map_of_eq (X := (O : Scheme.{u})) (SheafOfModules.unit (O : Scheme.{u}).ringCatSheaf) h
    ((Opens.map O.ι.base).map i)

theorem ιapp_injective {W : Z.Opens} (hW : W ≤ O) : Function.Injective (O.ι.app W) := by
  haveI := Scheme.Hom.isIso_app O.ι W (by rwa [Scheme.Opens.opensRange_ι])
  exact (ConcreteCategory.bijective_of_isIso (O.ι.app W)).1

theorem ιapp_bijective : Function.Bijective (O.ι.app O) := by
  haveI := Scheme.Hom.isIso_app O.ι O (by rw [Scheme.Opens.opensRange_ι])
  exact ConcreteCategory.bijective_of_isIso (O.ι.app O)

theorem ιapp_map {W₁ W₂ : Z.Opens} (i : W₁ ⟶ W₂) (g : Γ(Z, W₂)) :
    O.ι.app W₁ (Z.presheaf.map i.op g) =
      (O : Scheme.{u}).presheaf.map ((Opens.map O.ι.base).map i).op (O.ι.app W₂ g) := by
  have := O.ι.naturality i.op
  exact congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(Z, W₂) → _)) this) g

theorem preimage_inf_eq (V W : X.Opens) :
    (p ⁻¹ᵁ V).ι ⁻¹ᵁ (p ⁻¹ᵁ (W ⊓ V)) = (p ⁻¹ᵁ V).ι ⁻¹ᵁ (p ⁻¹ᵁ W) := by
  ext x
  constructor
  · intro hx; exact hx.1
  · intro hx; exact ⟨hx, x.2⟩

theorem bijective_smul_eta {V : X.Opens} {s : Γ(L, V)} (hs : Scheme.Modules.IsFrameOn s V)
    (hN : Scheme.Modules.IsInvertible (pb p L)) :
    Function.Bijective fun g : Γ(Z, p ⁻¹ᵁ V) => g • eta p L V s := by
  set O : Z.Opens := p ⁻¹ᵁ V with hO
  set t : Γ(pb p L, O) := eta p L V s with ht

  have hQ : ∀ W : X.Opens, Function.Bijective
      ((OO O).presheaf.map ((Opens.map p.base).map (homOfLE (inf_le_left : W ⊓ V ≤ W))).op) :=
    fun W => OO_map_bijective O _ (preimage_inf_eq p V W)

  obtain ⟨F₁, hF₁⟩ := (evalPull_bijective p L hs (OO O) hQ).2 (ofFun' O O 1)
  have hF₁' : toFun' O O (F₁.app O t) = 1 := congrArg (toFun' O O) hF₁
  refine ⟨fun g₁ g₂ h => ?_, fun y => ?_⟩
  ·
    have h' : F₁.app O (g₁ • t) = F₁.app O (g₂ • t) := congrArg (F₁.app O) h
    rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul] at h'
    have h'' := congrArg (toFun' O O) h'
    rw [toFun'_smul, toFun'_smul, hF₁', mul_one, mul_one] at h''
    exact (ιapp_bijective O).1 h''
  ·
    obtain ⟨g, hg⟩ := (ιapp_bijective O).2 (toFun' O O (F₁.app O y))
    refine ⟨g, ?_⟩
    change g • t = y

    have hfr : ∀ z : O, ∃ (U : Z.Opens), (z : Z) ∈ U ∧
        ∃ u : Γ(pb p L, U), Scheme.Modules.IsFrameOn u U := by
      intro z
      obtain ⟨U, hzU, ⟨e⟩⟩ := hN.1 (z : Z)
      exact ⟨U, hzU, Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit U e⟩
    choose U hzU u hu using hfr
    let W : O → Z.Opens := fun z => U z ⊓ O
    have hcover : O ≤ ⨆ z : O, W z := fun x hx =>
      Opens.mem_iSup.mpr ⟨⟨x, hx⟩, ⟨hzU ⟨x, hx⟩, hx⟩⟩
    let F : TopCat.Sheaf Ab Z := ⟨(pb p L).presheaf, Scheme.Modules.isSheaf _⟩
    refine TopCat.Sheaf.eq_of_locally_eq' F W O (fun z => homOfLE inf_le_right) hcover (g • t) y fun z => ?_
    change (pb p L).presheaf.map (homOfLE (inf_le_right : W z ≤ O)).op (g • t) =
      (pb p L).presheaf.map (homOfLE (inf_le_right : W z ≤ O)).op y

    have hu' : Scheme.Modules.IsFrameOn ((pb p L).presheaf.map (homOfLE (inf_le_left : W z ≤ U z)).op (u z))
        (W z) := ((hu z).map (homOfLE inf_le_left)).mono inf_le_left
    have hbij := hu'.bijective (le_refl (W z)) le_rfl
    rw [map_self] at hbij
    set u' := (pb p L).presheaf.map (homOfLE (inf_le_left : W z ≤ U z)).op (u z) with hu'def
    clear_value u'
    obtain ⟨c, hc⟩ := hbij.2 ((pb p L).presheaf.map (homOfLE (inf_le_right : W z ≤ O)).op t)
    obtain ⟨d, hd⟩ := hbij.2 ((pb p L).presheaf.map (homOfLE (inf_le_right : W z ≤ O)).op y)
    change c • u' = _ at hc
    change d • u' = _ at hd
    have e1 : F₁.app (W z) ((pb p L).presheaf.map (homOfLE (inf_le_right : W z ≤ O)).op t) =
        (OO O).presheaf.map (homOfLE (inf_le_right : W z ≤ O)).op (F₁.app O t) := app_map _ F₁ _ t
    have e2 : F₁.app (W z) ((pb p L).presheaf.map (homOfLE (inf_le_right : W z ≤ O)).op y) =
        (OO O).presheaf.map (homOfLE (inf_le_right : W z ≤ O)).op (F₁.app O y) := app_map _ F₁ _ y

    set a := toFun' O (W z) (F₁.app (W z) u') with ha
    have h1 : O.ι.app (W z) c * a = 1 := by
      have := congrArg (toFun' O (W z)) (congrArg (F₁.app (W z)) hc)
      rw [Scheme.Modules.Hom.app_smul, toFun'_smul, e1, toFun'_map, hF₁', map_one] at this
      exact this

    have h2 : O.ι.app (W z) (Z.presheaf.map (homOfLE (inf_le_right : W z ≤ O)).op g) =
        O.ι.app (W z) d * a := by
      have := congrArg (toFun' O (W z)) (congrArg (F₁.app (W z)) hd)
      rw [Scheme.Modules.Hom.app_smul, toFun'_smul, e2, toFun'_map] at this
      rw [ιapp_map, hg]
      exact this.symm

    have h3 : Z.presheaf.map (homOfLE (inf_le_right : W z ≤ O)).op g * c = d := by
      apply ιapp_injective O (inf_le_right : W z ≤ O)
      rw [map_mul, h2, mul_assoc, mul_comm a, h1, mul_one]
    rw [Scheme.Modules.map_smul, ← hc, ← hd, ← mul_smul, h3]

end Pull

theorem isLocalizedModule_powers_of_comap {A B M N : Type*} [CommRing A] [CommRing B] [AddCommGroup M]
    [AddCommGroup N] [Module B M] [Module B N] [Module A M] [Module A N] (φ : A →+* B)
    (hM : ∀ (a : A) (m : M), a • m = φ a • m) (hN : ∀ (a : A) (n : N), a • n = φ a • n) (r : A)
    (f : M →ₗ[B] N) [h : IsLocalizedModule (Submonoid.powers (φ r)) f] (g : M →ₗ[A] N)
    (hfg : ∀ x, g x = f x) : IsLocalizedModule (Submonoid.powers r) g := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have hu := h.map_units ⟨φ r ^ n, n, rfl⟩
    rw [Module.End.isUnit_iff] at hu
    have e : (fun y : N => r ^ n • y) = fun y : N => φ r ^ n • y := funext fun y => by rw [hN, map_pow]
    convert hu using 1
    exact e
  · intro y
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers (φ r)) f y
    refine ⟨⟨x, ⟨r ^ n, n, rfl⟩⟩, ?_⟩
    change r ^ n • y = g x
    rw [hfg, hN, map_pow]
    exact hx
  · intro x₁ x₂ hx
    rw [hfg, hfg] at hx
    obtain ⟨⟨_, n, rfl⟩, hc⟩ := h.exists_of_eq hx
    refine ⟨⟨r ^ n, n, rfl⟩, ?_⟩
    change r ^ n • x₁ = r ^ n • x₂
    rw [hM, hM, map_pow]
    exact hc

section Affine

variable {X Z : Scheme.{u}} (p : Z ⟶ X) (L : X.Modules) (U : X.Opens)

@[reducible] def algAB : Algebra Γ(X, U) Γ(Z, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra

@[reducible] def modAN : Module Γ(X, U) Γ(pb p L, p ⁻¹ᵁ U) :=
  Module.compHom Γ(pb p L, p ⁻¹ᵁ U) (p.app U).hom

attribute [local instance] algAB modAN

theorem algebraMap_AB (a : Γ(X, U)) : algebraMap Γ(X, U) Γ(Z, p ⁻¹ᵁ U) a = p.app U a := rfl

theorem smul_AN (a : Γ(X, U)) (n : Γ(pb p L, p ⁻¹ᵁ U)) : a • n = p.app U a • n := rfl

scoped instance isScalarTower_ABN : IsScalarTower Γ(X, U) Γ(Z, p ⁻¹ᵁ U) Γ(pb p L, p ⁻¹ᵁ U) :=
  ⟨fun a b n => by
    change (p.app U a * b) • n = p.app U a • (b • n)
    rw [mul_smul]⟩

scoped instance smulCommClass_ABN : SMulCommClass Γ(X, U) Γ(Z, p ⁻¹ᵁ U) Γ(pb p L, p ⁻¹ᵁ U) :=
  ⟨fun a b n => by
    change p.app U a • (b • n) = b • (p.app U a • n)
    rw [smul_smul, smul_smul, mul_comm]⟩

scoped instance smulCommClass_BAN : SMulCommClass Γ(Z, p ⁻¹ᵁ U) Γ(X, U) Γ(pb p L, p ⁻¹ᵁ U) :=
  SMulCommClass.symm _ _ _

def thetaFix (b : Γ(Z, p ⁻¹ᵁ U)) : Γ(L, U) →ₗ[Γ(X, U)] Γ(pb p L, p ⁻¹ᵁ U) where
  toFun s := b • eta p L U s
  map_add' s₁ s₂ := by
    rw [eta_add, smul_add]
  map_smul' a s := by
    change b • eta p L U (a • s) = p.app U a • (b • eta p L U s)
    rw [eta_smul, smul_smul, smul_smul, mul_comm]

def thetaBilin : Γ(Z, p ⁻¹ᵁ U) →ₗ[Γ(Z, p ⁻¹ᵁ U)] (Γ(L, U) →ₗ[Γ(X, U)] Γ(pb p L, p ⁻¹ᵁ U)) where
  toFun := thetaFix p L U
  map_add' b₁ b₂ := by
    ext s
    exact add_smul b₁ b₂ (eta p L U s)
  map_smul' c b := by
    ext s
    exact mul_smul c b (eta p L U s)

def theta : Γ(Z, p ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(L, U) →ₗ[Γ(Z, p ⁻¹ᵁ U)] Γ(pb p L, p ⁻¹ᵁ U) :=
  TensorProduct.AlgebraTensorModule.lift (thetaBilin p L U)

theorem theta_tmul (b : Γ(Z, p ⁻¹ᵁ U)) (s : Γ(L, U)) : theta p L U (b ⊗ₜ s) = b • eta p L U s :=
  TensorProduct.AlgebraTensorModule.lift_tmul _ b s

@[reducible] def modAZW (W : Z.Opens) (h : W ≤ p ⁻¹ᵁ U) : Module Γ(X, U) Γ(Z, W) :=
  Module.compHom Γ(Z, W) (p.appLE U W h).hom

@[reducible] def modANW (W : Z.Opens) (h : W ≤ p ⁻¹ᵁ U) : Module Γ(X, U) Γ(pb p L, W) :=
  Module.compHom Γ(pb p L, W) (p.appLE U W h).hom

theorem appLE_apply (W : Z.Opens) (h : W ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) :
    p.appLE U W h a = Z.presheaf.map (homOfLE h).op (p.app U a) := rfl

def resB (W : Z.Opens) (h : W ≤ p ⁻¹ᵁ U) :
    letI := modAZW p U W h
    Γ(Z, p ⁻¹ᵁ U) →ₗ[Γ(X, U)] Γ(Z, W) :=
  letI := modAZW p U W h
  { toFun := Z.presheaf.map (homOfLE h).op
    map_add' := fun x y => map_add _ x y
    map_smul' := fun a x => by
      change Z.presheaf.map (homOfLE h).op (p.app U a * x) = p.appLE U W h a * _
      rw [map_mul, appLE_apply] }

def resN (W : Z.Opens) (h : W ≤ p ⁻¹ᵁ U) :
    letI := modANW p L U W h
    Γ(pb p L, p ⁻¹ᵁ U) →ₗ[Γ(X, U)] Γ(pb p L, W) :=
  letI := modANW p L U W h
  { toFun := (pb p L).presheaf.map (homOfLE h).op
    map_add' := fun x y => map_add _ x y
    map_smul' := fun a x => by
      change (pb p L).presheaf.map (homOfLE h).op (p.app U a • x) = p.appLE U W h a • _
      rw [Scheme.Modules.map_smul, appLE_apply] }

theorem isLocalizedModule_resB_of_eq (hpU : IsAffineOpen (p ⁻¹ᵁ U)) (r : Γ(X, U)) (W : Z.Opens)
    (h : W ≤ p ⁻¹ᵁ U) (hW : W = Z.basicOpen (p.app U r)) :
    letI := modAZW p U W h
    IsLocalizedModule (Submonoid.powers r) (resB p U W h) := by
  subst hW
  letI := modAZW p U (Z.basicOpen (p.app U r)) h
  haveI : IsLocalization.Away (p.app U r) Γ(Z, Z.basicOpen (p.app U r)) := hpU.isLocalization_basicOpen _
  haveI : IsLocalizedModule (Submonoid.powers (p.app U r))
      (Algebra.linearMap (Z.presheaf.obj (op (p ⁻¹ᵁ U))) (Z.presheaf.obj (op (Z.basicOpen (p.app U r))))) :=
    (isLocalizedModule_iff_isLocalization' _ _).mpr inferInstance
  refine isLocalizedModule_powers_of_comap (p.app U).hom (fun a m => rfl) (fun a n => rfl) r
    (Algebra.linearMap (Z.presheaf.obj (op (p ⁻¹ᵁ U))) (Z.presheaf.obj (op (Z.basicOpen (p.app U r)))))
    (resB p U _ h) fun x => rfl

@[reducible] def modBO (N : Z.Modules) (O : Z.Opens) (f : Γ(Z, O)) : Module Γ(Z, O) Γ(N, Z.basicOpen f) :=
  Module.compHom Γ(N, Z.basicOpen f) (algebraMap Γ(Z, O) Γ(Z, Z.basicOpen f))

def resBO (N : Z.Modules) (O : Z.Opens) (f : Γ(Z, O)) :
    letI := modBO N O f
    Γ(N, O) →ₗ[Γ(Z, O)] Γ(N, Z.basicOpen f) :=
  letI := modBO N O f
  { toFun := N.presheaf.map (homOfLE (Z.basicOpen_le f)).op
    map_add' := fun x y => map_add _ x y
    map_smul' := fun a x => Scheme.Modules.map_smul N (homOfLE (Z.basicOpen_le f)) a x }

theorem isLocalizedModule_resBO (N : Z.Modules) (O : Z.Opens) (f : Γ(Z, O)) (hN : Scheme.Modules.IsInvertible N)
    (hO : IsAffineOpen O) :
    letI := modBO N O f
    IsLocalizedModule (Submonoid.powers f) (resBO N O f) := by
  letI := modBO N O f
  haveI : IsLocalization.Away f Γ(Z, Z.basicOpen f) := hO.isLocalization_basicOpen f
  obtain ⟨h1, h2⟩ :=
    (OModulePresheaf.isQuasicoherent_ofModules_of_locallyTrivial Z.toSpecΓ N hN.1) ⟨O, hO⟩ f
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have hu : IsUnit (algebraMap Γ(Z, O) Γ(Z, Z.basicOpen f) (f ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit f).pow n
    have := hu.smul_bijective (β := Γ(N, Z.basicOpen f))
    exact this
  · intro y
    obtain ⟨n, x, hx⟩ := h1 y
    exact ⟨⟨x, ⟨f ^ n, n, rfl⟩⟩, hx.symm⟩
  · intro x₁ x₂ h
    have h0 : N.presheaf.map (homOfLE (Z.basicOpen_le f)).op (x₁ - x₂) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr h
    obtain ⟨n, hn⟩ := h2 (x₁ - x₂) h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, ← sub_eq_zero, ← smul_sub]
    exact hn

theorem isLocalizedModule_resN_of_eq (hpU : IsAffineOpen (p ⁻¹ᵁ U)) (hN : Scheme.Modules.IsInvertible (pb p L))
    (r : Γ(X, U)) (W : Z.Opens) (h : W ≤ p ⁻¹ᵁ U) (hW : W = Z.basicOpen (p.app U r)) :
    letI := modANW p L U W h
    IsLocalizedModule (Submonoid.powers r) (resN p L U W h) := by
  subst hW
  letI := modANW p L U (Z.basicOpen (p.app U r)) h
  letI := modBO (pb p L) (p ⁻¹ᵁ U) (p.app U r)
  haveI := isLocalizedModule_resBO (pb p L) (p ⁻¹ᵁ U) (p.app U r) hN hpU
  refine isLocalizedModule_powers_of_comap (p.app U).hom (fun a m => rfl) (fun a n => rfl) r
    (resBO (pb p L) (p ⁻¹ᵁ U) (p.app U r)) (resN p L U _ h) fun x => rfl

theorem pre_le (r : Γ(X, U)) : p ⁻¹ᵁ X.basicOpen r ≤ p ⁻¹ᵁ U := fun _ hx => X.basicOpen_le r hx

@[reducible] def modAZ (r : Γ(X, U)) : Module Γ(X, U) Γ(Z, p ⁻¹ᵁ X.basicOpen r) :=
  modAZW p U (p ⁻¹ᵁ X.basicOpen r) (pre_le p U r)

@[reducible] def modANr (r : Γ(X, U)) : Module Γ(X, U) Γ(pb p L, p ⁻¹ᵁ X.basicOpen r) :=
  modANW p L U (p ⁻¹ᵁ X.basicOpen r) (pre_le p U r)

attribute [local instance] modAZ modANr modBO

theorem smul_AZ (r : Γ(X, U)) (a : Γ(X, U)) (b : Γ(Z, p ⁻¹ᵁ X.basicOpen r)) :
    a • b = p.appLE U (p ⁻¹ᵁ X.basicOpen r) (pre_le p U r) a * b := rfl

theorem smul_ANr (r : Γ(X, U)) (a : Γ(X, U)) (n : Γ(pb p L, p ⁻¹ᵁ X.basicOpen r)) :
    a • n = p.appLE U (p ⁻¹ᵁ X.basicOpen r) (pre_le p U r) a • n := rfl

theorem smul_BO (r : Γ(X, U)) (a : Γ(X, U)) (m : Γ(L, X.basicOpen r)) :
    a • m = X.presheaf.map (homOfLE (X.basicOpen_le r)).op a • m := rfl

theorem app_res (r : Γ(X, U)) (a : Γ(X, U)) :
    p.app (X.basicOpen r) (X.presheaf.map (homOfLE (X.basicOpen_le r)).op a) =
      p.appLE U (p ⁻¹ᵁ X.basicOpen r) (pre_le p U r) a := by
  have h := p.map_appLE (le_refl (p ⁻¹ᵁ X.basicOpen r)) (homOfLE (X.basicOpen_le r)).op
  rw [← Scheme.Hom.app_eq_appLE] at h
  exact congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(X, U) → _)) h) a

def thetaLoc (r : Γ(X, U)) :
    Γ(Z, p ⁻¹ᵁ X.basicOpen r) ⊗[Γ(X, U)] Γ(L, X.basicOpen r) →ₗ[Γ(X, U)] Γ(pb p L, p ⁻¹ᵁ X.basicOpen r) :=
  TensorProduct.lift
    (LinearMap.mk₂ Γ(X, U) (fun b m => b • eta p L (X.basicOpen r) m)
      (fun b₁ b₂ m => add_smul b₁ b₂ _)
      (fun a b m => mul_smul _ _ _)
      (fun b m₁ m₂ => by
        show b • eta p L (X.basicOpen r) (m₁ + m₂) = b • eta p L (X.basicOpen r) m₁ + b • eta p L (X.basicOpen r) m₂
        rw [eta_add, smul_add])
      (fun a b m => by
        show b • eta p L (X.basicOpen r) (X.presheaf.map (homOfLE (X.basicOpen_le r)).op a • m) =
          p.appLE U (p ⁻¹ᵁ X.basicOpen r) (pre_le p U r) a • (b • eta p L (X.basicOpen r) m)
        rw [eta_smul, app_res, smul_smul, smul_smul, mul_comm]))

theorem thetaLoc_tmul (r : Γ(X, U)) (b : Γ(Z, p ⁻¹ᵁ X.basicOpen r)) (m : Γ(L, X.basicOpen r)) :
    thetaLoc p L U r (b ⊗ₜ m) = b • eta p L (X.basicOpen r) m :=
  TensorProduct.lift.tmul b m

def resT (r : Γ(X, U)) :
    Γ(Z, p ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(L, U) →ₗ[Γ(X, U)] Γ(Z, p ⁻¹ᵁ X.basicOpen r) ⊗[Γ(X, U)] Γ(L, X.basicOpen r) :=
  TensorProduct.map (resB p U (p ⁻¹ᵁ X.basicOpen r) (pre_le p U r)) (resBO L U r)

def thetaA : Γ(Z, p ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(L, U) →ₗ[Γ(X, U)] Γ(pb p L, p ⁻¹ᵁ U) :=
  (theta p L U).restrictScalars Γ(X, U)

theorem thetaA_apply (x : Γ(Z, p ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(L, U)) : thetaA p L U x = theta p L U x := rfl

theorem thetaLoc_comp_resT (r : Γ(X, U)) :
    thetaLoc p L U r ∘ₗ resT p L U r = resN p L U (p ⁻¹ᵁ X.basicOpen r) (pre_le p U r) ∘ₗ thetaA p L U := by
  refine TensorProduct.ext' fun b m => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, thetaA_apply, theta_tmul]
  change thetaLoc p L U r (Z.presheaf.map (homOfLE (pre_le p U r)).op b ⊗ₜ
      L.presheaf.map (homOfLE (X.basicOpen_le r)).op m) =
    (pb p L).presheaf.map (homOfLE (pre_le p U r)).op (b • eta p L U m)
  rw [thetaLoc_tmul, Scheme.Modules.map_smul, map_eta p L (homOfLE (X.basicOpen_le r)) (homOfLE (pre_le p U r))]

theorem thetaLoc_bijective_of_frame (hU : IsAffineOpen U) (hpU : IsAffineOpen (p ⁻¹ᵁ U))
    (hN : Scheme.Modules.IsInvertible (pb p L)) (r : Γ(X, U)) {s₀ : Γ(L, X.basicOpen r)}
    (hs₀ : Scheme.Modules.IsFrameOn s₀ (X.basicOpen r)) : Function.Bijective (thetaLoc p L U r) := by
  haveI : IsLocalization.Away r Γ(X, X.basicOpen r) := hU.isLocalization_basicOpen r
  have hlocB := isLocalizedModule_resB_of_eq p U hpU r (p ⁻¹ᵁ X.basicOpen r) (pre_le p U r)
    (Scheme.preimage_basicOpen p r)
  let ψ : Γ(Z, p ⁻¹ᵁ X.basicOpen r) → Γ(Z, p ⁻¹ᵁ X.basicOpen r) ⊗[Γ(X, U)] Γ(L, X.basicOpen r) :=
    fun b => b ⊗ₜ s₀
  have key : Function.Bijective (thetaLoc p L U r ∘ ψ) := by
    have hfun : thetaLoc p L U r ∘ ψ = fun g => g • eta p L (X.basicOpen r) s₀ :=
      funext fun b => thetaLoc_tmul p L U r b s₀
    rw [hfun]
    exact bijective_smul_eta p L hs₀ hN

  have hψ : ∀ x, ∃ b, ψ b = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, TensorProduct.zero_tmul _ s₀⟩
    | tmul b m =>

      have hb := hs₀.bijective (le_refl (X.basicOpen r)) le_rfl
      rw [map_self] at hb
      obtain ⟨a', rfl⟩ := hb.2 m
      obtain ⟨⟨a₀, ⟨_, n, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers r) a'
      change a' * X.presheaf.map (homOfLE (X.basicOpen_le r)).op (r ^ n) =
        X.presheaf.map (homOfLE (X.basicOpen_le r)).op a₀ at ha
      have hu := hlocB.map_units ⟨r ^ n, n, rfl⟩
      rw [Module.End.isUnit_iff] at hu
      obtain ⟨b'', rfl⟩ := hu.2 b
      refine ⟨a₀ • b'', ?_⟩
      change (a₀ • b'') ⊗ₜ s₀ = ((r ^ n) • b'') ⊗ₜ (a' • s₀)
      rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul, smul_BO, smul_BO, smul_smul, mul_comm, ha]
    | add x y hx hy =>
      obtain ⟨b₁, rfl⟩ := hx
      obtain ⟨b₂, rfl⟩ := hy
      exact ⟨b₁ + b₂, TensorProduct.add_tmul b₁ b₂ s₀⟩
  refine ⟨fun x₁ x₂ h => ?_, fun y => ?_⟩
  · obtain ⟨b₁, rfl⟩ := hψ x₁
    obtain ⟨b₂, rfl⟩ := hψ x₂
    rw [key.1 h]
  · obtain ⟨b, hb⟩ := key.2 y
    exact ⟨ψ b, hb⟩

theorem exists_basicOpen_isFrameOn (hL : Scheme.Modules.IsInvertible L) (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) : ∃ f : Γ(X, U), x ∈ X.basicOpen f ∧
      ∃ s : Γ(L, X.basicOpen f), Scheme.Modules.IsFrameOn s (X.basicOpen f) := by
  obtain ⟨W, hxW, ⟨e⟩⟩ := hL.1 x
  obtain ⟨sW, hsW⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit W e
  obtain ⟨f, hfle, hxf⟩ := hU.exists_basicOpen_le (⟨x, hxW⟩ : W) hx
  exact ⟨f, hxf, L.presheaf.map (homOfLE hfle).op sW, (hsW.map (homOfLE hfle)).mono hfle⟩

theorem theta_bijective (hL : Scheme.Modules.IsInvertible L) (hU : IsAffineOpen U)
    (hpU : IsAffineOpen (p ⁻¹ᵁ U)) : Function.Bijective (theta p L U) := by
  have hN : Scheme.Modules.IsInvertible (pb p L) := hL.pullback p
  let S : Set Γ(X, U) := {f | ∃ s : Γ(L, X.basicOpen f), Scheme.Modules.IsFrameOn s (X.basicOpen f)}
  have hspan : Ideal.span S = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, hxf, hf⟩ := exists_basicOpen_isFrameOn L U hL hU hx
    exact Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hxf⟩
  haveI : ∀ r : S, IsLocalizedModule.Away r.1 (resB p U (p ⁻¹ᵁ X.basicOpen r.1) (pre_le p U r.1)) := fun r =>
    isLocalizedModule_resB_of_eq p U hpU r.1 _ _ (Scheme.preimage_basicOpen p r.1)
  haveI : ∀ r : S, IsLocalizedModule.Away r.1 (resBO L U r.1) := fun r =>
    isLocalizedModule_resBO L U r.1 hL hU
  haveI : ∀ r : S, IsLocalizedModule.Away r.1 (resN p L U (p ⁻¹ᵁ X.basicOpen r.1) (pre_le p U r.1)) :=
    fun r => isLocalizedModule_resN_of_eq p L U hpU hN r.1 _ _ (Scheme.preimage_basicOpen p r.1)
  haveI : ∀ r : S, IsLocalizedModule.Away r.1 (resT p L U r.1) := fun r => by
    unfold resT; infer_instance
  change Function.Bijective (thetaA p L U)
  refine bijective_of_isLocalized_span S hspan
    (fun r : S => Γ(Z, p ⁻¹ᵁ X.basicOpen r.1) ⊗[Γ(X, U)] Γ(L, X.basicOpen r.1))
    (fun r : S => resT p L U r.1)
    (fun r : S => Γ(pb p L, p ⁻¹ᵁ X.basicOpen r.1))
    (fun r : S => resN p L U (p ⁻¹ᵁ X.basicOpen r.1) (pre_le p U r.1))
    (thetaA p L U) fun r => ?_
  have hmap : IsLocalizedModule.map (Submonoid.powers r.1) (resT p L U r.1)
      (resN p L U (p ⁻¹ᵁ X.basicOpen r.1) (pre_le p U r.1)) (thetaA p L U) = thetaLoc p L U r.1 := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r.1) (resT p L U r.1)
      (f' := resN p L U (p ⁻¹ᵁ X.basicOpen r.1) (pre_le p U r.1))
    rw [IsLocalizedModule.map_comp, thetaLoc_comp_resT]
  rw [hmap]
  obtain ⟨s₀, hs₀⟩ := r.2
  exact thetaLoc_bijective_of_frame p L U hU hpU hN r.1 hs₀

def beta (hL : Scheme.Modules.IsInvertible L) (hU : IsAffineOpen U) (hpU : IsAffineOpen (p ⁻¹ᵁ U)) :
    Γ(Z, p ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(L, U) ≃ₗ[Γ(Z, p ⁻¹ᵁ U)] Γ(pb p L, p ⁻¹ᵁ U) :=
  LinearEquiv.ofBijective (theta p L U) (theta_bijective p L U hL hU hpU)

theorem beta_tmul (hL : Scheme.Modules.IsInvertible L) (hU : IsAffineOpen U) (hpU : IsAffineOpen (p ⁻¹ᵁ U))
    (b : Γ(Z, p ⁻¹ᵁ U)) (s : Γ(L, U)) : beta p L U hL hU hpU (b ⊗ₜ s) = b • eta p L U s :=
  theta_tmul p L U b s

end Affine

theorem beta_one_tmul {X Z : Scheme.{u}} (p : Z ⟶ X) (L : X.Modules) (U : X.Opens)
    (hL : Scheme.Modules.IsInvertible L) (hU : IsAffineOpen U) (hpU : IsAffineOpen (p ⁻¹ᵁ U)) (s : Γ(L, U)) :
    letI := algAB p U
    beta p L U hL hU hpU (1 ⊗ₜ s) = eta p L U s := by
  rw [beta_tmul, one_smul]

theorem result {X Z : Scheme.{u}} (p : Z ⟶ X) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (U : X.Opens) (hU : IsAffineOpen U) (hpU : IsAffineOpen (p ⁻¹ᵁ U)) :
    letI := (p.app U).hom.toAlgebra
    ∃ β : Γ(Z, p ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(L, U) ≃ₗ[Γ(Z, p ⁻¹ᵁ U)] Γ((Scheme.Modules.pullback p).obj L, p ⁻¹ᵁ U),
      ∀ s : Γ(L, U), β (1 ⊗ₜ s) = (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app L).app U) s :=
  ⟨beta p L U hL hU hpU, beta_one_tmul p L U hL hU hpU⟩

end P2mPullbackSectionsSol
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback.P2mPullbackSectionsSol"

theorem solution
    {X Z : Scheme.{u}} (p : Z ⟶ X) {L : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (U : X.Opens) (hU : IsAffineOpen U) (hpU : IsAffineOpen (p ⁻¹ᵁ U)) :
    letI := (p.app U).hom.toAlgebra
    ∃ β : Γ(Z, p ⁻¹ᵁ U) ⊗[Γ(X, U)] Γ(L, U) ≃ₗ[Γ(Z, p ⁻¹ᵁ U)] Γ((Scheme.Modules.pullback p).obj L, p ⁻¹ᵁ U),
      ∀ s : Γ(L, U), β (1 ⊗ₜ s) = (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app L).app U) s :=
  P2mPullbackSectionsSol.result p hL U hU hpU

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_baseChange_sections_linearEquiv_pullback (solution)
