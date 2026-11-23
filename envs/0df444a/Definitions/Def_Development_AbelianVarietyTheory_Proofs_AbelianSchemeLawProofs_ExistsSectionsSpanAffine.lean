-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
-- name    : Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:31:02.030844+00:00
-- url     : https://prove2.me/theorems/e4a7ccda-10bb-413d-9e92-47a9fd24a089
-- title:
--   Exists Sections Span Affine
-- statement:
--   Definitions and structural lemmas for Exists Sections Span Affine, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSectionsSpanAffine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SecAff
section Calc
variable {X X' X'' : Scheme.{0}}
def rs {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) := (X.presheaf.map (homOfLE h).op).hom
def pa (φ : X' ⟶ X) {U : X.Opens} {V : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) : Γ(X, U) →+* Γ(X', V) :=
  (φ.appLE U V h).hom
theorem le_pre_top (φ : X' ⟶ X) {V : X'.Opens} : V ≤ φ ⁻¹ᵁ ⊤ := le_top
theorem le_pre_inf {φ : X' ⟶ X} {V : X'.Opens} {U U' : X.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (h' : V ≤ φ ⁻¹ᵁ U') : V ≤ φ ⁻¹ᵁ (U ⊓ U') := le_inf h h'
theorem rs_pa (φ : X' ⟶ X) {U : X.Opens} {V W : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) (h₂ : W ≤ V)
    (x : Γ(X, U)) : rs h₂ (pa φ h x) = pa φ (h₂.trans h) x := by
  change (φ.appLE U V h ≫ X'.presheaf.map (homOfLE h₂).op).hom x = _
  rw [Scheme.Hom.appLE_map]
  rfl
theorem pa_rs (φ : X' ⟶ X) {U U' : X.Opens} {V : X'.Opens} (h₁ : U' ≤ U) (h : V ≤ φ ⁻¹ᵁ U')
    (x : Γ(X, U)) : pa φ h (rs h₁ x) = pa φ (h.trans (φ.preimage_mono h₁)) x := by
  change (X.presheaf.map (homOfLE h₁).op ≫ φ.appLE U' V h).hom x = _
  rw [Scheme.Hom.map_appLE]
  rfl
theorem pa_pa (φ : X' ⟶ X) (ψ : X'' ⟶ X') {U : X.Opens} {V : X'.Opens} {W : X''.Opens}
    (h : V ≤ φ ⁻¹ᵁ U) (h' : W ≤ ψ ⁻¹ᵁ V) (χ : X'' ⟶ X) (e : ψ ≫ φ = χ) (h'' : W ≤ χ ⁻¹ᵁ U)
    (x : Γ(X, U)) : pa ψ h' (pa φ h x) = pa χ h'' x := by
  subst e
  change (φ.appLE U V h ≫ ψ.appLE V W h').hom x = _
  rw [Scheme.Hom.appLE_comp_appLE]
  rfl
end Calc
theorem pa_linComb_g {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ψ : K → (Z ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) (hψ : ∀ k, h ≫ φ k = ψ k) (i j : K → L.ι)
    (e : LB.wchart L ψ i ⊓ LB.wchart L ψ j ≤ h ⁻¹ᵁ (LB.wchart L φ i ⊓ LB.wchart L φ j)) :
    pa h e (LB.lcg L φ ε i j : Γ(Y, LB.wchart L φ i ⊓ LB.wchart L φ j)) =
      (LB.lcg L ψ ε i j : Γ(Z, LB.wchart L ψ i ⊓ LB.wchart L ψ j)) := by
  have : Units.map (pa h e).toMonoidHom (LB.lcg L φ ε i j) = LB.lcg L ψ ε i j := by
    unfold LB.lcg
    rw [map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow]
    congr 1
    exact Units.ext (pa_pa (φ k) h _ e (ψ k) (hψ k) _ _)
  exact congrArg Units.val this
section Pull
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}
theorem chart_le (h : T' ⟶ T) (j : Fin 1 → L.ι) :
    (LPow A L a T').U j ≤ (h ▷ A).left ⁻¹ᵁ (LPow A L a T).U j :=
  chart_le_res A L (h ▷ A) (whiskerRight_snd h A) a j
omit [GrpObj A] in
theorem whisker_snd_left (h : T' ⟶ T) : (h ▷ A).left ≫ (snd T A).left = (snd T' A).left := by
  rw [← Over.comp_left, whiskerRight_snd]
omit [GrpObj A] in
theorem whisker_fst_left (h : T' ⟶ T) :
    (h ▷ A).left ≫ (fst T A).left = (fst T' A).left ≫ h.left := by
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
theorem pa_g (h : T' ⟶ T) (i j : Fin 1 → L.ι)
    (e : (LPow A L a T').U i ⊓ (LPow A L a T').U j ≤
      (h ▷ A).left ⁻¹ᵁ ((LPow A L a T).U i ⊓ (LPow A L a T).U j)) :
    pa (h ▷ A).left e ((LPow A L a T).g i j :
      Γ((T ⊗ A).left, (LPow A L a T).U i ⊓ (LPow A L a T).U j)) =
      ((LPow A L a T').g i j : Γ((T' ⊗ A).left, (LPow A L a T').U i ⊓ (LPow A L a T').U j)) := by
  exact pa_linComb_g L (fun _ : Fin 1 => (snd T A).left) (fun _ => (snd T' A).left) (fun _ => a)
    (h ▷ A).left (fun _ => whisker_snd_left A h) i j e
theorem liftHom_eq (W : (T ⊗ A).left.Opens) (r : Γ(T.left, ⊤)) :
    liftHom A W r = pa (fst T A).left (le_pre_top _) r := rfl
theorem pa_liftHom (h : T' ⟶ T) {W : (T ⊗ A).left.Opens} {W' : (T' ⊗ A).left.Opens}
    (e : W' ≤ (h ▷ A).left ⁻¹ᵁ W) (r : Γ(T.left, ⊤)) :
    pa (h ▷ A).left e (liftHom A W r) = liftHom A W' (pa h.left (le_pre_top _) r) := by
  rw [liftHom_eq, liftHom_eq, pa_pa _ _ _ _ _ (whisker_fst_left A h) (le_pre_top _),
    pa_pa _ _ _ _ _ rfl (le_pre_top _)]
def pull (h : T' ⟶ T) :
    SecM A L a T →ₛₗ[pa h.left (V := ⊤) (le_pre_top _)] SecM A L a T' where
  toFun s := ⟨fun j => pa (h ▷ A).left (chart_le A L a h j) (s.1 j), fun i j => by
    have hs : rs inf_le_left (s.1 i) = ((LPow A L a T).g i j :
      Γ((T ⊗ A).left, (LPow A L a T).U i ⊓ (LPow A L a T).U j)) * rs inf_le_right (s.1 j) :=
      s.2 i j
    have e := le_pre_inf (inf_le_left.trans (chart_le A L a h i))
      (inf_le_right.trans (chart_le A L a h j))
    have := congrArg (pa (h ▷ A).left e) hs
    rw [map_mul, pa_rs, pa_rs] at this
    replace this := this.trans (congrArg (· * _) (pa_g A L a h i j e))
    change rs _ _ = _ * rs _ _
    rw [rs_pa, rs_pa]
    exact this⟩
  map_add' s t := by
    ext j
    exact map_add (pa (h ▷ A).left (chart_le A L a h j)) _ _
  map_smul' r s := by
    ext j
    change pa (h ▷ A).left (chart_le A L a h j) (liftHom A _ r * s.1 j) =
      liftHom A _ _ * pa (h ▷ A).left (chart_le A L a h j) (s.1 j)
    rw [map_mul, pa_liftHom]
end Pull
section Span
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' T'' : Over S}
instance isOpenImmersion_overResι (V : T.left.Opens) : IsOpenImmersion (overResι V).left :=
  inferInstanceAs (IsOpenImmersion V.ι)
end Span
end GlobalTheory.SecAff


