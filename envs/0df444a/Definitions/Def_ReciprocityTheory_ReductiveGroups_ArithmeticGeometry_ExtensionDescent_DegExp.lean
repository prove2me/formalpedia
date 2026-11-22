-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:04.679338+00:00
-- url     : https://prove2.me/theorems/df67ea7b-6fba-4695-a609-3dec7d522ae4
-- title:
--   Deg Exp
-- statement:
--   Definitions and structural lemmas for Deg Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/DegExp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
def scal {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : R) :
    Γ(Y, ⊤) :=
  p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
abbrev resTop {Y : Scheme.{0}} (W : Y.Opens) (c : Γ(Y, ⊤)) : Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom c
abbrev H0 {Y : Scheme.{0}} (L : LB Y) (k : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 Y) (fun _ => (k : ℤ)))
namespace GeneratorPullback
variable {X Y Y' : Scheme.{0}} (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
def SecScal (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) (s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y)
    (c : Γ(Y', ⊤)) : Prop :=
  ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι),
    LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim j₁ j₂) →
    (Y'.presheaf.map (homOfLE (inf_le_right.trans
        (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤
          h ⁻¹ᵁ LB.wchart L φ₂ j₂)).op).hom ((h.app (LB.wchart L φ₂ j₂)).hom (s₂.f j₂)) =
      resTop _ c *
      (Y'.presheaf.map (homOfLE (inf_le_left :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ LB.wchart L φ₁ j₁)).op).hom
        (s₁.f j₁)
end GeneratorPullback
namespace DegPre
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
def famφB (α : D.X) : Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  ![𝟙 _, (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left, (toUnit D.P.A ≫ D.c α).left,
    (toUnit D.P.A ≫ η[D.P.A]).left]
abbrev SecB (k : ℕ) (α : D.X) : Type := LB.Sec (LB.LinComb D.P.L (famφB D α) (famε k))
end DegPre
def CohAll {X Y : Scheme.{0}} (L : LB X) {Idx : Type} (φ : Idx → (Y ⟶ X)) (j : Idx → L.ι) : Prop :=
  ∀ a b, φ a = φ b → j a = j b
section Expansion
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
namespace UnifPre
variable (U : UnifPre I D A G)
abbrev SecK (k : ℕ) : Type :=
  LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)))
abbrev expW (e : ℕ) (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
    (j₁ : Fin 1 → U.LG.L.ι) (S : Finset D.toPre.X) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι) :
    (thickObj R I e G).left.Opens :=
  (LB.div (D.toPre.P.L.pull (U.gt e).pG.left) (U.LG.L.pull (fstG I e G).left)).U p ⊓
    (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁ ⊓
    S.inf (fun α => (U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) ⊓
      LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG α) (jt α))
lemma expW_le_f (e : ℕ) (p) (j₁) {S : Finset D.toPre.X} (jf jt) {α : D.toPre.X} (hα : α ∈ S) :
    U.expW e p j₁ S jf jt ≤ (U.gt e).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) :=
  inf_le_right.trans ((Finset.inf_le hα).trans inf_le_left)
lemma expWeight_le_chart_weight (e : ℕ) (p) (j₁) {S : Finset D.toPre.X} (jf jt) {α : D.toPre.X} (hα : α ∈ S) :
    U.expW e p j₁ S jf jt ≤ LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt e).pG α) (jt α) :=
  inf_le_right.trans ((Finset.inf_le hα).trans inf_le_right)
def ExpandsAt (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) : Prop :=
  ∃ S : Finset D.toPre.X,
    (∀ α ∉ S, ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt e).pG.left.app _).hom ((f α).f j) = 0) ∧
    ∀ (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι)) (j₁ : Fin 1 → U.LG.L.ι)
      (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι),
      j₁ 0 = p.2 PUnit.unit →
      CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) →
      (res (inf_le_left.trans inf_le_left :
          U.expW e p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
            (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ k *
        ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
          U.expW e p j₁ S jf jt ≤
            (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)).op).hom
          (((fstG I e G).left.app _).hom (σ.f j₁)) =
      ∑ α ∈ S.attach,
        ((thickObj R I e G).left.presheaf.map
            (homOfLE (U.expW_le_f e p j₁ jf jt α.2)).op).hom
            (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
          (res (U.expWeight_le_chart_weight e p j₁ jf jt α.2) (((U.gt e).t α.1).s (jt α.1))).val
def Expands (k : ℕ) (s : U.SecK k) (F : Fam D.toPre (FractionRing R) k) : Prop :=
  ∃ (r : R) (_ : r ≠ 0)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α),
    GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r) ∧
    (∀ α : D.toPre.X,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α)
        (D.toPre.famφB α) (DegPre.famε k) (f α) (DegPre.prB D.toPre (FractionRing R)).left
        (scal (DegPre.BF D.toPre (FractionRing R)).hom r)) ∧
    ∀ e : ℕ, U.ExpandsAt e k σ f
def ExpBij (k : ℕ) : Prop :=
  (∀ s : U.SecK k, ∃! F : Fam D.toPre (FractionRing R) k, U.Expands k s F) ∧
    ∀ F : Fam D.toPre (FractionRing R) k, ∃! s : U.SecK k, U.Expands k s F
end UnifPre
end Expansion
structure Unif {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    extends UnifPre I D A G where
  expand : ∀ k : ℕ, 1 ≤ k → toUnifPre.ExpBij k
end ReciprocityTheory.ChartRestriction.G.Out


