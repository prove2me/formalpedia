-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:38:16.621637+00:00
-- url     : https://prove2.me/theorems/ed61b017-687a-4806-983a-90bd804f07a5
-- title:
--   Deg Exp F
-- statement:
--   Definitions and structural lemmas for Deg Exp F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/DegExpF.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
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
namespace GeneratorPullback
section Lin
variable {X Y Y' : Scheme.{0}} (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
def SecLin (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁))
    (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) {n : ℕ} (s₂ : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂))
    (h : Y' ⟶ Y) (c : Fin n → Γ(Y', ⊤)) : Prop :=
  ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι),
    LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim j₁ j₂) →
    (Y'.presheaf.map (homOfLE (inf_le_left :
        LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ LB.wchart L φ₁ j₁)).op).hom
        (s₁.f j₁) =
      ∑ i, resTop _ (c i) *
        (Y'.presheaf.map (homOfLE (inf_le_right.trans
          (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k) :
          LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤
            h ⁻¹ᵁ LB.wchart L φ₂ j₂)).op).hom ((h.app (LB.wchart L φ₂ j₂)).hom ((s₂ i).f j₂))
end Lin
section IsoRel
variable {Y Y' X₁ X₂ Z₁ Z₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂)
abbrev isoW (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (m : Y' ⟶ Y) (g₁ : Z₁ ⟶ X₁) (h₁ : Y' ⟶ Z₁)
    (g₂ : Z₂ ⟶ X₂) (h₂ : Y' ⟶ Z₂) (p : (PUnit.{1} → L₂.ι) × (PUnit.{1} → L₁.ι))
    (j₁ : Fin 1 → L₁.ι) (j₂ : Fin 1 → L₂.ι) : Y'.Opens :=
  m ⁻¹ᵁ (LB.div (L₂.pull f₂) (L₁.pull f₁)).U p ⊓
    h₁ ⁻¹ᵁ LB.wchart L₁ (fun _ : Fin 1 => g₁) j₁ ⊓ h₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => g₂) j₂
def IsoRelM (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (m : Y' ⟶ Y)
    (k : ℕ) (g₁ : Z₁ ⟶ X₁) (h₁ : Y' ⟶ Z₁)
    (a : LB.Sec (LB.LinComb L₁ (K := Fin 1) (fun _ => g₁) (fun _ => (k : ℤ))))
    (g₂ : Z₂ ⟶ X₂) (h₂ : Y' ⟶ Z₂)
    (b : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => g₂) (fun _ => (k : ℤ)))) : Prop :=
  h₁ ≫ g₁ = m ≫ f₁ ∧ h₂ ≫ g₂ = m ≫ f₂ ∧
  ∀ (p : (PUnit.{1} → L₂.ι) × (PUnit.{1} → L₁.ι)) (j₁ : Fin 1 → L₁.ι) (j₂ : Fin 1 → L₂.ι),
    j₁ 0 = p.2 PUnit.unit → j₂ 0 = p.1 PUnit.unit →
    (Y'.presheaf.map (homOfLE (inf_le_right :
        isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ p j₁ j₂ ≤ h₂ ⁻¹ᵁ LB.wchart L₂ (fun _ : Fin 1 => g₂) j₂)).op).hom
        ((h₂.app _).hom (b.f j₂)) =
      (res (inf_le_left.trans inf_le_left :
          isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ p j₁ j₂ ≤ m ⁻¹ᵁ (LB.div (L₂.pull f₂) (L₁.pull f₁)).U p)
          (pullU m _ (w.s p))).val ^ k *
      (Y'.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
        isoW L₁ L₂ f₁ f₂ m g₁ h₁ g₂ h₂ p j₁ j₂ ≤ h₁ ⁻¹ᵁ LB.wchart L₁ (fun _ : Fin 1 => g₁) j₁)).op).hom
        ((h₁.app _).hom (a.f j₁))
end IsoRel
end GeneratorPullback
section ExpansionF
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
namespace UnifPre
variable (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
abbrev GF : Over (TK R).left := TFK (R := R) F ⊗ (Over.pullback (jK R)).obj G
abbrev gFK : (GF (G := G) F).left ⟶ G.left :=
  (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left ≫ pullback.fst G.hom (jK R)
abbrev genF : GF (G := G) F ⟶ TFK (R := R) F ⊗ A.A :=
  lift (fst _ _) (snd _ _ ≫ U.gen.hom)
abbrev SecGF (k : ℕ) : Type :=
  LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => gFK (G := G) F) (fun _ => (k : ℤ)))
def ExpandsG (k : ℕ) (σ' : U.SecGF F k) (s : Fam D.toPre F k) : Prop :=
  ∃ (n : ℕ) (c : Fin n → F)
    (σ : Fin n → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : Fin n → ∀ α : D.toPre.X, D.toPre.SecB k α),
    (∀ i e, U.ExpandsAt e k (σ i) (f i)) ∧
    GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => gFK (G := G) F) (fun _ => (k : ℤ)) σ'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i)) ∧
    ∀ α : D.toPre.X,
      GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α)
        (D.toPre.famφB α) (DegPre.famε k) (fun i => f i α) (DegPre.prB D.toPre F).left
        (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i))
def ExpandsF (k : ℕ)
    (w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))))
    (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (s : Fam D.toPre F k) : Prop :=
  ∃ σ' : U.SecGF F k,
    GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
      (snd (TFK (R := R) F) A.A).left (U.genF F).left t
      (gFK (G := G) F) (𝟙 _) σ' ∧
    U.ExpandsG F k σ' s
end UnifPre
end ExpansionF
end ReciprocityTheory.ChartRestriction.G.Out


