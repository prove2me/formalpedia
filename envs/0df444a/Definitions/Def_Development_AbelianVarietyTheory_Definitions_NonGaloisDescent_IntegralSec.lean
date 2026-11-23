-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IntegralSec
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IntegralSec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:24.527799+00:00
-- url     : https://prove2.me/theorems/29fd7c32-0957-4879-b791-7fa15f0b988b
-- title:
--   Integral Sec
-- statement:
--   Definitions and structural lemmas for Integral Sec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IntegralSec.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ModelMetric
variable {C : Type} [Field C] (O : ValuationSubring C)
abbrev SO : Scheme.{0} := Spec (CommRingCat.of O)
abbrev TO : Over (SO O) := Over.mk (𝟙 (SO O))
abbrev TC : Over (SO O) := Over.mk (Spec.map (CommRingCat.ofHom O.subtype))
def gen : TC O ⟶ TO O := Over.homMk (Spec.map (CommRingCat.ofHom O.subtype)) (Category.comp_id _)
def cst (c : C) : Γ((TC O).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom c
variable {O} (A : Over (SO O)) [GrpObj A] (L : LB A.left)
def ModelVal (a : ℤ) (s : LB.Sec (LPow A L a (TC O))) (x : TO O ⟶ A) (c : C) : Prop :=
  ∃ τ : LB.Gen (LB.LinComb L (Y := (TO O).left) (K := Fin 1) (fun _ => x.left) (fun _ => a)), τ.IsGen ∧
    IsValueAt A L a s (gen O ≫ x) (LB.pullGen L (fun _ : Fin 1 => x.left) (fun _ => a) τ (gen O).left) (cst O c)
def SupLE (a : ℤ) (s : LB.Sec (LPow A L a (TC O))) (κ : C) : Prop :=
  ∀ (x : TO O ⟶ A) (c : C), ModelVal A L a s x c → κ * c ∈ O
def Normalised (a : ℤ) (s : LB.Sec (LPow A L a (TC O))) : Prop :=
  SupLE A L a s 1 ∧ ∃ x : TO O ⟶ A, ModelVal A L a s x 1
def FinOrd (k : ℤ) (θ : ThetaGrp A L k (TC O)) : Prop :=
  ∃ n : ℕ, 0 < n ∧ θ.pt ^ n = 1 ∧ LB.Gen.Corr L _ _ _ _ (powGen A L k θ n) (LB.oneGen L)
def IsoPull (N : ℕ) (s : LB.Sec (LPow A L 1 (TC O))) (s₁ : LB.Sec (LPow A L ((N : ℤ) ^ 2) (TC O))) : Prop :=
  (∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd (TC O) A).left, (snd (TC O) A ^ N).left] ![(N : ℤ) ^ 2, -1]),
    α.IsGen ∧ IsTwistPull A L (mulT A (TC O) N) (snd (TC O) A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁) ∧
  ∀ (x : TO O ⟶ A) (c : C), ModelVal A L ((N : ℤ) ^ 2) s₁ x c ↔ ModelVal A L 1 s (x ^ N) c
def BddDatum (N : ℕ) (κ : C) (s₁ g : LB.Sec (LPow A L ((N : ℤ) ^ 2) (TC O))) : Prop :=
  ∃ (n : ℕ) (θ : Fin n → ThetaGrp A L ((N : ℤ) ^ 2) (TC O)) (c : Fin n → C)
    (t : Fin n → LB.Sec (LPow A L ((N : ℤ) ^ 2) (TC O))),
    (∀ j, FinOrd A L _ (θ j)) ∧ (∀ j, κ * c j ∈ O) ∧ (∀ j, IsActOf A L _ (θ j) s₁ (t j)) ∧
    ∀ i, g.f i = ∑ j, liftFun A _ (cst O (c j)) * (t j).f i
def IntegralSec (a : ℤ) (s : LB.Sec (LPow A L a (TC O))) (κ : C) : Prop :=
  ∃ s₀ : LB.Sec (LPow A L a (TO O)), ∀ (i : Fin 1 → L.ι) (W : ((TC O) ⊗ A).left.Opens)
    (h₁ : W ≤ (LPow A L a (TC O)).U i) (h₂ : W ≤ (gen O ▷ A).left ⁻¹ᵁ (LPow A L a (TO O)).U i),
    liftFun A W (cst O κ) * (((TC O) ⊗ A).left.presheaf.map (homOfLE h₁).op).hom (s.f i) =
      ((gen O ▷ A).left.appLE _ W h₂).hom (s₀.f i)
end GlobalTheory.ModelMetric


