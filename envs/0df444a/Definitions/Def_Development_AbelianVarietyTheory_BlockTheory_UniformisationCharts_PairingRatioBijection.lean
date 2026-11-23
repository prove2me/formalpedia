-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PairingRatioBijection
-- name    : Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_PairingRatioBijection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:32.005325+00:00
-- url     : https://prove2.me/theorems/85e16dee-7147-435f-bf32-a02e95e52163
-- title:
--   Pairing Ratio Bijection
-- statement:
--   Definitions and structural lemmas for Pairing Ratio Bijection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/PairingRatioBijection.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_TorusPointForms
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
def scal : F →+* Γ(Spec (CommRingCat.of F), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
def trPt (b : TF (R := R) F ⟶ D.P.A) : D.BF F ⟶ D.BF F :=
  lift (fst _ _) (padd D.P.A (D.prB F) (fst _ _ ≫ b))
abbrev lineAt (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) : LB (TF (R := R) F).left :=
  LB.LinComb D.P.L (K := PUnit) (fun _ => b.left) (fun _ => (k : ℤ))
def LineGen (k : ℕ) (b : TF (R := R) F ⟶ D.P.A) : Type :=
  {t : LB.Gen (lineAt D F k b) // t.IsGen}
def phφ (b : TF (R := R) F ⟶ D.P.A) (y α : D.X) : Fin 4 ⊕ Fin 4 → ((D.BF F).left ⟶ D.P.A.left) :=
  Sum.elim (D.famφ F (α + y)) (fun i => (trPt D F b).left ≫ D.famφ F α i)
def phMult (k : ℕ) (g : GtPt D F) (t : LineGen D F k g.base) (α : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g.form α) (LB.invGen D.P.L _ _ t.1))
    (GeneratorPullback.powGen D.P.L _ _ (LB.pullGen D.P.L _ _ D.rig (toUnit (TF (R := R) F)).left) k)
variable {D F}
def IsPh {k : ℕ} (p : QPair D F k) (t : LineGen D F k p.1.2.base) (s s' : Fam D F k) : Prop :=
  ∀ α : D.X, ∃ u : LB.Gen (LB.LinComb D.P.L (phφ D F p.1.2.base p.1.1 α) (DegPre.deltaε k)),
    u.IsGen ∧
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (D.zF F).left) (phMult D F k p.1.2 t α) ∧
    GeneratorPullback.SecRel D.P.L (D.famφ F (α + p.1.1)) (DegPre.famε k) (s'.s (α + p.1.1))
      (D.famφ F α) (DegPre.famε k) (s.s α) (trPt D F p.1.2.base).left
      (phφ D F p.1.2.base p.1.1 α) (DegPre.deltaε k) u
def FamSmul {k : ℕ} (c : F) (s s' : Fam D F k) : Prop :=
  ∀ α j, (s'.s α).f j = liftFun D.P.A (T := TF (R := R) F) _ (scal F c) * (s.s α).f j
def FamAdd {k : ℕ} (s s' s'' : Fam D F k) : Prop :=
  ∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j
def CommIs {k : ℕ} (p p' : QPair D F k) (ζ : Fˣ) : Prop :=
  ∀ (t : LineGen D F k p.1.2.base) (t' : LineGen D F k p'.1.2.base) (s s₁ s₂ r₁ r₂ : Fam D F k),
    IsPh p' t' s s₁ → IsPh p t s₁ s₂ → IsPh p t s r₁ → IsPh p' t' r₁ r₂ → FamSmul (ζ : F) r₂ s₂
def PairingIs {k : ℕ} (a b : Qk D F k) (ζ : Fˣ) : Prop :=
  1 ≤ k ∧ D.TauBimult ∧
    ∀ p p' : QPair D F k, Qk.mk p = a → Qk.mk p' = b → CommIs p p' ζ
def cubPow (k : ℕ) (x x' : TF (R := R) F ⟶ D.P.A) :
    LB.Gen (LB.LinComb D.P.L (K := Fin k × thK)
      (fun q => (lift (x ^ (q.1 : ℕ)) (lift x x')).left ≫ thφ D.P.A (x3 D.P.A) q.2)
      (fun q => thε q.2)) where
  s := fun j => ∏ i : Fin k,
    res ((fun _ hy => Set.mem_iInter.2 fun I => Set.mem_iInter.1 hy (i, I)) :
        LB.wchart D.P.L (K := Fin k × thK)
          (fun q => (lift (x ^ (q.1 : ℕ)) (lift x x')).left ≫ thφ D.P.A (x3 D.P.A) q.2) j ≤
        LB.wchart D.P.L
          (fun I => (lift (x ^ (i : ℕ)) (lift x x')).left ≫ thφ D.P.A (x3 D.P.A) I)
          (fun I => j (i, I)))
      ((cubAt D (x ^ (i : ℕ)) x x').s (fun I => j (i, I)))
def constF (c : Fˣ) :
    LB.Gen (LB.LinComb D.P.L (Y := (TF (R := R) F).left) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res (X := (TF (R := R) F).left) le_top (Units.map (scal F).toMonoidHom c)
def RatioIs {k : ℕ} (p p' : QPair D F k) (ζ : Fˣ) : Prop :=
  LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (p.1.2.form p'.1.1) (cubPow k p'.1.2.base p.1.2.base))
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (p'.1.2.form p.1.1) (cubPow k p.1.2.base p'.1.2.base))
      (constF (D := D) ζ))
variable (R F) in

abbrev TKF : Over (Spec (CommRingCat.of (FractionRing R))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing R) F)))
variable (P : PolAV (Spec (CommRingCat.of (FractionRing R))))
variable (F) in

abbrev SecA (k : ℕ) : Type := LB.Sec (LPow P.A P.L (k : ℤ) (TKF R F))
variable {P}
structure IsLinBij {k : ℕ} (E : SecA F P k → Fam D F k → Prop) : Prop where
  existsUnique_right : ∀ σ, ∃! s, E σ s
  existsUnique_left : ∀ s, ∃! σ, E σ s
  add : ∀ σ σ' σ'' s s' s'', E σ s → E σ' s' → E σ'' s'' →
    (∀ j, σ''.f j = σ.f j + σ'.f j) → FamAdd s s' s''
  smul : ∀ (c : F) σ σ' s s', E σ s → E σ' s' →
    (∀ j, σ'.f j = liftFun P.A (T := TKF R F) _ (scal F c) * σ.f j) → FamSmul c s s'
def Intertwines {k : ℕ} (E : SecA F P k → Fam D F k → Prop)
    (θ : ThetaGrp P.A P.L (k : ℤ) (TKF R F)) (p : QPair D F k) (t : LineGen D F k p.1.2.base) :
    Prop :=
  ∀ σ σ' s s', E σ s → E σ' s' → (IsActOf P.A P.L (k : ℤ) θ σ σ' ↔ IsPh p t s s')
def IsImage {k : ℕ} (E : SecA F P k → Fam D F k → Prop) (p : QPair D F k)
    (x : TKF R F ⟶ P.A) : Prop :=
  1 ≤ k ∧ D.TauBimult ∧ IsLinBij E ∧ x ^ k = 1 ∧
    (∀ θ : ThetaGrp P.A P.L (k : ℤ) (TKF R F), θ.pt = x → ∃ t, Intertwines E θ p t) ∧
    (∀ t, ∃ θ : ThetaGrp P.A P.L (k : ℤ) (TKF R F), θ.pt = x ∧ Intertwines E θ p t)
def IsImageQ {k : ℕ} (E : SecA F P k → Fam D F k → Prop) (a : Qk D F k)
    (x : TKF R F ⟶ P.A) : Prop :=
  ∀ p : QPair D F k, Qk.mk p = a → IsImage E p x
variable (D F)
def PhOperatorSt : Prop :=
  D.TauBimult → ∀ (k : ℕ) (p : QPair D F k) (t : LineGen D F k p.1.2.base),
    (∀ s, ∃! s', IsPh p t s s') ∧
    ∀ t' : LineGen D F k p.1.2.base, ∃ c : Fˣ,
      ∀ s s' s'', IsPh p t s s' → IsPh p t' s s'' → FamSmul (c : F) s' s''
def PairingRatioSt : Prop :=
  D.TauBimult → ∀ k : ℕ, 1 ≤ k → ∀ (p p' : QPair D F k) (ζ : Fˣ),
    PairingIs (Qk.mk p) (Qk.mk p') ζ ↔ RatioIs p p' ζ
variable (P)
def ImageSt : Prop :=
  CharZero F → ∀ (k : ℕ) (E : SecA F P k → Fam D F k → Prop),
    (∀ p x x', IsImage E p x → IsImage E p x' → x = x') ∧
    (∀ p x, IsImage E p x ↔ IsImageQ E (Qk.mk p) x) ∧
    ∀ a a' x x' (ζ : Fˣ), IsImageQ E a x → IsImageQ E a' x' →
      (PairingIs a a' ζ ↔ WeilIs P.A P.L (k : ℤ) x x' (Units.map (scal F).toMonoidHom ζ))
example {k : ℕ} (s : Fam D F k) : FamSmul (1 : F) s s := fun α j => by
  simp [liftFun]
example {k : ℕ} (E : SecA F P k → Fam D F k → Prop) (p : QPair D F k) (x : TKF R F ⟶ P.A)
    (h : IsImageQ E (Qk.mk p) x) : x ^ k = 1 := (h p rfl).2.2.2.1
end GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators


