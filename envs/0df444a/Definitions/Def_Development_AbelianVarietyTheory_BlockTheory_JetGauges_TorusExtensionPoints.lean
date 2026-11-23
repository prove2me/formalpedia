-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_TorusExtensionPoints
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_TorusExtensionPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:27.064455+00:00
-- url     : https://prove2.me/theorems/f2180553-8bde-4c3c-a389-ea5c457ff47b
-- title:
--   Torus Extension Points
-- statement:
--   Definitions and structural lemmas for Torus Extension Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/TorusExtensionPoints.lean

import Mathlib
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusExtensionPoints
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
section Defs
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
abbrev cT (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ
abbrev zeroT (T : Over (Spec (CommRingCat.of R))) : T ⟶ D.P.A := toUnit T ≫ η[D.P.A]
def lamInvφ {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) :
    Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (cT D T χ) b).left, (cT D T χ).left, b.left, (zeroT D T).left]
def cubT {T : Over (Spec (CommRingCat.of R))} (x x' y : T ⟶ D.P.A) :=
  LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left
structure GtPt (T : Over (Spec (CommRingCat.of R))) where
  b : T ⟶ D.P.A
  s : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (lamInvφ D b χ) DegPre.gtε)
  isGen : ∀ χ, (s χ).IsGen
  s_zero : LB.Gen.Corr D.P.L _ _ _ _ (s 0) (LB.oneGen D.P.L)
  mult : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (s (χ + χ')) (cubT D (cT D T χ) (cT D T χ') b))
    (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ'))
abbrev TU (U : (Spec (CommRingCat.of R)).Opens) : Over (Spec (CommRingCat.of R)) := Over.mk U.ι
abbrev PsiFam (U : (Spec (CommRingCat.of R)).Opens) : Type :=
  ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (cT D (TU U) χ).left) (fun _ => -1))
def IsPsiExt (U : (Spec (CommRingCat.of R)).Opens) (ψ' : PsiFam D U) : Prop :=
  ∀ χ : D.X, (ψ' χ).IsGen ∧ ∀ j : TK R ⟶ TU U,
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (ψ' χ) j.left) (D.psi χ)
def PsiGenOn (U : (Spec (CommRingCat.of R)).Opens) : Prop := ∃ ψ' : PsiFam D U, IsPsiExt D U ψ'
def psiLocus : (Spec (CommRingCat.of R)).Opens := sSup {U | PsiGenOn D U}
def tauU {U : (Spec (CommRingCat.of R)).Opens} (ψ' : PsiFam D U) (a b : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψ' (a + b)) (LB.invGen D.P.L _ _ (ψ' a)))
      (LB.invGen D.P.L _ _ (ψ' b)))
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ D.rig (toUnit (TU U)).left))
namespace GtPt
variable {D} {T : Over (Spec (CommRingCat.of R))}
def IsZero (g : GtPt D T) : Prop :=
  g.b = zeroT D T ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.oneGen D.P.L)
def IsAdd (g g' g'' : GtPt D T) : Prop :=
  g''.b = padd D.P.A g.b g'.b ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g''.s χ) (cubT D (cT D T χ) g.b g'.b))
    (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ))
def IsNsmul (k : ℕ) (g h : GtPt D T) : Prop :=
  ∃ gs : Fin (k + 1) → GtPt D T, (gs 0).IsZero ∧
    (∀ i : Fin k, IsAdd (gs i.castSucc) g (gs i.succ)) ∧ gs (Fin.last k) = h
def IsIota (U : (Spec (CommRingCat.of R)).Opens) (y : D.X) (g : GtPt D T) : Prop :=
  g.b = cT D T y ∧ ∃ (u : T ⟶ TU U) (ψ' : PsiFam D U), IsPsiExt D U ψ' ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.pullGen D.P.L _ _ (tauU D ψ' y χ) u.left)
end GtPt
structure QkPtT (U : (Spec (CommRingCat.of R)).Opens) (T : Over (Spec (CommRingCat.of R)))
    (k : ℕ) where
  y : D.X
  g : GtPt D T
  eq : ∃ h : GtPt D T, GtPt.IsNsmul k g h ∧ GtPt.IsIota U y h
def QkPtT.Equiv {D : DegPre R} {U : (Spec (CommRingCat.of R)).Opens}
    {T : Over (Spec (CommRingCat.of R))} {k : ℕ} (p p' : QkPtT D U T k) : Prop :=
  ∃ z : D.X, p'.y = p.y + k • z ∧ ∃ h : GtPt D T, GtPt.IsIota U z h ∧ GtPt.IsAdd p.g h p'.g
variable {D} {F : Type} [Field F] [Algebra (FractionRing R) F]
def GtRestricts {T : Over (Spec (CommRingCat.of R))} (f : TF (R := R) F ⟶ T) (g : GtPt D T)
    (x : GtPtF D F) : Prop :=
  x.b = f ≫ g.b ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (x.s χ) (LB.pullGen D.P.L _ _ (g.s χ) f.left)
def QkRestricts {U : (Spec (CommRingCat.of R)).Opens} {T : Over (Spec (CommRingCat.of R))} {k : ℕ}
    (f : TF (R := R) F ⟶ T) (p : QkPtT D U T k) (q : QkPt D F k) : Prop :=
  q.y = p.y ∧ GtRestricts f p.g q.g
variable (D F) in

def equivField : GtPt D (TF (R := R) F) ≃ GtPtF D F where
  toFun g := ⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩
  invFun g := ⟨g.b, g.s, g.isGen, g.s_zero, g.mult⟩
  left_inv _ := rfl
  right_inv _ := rfl
example (g : GtPt D (TF (R := R) F)) : g.IsZero ↔ (equivField D F g).IsZero := Iff.rfl
example (g g' g'' : GtPt D (TF (R := R) F)) :
    GtPt.IsAdd g g' g'' ↔
      GtPtF.IsAdd (equivField D F g) (equivField D F g') (equivField D F g'') := Iff.rfl
end Defs
def PsiExtClaim : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R),
    (∀ (U : (Spec (CommRingCat.of R)).Opens) (ψ₁ ψ₂ : PsiFam D U),
      IsPsiExt D U ψ₁ → IsPsiExt D U ψ₂ → ψ₁ = ψ₂) ∧ PsiGenOn D (psiLocus D)
def IotaClaim : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (U : (Spec (CommRingCat.of R)).Opens), PsiGenOn D U →
      ∀ (T : Over (Spec (CommRingCat.of R))), Nonempty (T ⟶ TU U) →
        ∀ y : D.X, ∃! g : GtPt D T, GtPt.IsIota U y g
def GtRestrictClaim : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (T : Over (Spec (CommRingCat.of R))) (f : TF (R := R) F ⟶ T),
    (∀ g : GtPt D T, ∃! x : GtPtF D F, GtRestricts f g x) ∧
    (∀ (g : GtPt D T) (x : GtPtF D F), GtRestricts f g x → g.IsZero → x.IsZero) ∧
    (∀ (g g' g'' : GtPt D T) (x x' x'' : GtPtF D F), GtRestricts f g x → GtRestricts f g' x' →
      GtRestricts f g'' x'' → GtPt.IsAdd g g' g'' → GtPtF.IsAdd x x' x'') ∧
    (∀ (k : ℕ) (g h : GtPt D T) (x x' : GtPtF D F), GtRestricts f g x → GtRestricts f h x' →
      GtPt.IsNsmul k g h → GtPtF.IsNsmul k x x') ∧
    (∀ (U : (Spec (CommRingCat.of R)).Opens) (y : D.X) (g : GtPt D T) (x : GtPtF D F),
      GtRestricts f g x → GtPt.IsIota U y g → GtPtF.IsIota y x)
def QkRestrictClaim : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (U : (Spec (CommRingCat.of R)).Opens)
    (T : Over (Spec (CommRingCat.of R))) (f : TF (R := R) F ⟶ T) (k : ℕ),
    (∀ p : QkPtT D U T k, ∃! q : QkPt D F k, QkRestricts f p q) ∧
    (∀ (p p' : QkPtT D U T k) (q q' : QkPt D F k), QkRestricts f p q → QkRestricts f p' q' →
      QkPtT.Equiv p p' → QkPt.Equiv D F q q')
end GlobalTheory.IndefiniteRowSideFullHecke.TorusExtensionPoints


