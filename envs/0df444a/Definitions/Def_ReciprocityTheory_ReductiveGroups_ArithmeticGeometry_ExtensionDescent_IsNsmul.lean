-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:40:18.565658+00:00
-- url     : https://prove2.me/theorems/811eb782-8dc4-488f-af00-3dc422e51f7f
-- title:
--   Is Nsmul
-- statement:
--   Definitions and structural lemmas for Is Nsmul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/IsNsmul.lean

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
section GtPoints
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (T : Over (Spec (CommRingCat.of R)))
namespace DegPre
abbrev cT (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ
abbrev zeroT : T ⟶ D.P.A := toUnit T ≫ η[D.P.A]
def gtφT (b : T ⟶ D.P.A) (χ : D.X) : Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (cT D T χ) b).left, (cT D T χ).left, b.left, (zeroT D T).left]
def cubAtT (x x' y : T ⟶ D.P.A) :=
  LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left
end DegPre
structure GtPt where
  b : T ⟶ D.P.A
  s : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T b χ) DegPre.gtε)
  isGen : ∀ χ, (s χ).IsGen
  s_zero : LB.Gen.Corr D.P.L _ _ _ _ (s 0) (LB.oneGen D.P.L)
  mult : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (s (χ + χ'))
      (DegPre.cubAtT D T (DegPre.cT D T χ) (DegPre.cT D T χ') b))
    (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ'))
namespace GtPt
variable {D T}
def IsZero (g : GtPt D T) : Prop :=
  g.b = DegPre.zeroT D T ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.oneGen D.P.L)
def IsAdd (g g' g'' : GtPt D T) : Prop :=
  g''.b = padd D.P.A g.b g'.b ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g''.s χ) (DegPre.cubAtT D T (DegPre.cT D T χ) g.b g'.b))
    (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ))
def IsNsmul (k : ℕ) (g h : GtPt D T) : Prop :=
  ∃ gs : Fin (k + 1) → GtPt D T, (gs 0).IsZero ∧
    (∀ i : Fin k, IsAdd (gs i.castSucc) g (gs i.succ)) ∧ gs (Fin.last k) = h
def IsPull {T' : Over (Spec (CommRingCat.of R))} (h : T'.left ⟶ T.left) (g : GtPt D T)
    (g' : GtPt D T') : Prop :=
  g'.b.left = h ≫ g.b.left ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g'.s χ) (LB.pullGen D.P.L _ _ (g.s χ) h)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
def IsPullF (x : Spec (CommRingCat.of F) ⟶ T.left) (g : GtPt D T) (g' : GtPtF D F) : Prop :=
  g'.b.left = x ≫ g.b.left ∧
    ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g'.s χ) (LB.pullGen D.P.L _ _ (g.s χ) x)
end GtPt
end GtPoints
section OnW
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (W : (Spec (CommRingCat.of R)).Opens)
abbrev TW : Over (Spec (CommRingCat.of R)) := Over.mk W.ι
abbrev overW (T : Over W.toScheme) : Over (Spec (CommRingCat.of R)) := (Over.map W.ι).obj T
structure PsiOn where
  psi : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit)
    (fun _ => (toUnit (TW W) ≫ D.c χ).left) (fun _ => -1))
  psi_gen : ∀ χ, (psi χ).IsGen
  psi_eq : ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.pullGen D.P.L _ _ (psi χ) (jK R ∣_ W))
    (LB.pullGen D.P.L _ _ (D.psi χ) (jK R ⁻¹ᵁ W).ι)
namespace DegPre
def rigW := LB.pullGen D.P.L _ _ D.rig (toUnit (TW W)).left
end DegPre
namespace PsiOn
variable {D W}
def tau (ψW : PsiOn D W) (a b : D.X) :=
  LB.mulGen D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (ψW.psi (a + b)) (LB.invGen D.P.L _ _ (ψW.psi a)))
      (LB.invGen D.P.L _ _ (ψW.psi b)))
    (LB.invGen D.P.L _ _ (D.rigW W))
end PsiOn
def GtPt.IsIotaW {D : DegPre R} {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W)
    {T : Over W.toScheme} (y : D.X) (g : GtPt D (overW W T)) : Prop :=
  g.b = DegPre.cT D (overW W T) y ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ)
    (LB.pullGen D.P.L _ _ (ψW.tau y χ) T.hom)
structure QkPtW (ψW : PsiOn D W) (k : ℕ) (T : Over W.toScheme) where
  y : D.X
  g : GtPt D (overW W T)
  eq : ∃ h : GtPt D (overW W T), GtPt.IsNsmul k g h ∧ GtPt.IsIotaW ψW y h
namespace QkPtW
variable {D W} {ψW : PsiOn D W} {k : ℕ} {T : Over W.toScheme}
def Equiv (p p' : QkPtW D W ψW k T) : Prop :=
  ∃ z : D.X, p'.y = p.y + k • z ∧
    ∃ h : GtPt D (overW W T), GtPt.IsIotaW ψW z h ∧ GtPt.IsAdd p.g h p'.g
def IsAdd (p p' p'' : QkPtW D W ψW k T) : Prop :=
  p''.y = p.y + p'.y ∧ GtPt.IsAdd p.g p'.g p''.g
def IsPull {T' : Over W.toScheme} (h : T' ⟶ T) (p : QkPtW D W ψW k T) (p' : QkPtW D W ψW k T') :
    Prop :=
  p'.y = p.y ∧ GtPt.IsPull h.left p.g p'.g
def IsPullF (F : Type) [Field F] [Algebra (FractionRing R) F]
    (x : Spec (CommRingCat.of F) ⟶ T.left) (p : QkPtW D W ψW k T) (p' : QkPt D F k) : Prop :=
  p'.y = p.y ∧ GtPt.IsPullF F x p.g p'.g
end QkPtW
end OnW
end ReciprocityTheory.ChartRestriction.G.Out


