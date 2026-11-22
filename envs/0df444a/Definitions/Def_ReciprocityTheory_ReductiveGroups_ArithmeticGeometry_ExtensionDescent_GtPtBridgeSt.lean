-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtPtBridgeSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:34.338478+00:00
-- url     : https://prove2.me/theorems/4e8a1192-8292-432d-bf34-0601c1b3cccb
-- title:
--   Gt Pt Bridge St
-- statement:
--   Definitions and structural lemmas for Gt Pt Bridge St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/GtPtBridgeSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_QSurjective
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
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace DegPre
abbrev cF (χ : D.X) : TF (R := R) F ⟶ D.P.A := toUnit _ ≫ D.c χ
abbrev zeroF : TF (R := R) F ⟶ D.P.A := toUnit _ ≫ η[D.P.A]
def gtφ (b : TF (R := R) F ⟶ D.P.A) (χ : D.X) : Fin 4 → ((TF (R := R) F).left ⟶ D.P.A.left) :=
  ![(padd D.P.A (cF D F χ) b).left, (cF D F χ).left, b.left, (zeroF D F).left]
def gtε : Fin 4 → ℤ := ![-1, 1, 1, -1]
def cubAt (x x' y : TF (R := R) F ⟶ D.P.A) :=
  LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' y)).left
end DegPre
structure GtPtF where
  b : TF (R := R) F ⟶ D.P.A
  s : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (DegPre.gtφ D F b χ) DegPre.gtε)
  isGen : ∀ χ, (s χ).IsGen
  s_zero : LB.Gen.Corr D.P.L _ _ _ _ (s 0) (LB.oneGen D.P.L)
  mult : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (s (χ + χ')) (DegPre.cubAt D F (DegPre.cF D F χ) (DegPre.cF D F χ') b))
    (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ'))
namespace GtPtF
variable {D F}
def IsZero (g : GtPtF D F) : Prop :=
  g.b = DegPre.zeroF D F ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ) (LB.oneGen D.P.L)
def IsAdd (g g' g'' : GtPtF D F) : Prop :=
  g''.b = padd D.P.A g.b g'.b ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (g''.s χ) (DegPre.cubAt D F (DegPre.cF D F χ) g.b g'.b))
    (LB.mulGen D.P.L _ _ _ _ (g.s χ) (g'.s χ))
def IsNsmul (k : ℕ) (g h : GtPtF D F) : Prop :=
  ∃ gs : Fin (k + 1) → GtPtF D F, (gs 0).IsZero ∧
    (∀ i : Fin k, IsAdd (gs i.castSucc) g (gs i.succ)) ∧ gs (Fin.last k) = h
def IsIota (y : D.X) (g : GtPtF D F) : Prop :=
  g.b = DegPre.cF D F y ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g.s χ)
    (LB.pullGen D.P.L _ _ (D.io y χ) (jFK (R := R) F))
end GtPtF
structure QkPt (k : ℕ) where
  y : D.X
  g : GtPtF D F
  eq : ∃ h : GtPtF D F, GtPtF.IsNsmul k g h ∧ GtPtF.IsIota y h
def QkPt.Equiv {k : ℕ} (p p' : QkPt D F k) : Prop :=
  ∃ z : D.X, p'.y = p.y + k • z ∧ ∃ h : GtPtF D F, GtPtF.IsIota z h ∧ GtPtF.IsAdd p.g h p'.g
end GtPoints
section Phi
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace DegPre
def trPt (b : TF (R := R) F ⟶ D.P.A) : BF D F ⟶ BF D F :=
  lift (fst _ _) (padd D.P.A (prB D F) (fst _ _ ≫ b))
def phiφ (y α : D.X) (b : TF (R := R) F ⟶ D.P.A) : Fin 4 ⊕ Fin 4 → ((BF D F).left ⟶ D.P.A.left) :=
  Sum.elim (famφ D F (α + y)) (fun i => (trPt D F b).left ≫ famφ D F α i)
def lineφ (b : TF (R := R) F ⟶ D.P.A) : Fin 2 → ((TF (R := R) F).left ⟶ D.P.A.left) :=
  ![(zeroF D F).left, b.left]
def lineε (k : ℕ) : Fin 2 → ℤ := ![(k : ℤ), -(k : ℤ)]
def constBF (ζ : F) (W : (BF D F).left.Opens) : Γ((BF D F).left, W) :=
  ((BF D F).left.presheaf.map (homOfLE le_top).op).hom
    ((fst (TF (R := R) F) D.P.A).left.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ))
end DegPre
def PhiRel (k : ℕ) (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (s s' : Fam D F k) : Prop :=
  ∀ (α : D.X) (u : LB.Gen (LB.LinComb D.P.L (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k))),
    u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) →
    GeneratorPullback.SecRel D.P.L (DegPre.famφ D F (α + p.y)) (DegPre.famε k) (s'.s (α + p.y))
      (DegPre.famφ D F α) (DegPre.famε k) (s.s α) (DegPre.trPt D F p.g.b).left
      (DegPre.phiφ D F p.y α p.g.b) (DegPre.deltaε k) u
def Fam.IsSmul {k : ℕ} (ζ : F) (s s' : Fam D F k) : Prop :=
  ∀ (α : D.X) (j : Fin 4 → D.P.L.ι), (s'.s α).f j = DegPre.constBF D F ζ _ * (s.s α).f j
def WeilQkIs (k : ℕ) (p p' : QkPt D F k) (ζ : F) : Prop :=
  ∀ (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)))
    (w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p'.g.b) (DegPre.lineε k))),
    w.IsGen → w'.IsGen →
    ∀ s s₁ s₂ s₃ s₄ : Fam D F k,
      PhiRel D F k p' w' s s₁ → PhiRel D F k p w s₁ s₂ →
      PhiRel D F k p w s s₃ → PhiRel D F k p' w' s₃ s₄ →
      Fam.IsSmul D F ζ s₄ s₂
end Phi
section QkToAk
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
abbrev TFK : Over (TK R).left := Over.mk (jFK (R := R) F)
def QkToAk (P' : PolAV (TK R).left) (k : ℕ)
    (E : LB.Sec (LPow P'.A P'.L (k : ℤ) (TFK (R := R) F)) → Fam D F k → Prop)
    (p : QkPt D F k) (x : TFK (R := R) F ⟶ P'.A) : Prop :=
  x ^ k = 1 ∧
    ∀ θ : ThetaGrp P'.A P'.L (k : ℤ) (TFK (R := R) F), θ.pt = x →
      ∃ w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)), w.IsGen ∧
        ∀ (t t' : LB.Sec (LPow P'.A P'.L (k : ℤ) (TFK (R := R) F))) (s s' : Fam D F k),
          E t s → E t' s' → IsActOf P'.A P'.L (k : ℤ) θ t t' → PhiRel D F k p w s s'
end QkToAk
section Bridge
open scoped CategoryTheory.Obj
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace DegPre
abbrev jFR : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R) := jFK (R := R) F ≫ jK R
abbrev BFo : Over (Spec (CommRingCat.of F)) := (Over.pullback (jFR (R := R) F)).obj D.P.A
abbrev prBo : (BFo D F).left ⟶ D.P.A.left := pullback.fst _ _
abbrev overR (Y : Over (Spec (CommRingCat.of F))) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (Y.hom ≫ jFR (R := R) F)
def ptOfBFo {Y : Over (Spec (CommRingCat.of F))} (e : Y ⟶ BFo D F) : overR (R := R) F Y ⟶ D.P.A :=
  Over.homMk (e.left ≫ prBo D F) (by
    simp only [overR, Over.mk_hom, Category.assoc, prBo, pullback.condition]
    rw [← Over.w e]
    rfl)
def oFφ {Y : Over (Spec (CommRingCat.of F))} (e : Y ⟶ BFo D F) (χ : D.X) :
    Fin 4 → (Y.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (ptOfBFo D F e) (toUnit _ ≫ D.c χ)).left, (toUnit (overR (R := R) F Y) ≫ D.c χ).left,
    (ptOfBFo D F e).left, (toUnit (overR (R := R) F Y) ≫ η[D.P.A]).left]
def oFε : Fin 4 → ℤ := ![1, -1, -1, 1]
end DegPre
structure SplitExtIsD (E : SplitExt (Spec (CommRingCat.of F))) where
  e : E.B ≅ DegPre.BFo D F
  hom : IsMonHom e.hom
  chi : D.X ≃+ E.X
  oIso : ∀ χ : D.X,
    ∃ t : LB.Iso (LB.LinComb D.P.L (DegPre.oFφ D F e.hom χ) DegPre.oFε) (E.O (chi χ)).L, t.IsGen
def GtPtBridgeSt : Prop :=
  ∀ (E : SplitExt (Spec (CommRingCat.of F))) (h : SplitExtIsD D F E)
    (G : Over (Spec (CommRingCat.of F))) [GrpObj G] (Dat : E.GtDatum G),
    ∃ φ : (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) ≃ GtPtF D F,
      (∀ x x', GtPtF.IsAdd (φ x) (φ x') (φ (x * x'))) ∧
      ∀ x, (φ x).b.left = (x ≫ Dat.q ≫ h.e.hom).left ≫ DegPre.prBo D F
end Bridge
end ReciprocityTheory.ChartRestriction.G.Out


