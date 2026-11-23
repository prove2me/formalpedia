-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_TorusPointForms
-- name    : Development_AbelianVarietyTheory_BlockTheory_UniformisationCharts_TorusPointForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:27.486413+00:00
-- url     : https://prove2.me/theorems/bf73ccf3-c72a-4ea5-b9f3-c8074e703f98
-- title:
--   Torus Point Forms
-- statement:
--   Definitions and structural lemmas for Torus Point Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/UniformisationCharts/TorusPointForms.lean

import Mathlib
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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] SplitExt.free SplitExt.finite
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
abbrev cPt (T : Over (Spec (CommRingCat.of R))) (χ : D.X) : T ⟶ D.P.A := toUnit T ≫ D.c χ
def oφ {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) :
    Fin 4 → (T.left ⟶ D.P.A.left) :=
  ![(padd D.P.A b (cPt D T χ)).left, (cPt D T χ).left, b.left, (pzero D.P.A T).left]
def oε : Fin 4 → ℤ := ![1, -1, -1, 1]
def oεInv : Fin 4 → ℤ := ![-1, 1, 1, -1]
abbrev oLB {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) : LB T.left :=
  LB.LinComb D.P.L (oφ D b χ) oε
abbrev oInvLB {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ : D.X) : LB T.left :=
  LB.LinComb D.P.L (oφ D b χ) oεInv
def cubAt {T : Over (Spec (CommRingCat.of R))} (x x' x'' : T ⟶ D.P.A) :=
  LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift x (lift x' x'')).left
variable (F : Type) [Field F] [Algebra (FractionRing R) F]
structure GtPt where

  base : TF (R := R) F ⟶ D.P.A

  form : ∀ χ : D.X, LB.Gen (oInvLB D base χ)
  form_gen : ∀ χ : D.X, (form χ).IsGen
  form_mul : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
    (LB.mulGen D.P.L _ _ _ _ (form (χ + χ')) (cubAt D (cPt D _ χ) (cPt D _ χ') base))
    (LB.mulGen D.P.L _ _ _ _ (form χ) (form χ'))
namespace GtPt
variable {D F}
def IsAdd (g g' h : GtPt D F) : Prop :=
  h.base = padd D.P.A g.base g'.base ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (h.form χ) (cubAt D (cPt D _ χ) g.base g'.base))
      (LB.mulGen D.P.L _ _ _ _ (g.form χ) (g'.form χ))
def IsZero (g : GtPt D F) : Prop :=
  g.base = pzero D.P.A _ ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (g.form χ) (LB.oneGen D.P.L)
inductive IsNsmul (g : GtPt D F) : ℕ → GtPt D F → Prop
  | zero (h : GtPt D F) : IsZero h → IsNsmul g 0 h
  | succ (k : ℕ) (h h' : GtPt D F) : IsNsmul g k h → IsAdd h g h' → IsNsmul g (k + 1) h'
def IsIo (y : D.X) (g : GtPt D F) : Prop :=
  g.base = cPt D _ y ∧
    ∀ χ : D.X, LB.Gen.Corr D.P.L _ _ _ _ (g.form χ)
      (LB.pullGen D.P.L _ _ (D.io y χ) (jFK (R := R) F))
end GtPt
def QPair (k : ℕ) : Type :=
  {p : D.X × GtPt D F // ∃ h : GtPt D F, p.2.IsNsmul k h ∧ GtPt.IsIo p.1 h}
def QRel (k : ℕ) (p p' : QPair D F k) : Prop :=
  ∃ (z : D.X) (w : GtPt D F), GtPt.IsIo z w ∧ p'.1.1 = p.1.1 + k • z ∧ GtPt.IsAdd p.1.2 w p'.1.2
def Qk (k : ℕ) : Type := Quot (QRel D F k)
namespace Qk
variable {D F} {k : ℕ}
def mk (p : QPair D F k) : Qk D F k := Quot.mk _ p
def IsAdd (a b c : Qk D F k) : Prop :=
  ∃ p p' p'' : QPair D F k, mk p = a ∧ mk p' = b ∧ mk p'' = c ∧
    p''.1.1 = p.1.1 + p'.1.1 ∧ GtPt.IsAdd p.1.2 p'.1.2 p''.1.2
def IsZero (a : Qk D F k) : Prop :=
  ∃ p : QPair D F k, mk p = a ∧ p.1.1 = 0 ∧ p.1.2.IsZero
def toQuot : Qk D F k → D.X ⧸ (nsmulAddMonoidHom (α := D.X) k).range :=
  Quot.lift (fun p => QuotientAddGroup.mk p.1.1) (by
    rintro p p' ⟨z, -, -, hz, -⟩
    refine QuotientAddGroup.eq.2 ⟨z, ?_⟩
    rw [hz]; simp)
end Qk
def GroupLawSt : Prop :=
  ∃ _ : AddCommGroup (GtPt D F),
    (∀ g g' h : GtPt D F, g.IsAdd g' h ↔ g + g' = h) ∧
    (∀ g : GtPt D F, g.IsZero ↔ g = 0) ∧
    (∀ (k : ℕ) (g h : GtPt D F), g.IsNsmul k h ↔ k • g = h)
def IoQSt : Prop :=
  D.TauBimult →
    (∀ y : D.X, ∃! g : GtPt D F, GtPt.IsIo y g) ∧
    (∀ (y y' : D.X) (g g' h : GtPt D F), GtPt.IsIo y g → GtPt.IsIo y' g' →
      GtPt.IsIo (y + y') h → g.IsAdd g' h) ∧
    ∀ k : ℕ, Equivalence (QRel D F k) ∧
      ∃ _ : AddCommGroup (Qk D F k),
        (∀ a b c : Qk D F k, a.IsAdd b c ↔ a + b = c) ∧ (∀ a : Qk D F k, a.IsZero ↔ a = 0)
abbrev baseF : Over (Spec (CommRingCat.of F)) :=
  (Over.pullback (jFK (R := R) F ≫ jK R)).obj D.P.A
def toB {B' : Over (Spec (CommRingCat.of F))} (β : B' ≅ baseF D F) :
    Over.mk (B'.hom ≫ jFK (R := R) F ≫ jK R) ⟶ D.P.A :=
  Over.homMk (β.hom.left ≫ pullback.fst D.P.A.hom (jFK (R := R) F ≫ jK R)) (by
    have h : β.hom.left ≫ pullback.snd D.P.A.hom (jFK (R := R) F ≫ jK R) = B'.hom := Over.w β.hom
    simp only [Over.mk_hom, Category.assoc]
    erw [pullback.condition]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jFK (R := R) F ≫ jK R) h))
def IsDatumIso (E : SplitExt (Spec (CommRingCat.of F))) (β : E.B ≅ baseF D F)
    (ξ : E.X ≃+ D.X) : Prop :=
  IsMonHom β.hom ∧
    ∀ χ : E.X, ∃ t : LB.Iso (E.O χ).L (oLB D (toB D F β) (ξ χ)), t.IsGen
def IsPointCorr {E : SplitExt (Spec (CommRingCat.of F))} (β : E.B ≅ baseF D F)
    {G : Over (Spec (CommRingCat.of F))} [GrpObj G] (q : G ⟶ E.B)
    (e : (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) ≃ GtPt D F) : Prop :=
  (∀ x x', (e x).IsAdd (e x') (e (padd G x x'))) ∧
    (e η[G]).IsZero ∧
    ∀ x, (e x).base.left = (x ≫ q).left ≫ (toB D F β).left
def PointsOfGtSt : Prop :=
  ∀ (E : SplitExt (Spec (CommRingCat.of F))) (β : E.B ≅ baseF D F) (ξ : E.X ≃+ D.X),
    IsDatumIso D F E β ξ →
    ∀ (G : Over (Spec (CommRingCat.of F))) [GrpObj G] (d : E.GtDatum G),
      ∃ e : (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) ≃ GtPt D F, IsPointCorr D F β d.q e
def PointsOfGtCoordSt : Prop :=
  ∀ (E : SplitExt (Spec (CommRingCat.of F))) (β : E.B ≅ baseF D F) (ξ : E.X ≃+ D.X),
    IsDatumIso D F E β ξ →
    ∀ (G : Over (Spec (CommRingCat.of F))) [GrpObj G] (d : E.GtDatum G),
      ∃ (e : (𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) ≃ GtPt D F)
        (t : ∀ k, LB.Iso (E.O (E.basis k)).L (oLB D (toB D F β) (ξ (E.basis k)))),
        IsPointCorr D F β d.q e ∧ (∀ k, (t k).IsGen) ∧
        ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of F))) ⟶ G) (j : E.ChartIdx) (j' : Fin 4 → D.P.L.ι)
          (k : Module.Free.ChooseBasisIndex ℤ E.X) (W : (Spec (CommRingCat.of F)).Opens)
          (h₁ : W ≤ (oInvLB D (e x).base (ξ (E.basis k))).U j')
          (h₂ : W ≤ (x ≫ d.q).left ⁻¹ᵁ
            (LB.div (oLB D (toB D F β) (ξ (E.basis k))) (E.O (E.basis k)).L).U (j', j k))
          (h₃ : W ≤ x.left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart j)),
          res (X := Spec (CommRingCat.of F)) h₁ (((e x).form (ξ (E.basis k))).s j') *
              res (X := Spec (CommRingCat.of F)) h₂ (pullU (x ≫ d.q).left _ ((t k).s (j', j k))) =
            res (X := Spec (CommRingCat.of F)) h₃ (pullU x.left _ (d.u j k))
example (g h : GtPt D F) : g.IsNsmul 0 h ↔ h.IsZero :=
  ⟨fun H => by cases H; assumption, GtPt.IsNsmul.zero h⟩
example (k : ℕ) (g h : GtPt D F) (H : g.IsNsmul k h) : h.base = g.base ^ k := by
  induction H with
  | zero h hz => rw [hz.1, pow_zero]; rfl
  | succ k h h' _ ha ih => rw [ha.1, ih, pow_succ]; rfl
example (h : PointsOfGtCoordSt D F) : PointsOfGtSt D F := fun E β ξ hi G _ d => by
  obtain ⟨e, -, he, -⟩ := h E β ξ hi G d
  exact ⟨e, he⟩
end GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms


