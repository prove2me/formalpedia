-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:48.226617+00:00
-- url     : https://prove2.me/theorems/f350273c-9504-44df-89cb-005cffdf5663
-- title:
--   Section Of Line Bundle One
-- statement:
--   Definitions and structural lemmas for Section Of Line Bundle One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SectionOfLineBundleOne.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
abbrev ArcLt (Dw : Datum H) : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ) × Fin (Dw.mult τ)
def arcDet (Dw : Datum H) (K₁ : Type) [Field K₁] : MvPolynomial (ArcLt Dw) (LaurentSeries K₁) :=
  ∏ τ : E →+* ℂ, Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K₁)))
abbrev ArcS (Dw : Datum H) (K₁ : Type) [Field K₁] : Type := Localization.Away (arcDet Dw K₁)
def arcX (Dw : Datum H) (K₁ : Type) [Field K₁] (τ : E →+* ℂ) (i k : Fin (Dw.mult τ)) : ArcS Dw K₁ :=
  algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw))
def arcι (Dw : Datum H) (K₁ : Type) [Field K₁] : PowerSeries K₁ →+* ArcS Dw K₁ :=
  (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁)).comp
    ((MvPolynomial.C).comp (HahnSeries.ofPowerSeries ℤ K₁))
variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def IsLieImage {Y : Model Xo c β} {K₁ : Type} [Field K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b}
    {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (ν : ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁)) (v : epsR (PowerSeries K₁) ⟶ W.t.G) : Prop :=
  ∀ (n : ℕ) (ρ : DualNumber (PowerSeries K₁) →+* DualNumber (PowerSeries K₁ ⧸ Ideal.span {PowerSeries.X} ^ (n + 1)))
    (κ : DualNumber K₁ →+* DualNumber (PowerSeries K₁ ⧸ Ideal.span {(PowerSeries.X : PowerSeries K₁)} ^ (n + 1)))
    (vn : Sp (DualNumber (PowerSeries K₁ ⧸ Ideal.span {(PowerSeries.X : PowerSeries K₁)} ^ (n + 1))) ⟶
      (ReciprocityTheory.ChartRestriction.G.Out.thickObj (PowerSeries K₁) (Ideal.span {PowerSeries.X}) n W.t.G).left),
    (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ r)) → ρ DualNumber.eps = DualNumber.eps →
    (∀ r, κ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Ideal.Quotient.mk _ (PowerSeries.C r))) →
    κ DualNumber.eps = DualNumber.eps →
    vn ≫ (ReciprocityTheory.ChartRestriction.G.Out.thickObj (PowerSeries K₁) (Ideal.span {PowerSeries.X}) n W.t.G).hom =
      spMap (algebraMap (PowerSeries K₁ ⧸ Ideal.span {(PowerSeries.X : PowerSeries K₁)} ^ (n + 1))
        (DualNumber (PowerSeries K₁ ⧸ Ideal.span {(PowerSeries.X : PowerSeries K₁)} ^ (n + 1)))) →
    vn ≫ (ReciprocityTheory.ChartRestriction.G.Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left = spMap ρ ≫ v.left →
    ∀ x, GenRelR W.w (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) vn) (LB.pullGen _ _ _ (ν.s x) (spMap κ))
def IsArcPointPowerSeries (Y : Model Xo c β) {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} (a : ArcIn Dw l β K₁ b)
    (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁))
    [Algebra c.F (ArcS Dw K₁)] (yF : FrPt Xo c (ArcS Dw K₁)) : Prop :=
  χ ≫ Y.s = spMap (PowerSeries.C (R := K₁)) ≫ spMap b ∧
  (∃ z : Sp (ArcS Dw K₁) ⟶ Xo.XF c, z ≫ Y.j = spMap (arcι Dw K₁) ≫ χ ∧ z ≫ pullback.fst _ _ = yF.x) ∧
  ∃ v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (PowerSeries K₁) ⟶ W.t.G),
    (∀ τ k, IsLieImage W (e τ k) (v τ k)) ∧
    ∀ τ i, ∃ vS : Fin (Dw.mult τ) → (Sp (DualNumber (ArcS Dw K₁)) ⟶ Xo.univ.t.G.left),
      (∀ k, ∃ v'' : Sp (DualNumber (ArcS Dw K₁)) ⟶ Y.oF.t.G.left,
        v'' ≫ Y.m.φ = spMap (dualMap (arcι Dw K₁)) ≫ (v τ k).left ≫ W.m.φ ∧ vS k = v'' ≫ Y.m0.toSABMap.φ) ∧
      IsCombAt yF.x vS (fun k => arcX Dw K₁ τ i k) (yF.u τ i)
def SectionOfLineBundleOne {X : Scheme.{0}} {L : LB X} (σ : ReciprocityTheory.ChartRestriction.G.Out.H0 L 1) (θ : LB.Sec L) : Prop :=
  ∀ (j : Fin 1 → L.ι) (h : LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0)),
    σ.f j = (X.presheaf.map (homOfLE h).op).hom (θ.f (j 0))
def IsArcPt3At (Y : Model Xo c β) {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} (a : ArcIn Dw l β K₁ b)
    (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    [Algebra c.F (ArcS Dw K₁)] (yF : FrPt Xo c (ArcS Dw K₁)) (th : a.D₀.P.L.Sec) : Prop :=
  ∃ (σ : ReciprocityTheory.ChartRestriction.G.Out.H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x)
    (θ' : LB.Sec W.P.U.LG.L) (θ : LB.Sec W.t.PP.L),
    (∃ j, th.f j ≠ 0) ∧ (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 (show _ from σ) fam) ∧
    (∀ (j : Fin 4 → W.P.D.toPre.P.L.ι) (j₀ : a.D₀.P.L.ι) (V : W.P.D.toPre.P.A.left.Opens)
      (h₁ : V ≤ LB.wchart W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j)
      (h₂ : V ≤ (LB.div (a.D₀.P.L.pull W.φ) W.P.D.toPre.P.L).U (fun _ => j₀, j 1)) (h₃ : V ≤ W.φ ⁻¹ᵁ a.D₀.P.L.U j₀),
      LB.Coh W.P.D.toPre.P.L (W.P.D.toPre.famφB 0) j →
      (W.φ.appLE _ _ h₃).hom (th.f j₀) = resG _ h₂ (W.w.s (fun _ => j₀, j 1)).val * resG _ h₁ ((fam 0).f j)) ∧
    SectionOfLineBundleOne σ θ' ∧ HEq θ θ' ∧
    ∃ (t' : SAB H (Sp (ArcS Dw K₁))) (m1 : SABMap t' Xo.univ.t yF.x) (m2 : SABMap t' W.t (spMap (arcι Dw K₁)))
      (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (W.t.PP.L.pull m2.φ))
      (σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (W.t.PP.L.pull m2.φ)),
      (∃ g : t'.G.left ⟶ Y.oF.t.G.left, g ≫ Y.m0.toSABMap.φ = m1.φ ∧ g ≫ Y.m.φ = m2.φ ≫ W.m.φ) ∧
      RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ' s1 ∧ IsoMaps w2 σ' θ2 ∧ PullSec m2.φ θ θ2 ∧
      ∀ g : t'.G.left ⟶ Gx yF.x, g ≫ (snd (Over.mk yF.x) Xo.univ.t.G).left = m1.φ →
        g ≫ (fst (Over.mk yF.x) Xo.univ.t.G).left = t'.G.hom →
        ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx yF.x).U (fun _ => j PUnit.unit)),
          s1.f j = (g.appLE _ _ h).hom (yF.s.f (fun _ => j PUnit.unit))
def IsArcPt3 (Y : Model Xo c β) {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} (a : ArcIn Dw l β K₁ b)
    (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    [Algebra c.F (ArcS Dw K₁)] (yF : FrPt Xo c (ArcS Dw K₁)) : Prop :=
  ∃ th : a.D₀.P.L.Sec, IsArcPt3At Y a χ W yF th
def IsArcPt (Y : Model Xo c β) {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} (a : ArcIn Dw l β K₁ b)
    (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁))
    [Algebra c.F (ArcS Dw K₁)] (yF : FrPt Xo c (ArcS Dw K₁)) : Prop :=
  IsArcPointPowerSeries Y a χ W e yF ∧ IsArcPt3 Y a χ W yF
def ArcLieBasis {Y : Model Xo c β} {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b}
    {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁)) : Prop :=
  ∃ v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR (PowerSeries K₁) ⟶ W.t.G),
    (∀ τ k, IsLieImage W (e τ k) (v τ k)) ∧
    ∀ τ : E →+* ℂ,
      let eig : (epsR (PowerSeries K₁) ⟶ W.t.G) → Prop := fun w => ∀ x : 𝓞 E,
        (w ≫ W.t.act.act x).left =
          spMap (epsScaleR (PowerSeries.C (R := K₁) (algebraMap c.F K₁ (embK c τ x)))) ≫ w.left
      (∀ k, IsTangent (v τ k) ∧ eig (v τ k)) ∧
      ∀ w, IsTangent w → eig w → ∃! cf : Fin (Dw.mult τ) → PowerSeries K₁, IsLieComb cf (v τ) w
def ArcPtExSt : Prop :=
  ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (K₁ : Type) [Field K₁] [Algebra c.F K₁]
    (b : O →+* K₁) (a : ArcIn Dw l β K₁ b) (χ : Sp (PowerSeries K₁) ⟶ Y.X)
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ReciprocityTheory.ChartRestriction.G.Out.GtPt a.D₀ (epsR K₁)) [Algebra c.F (ArcS Dw K₁)],
    (∃ r z : O, ((β r : c.F) : ℂ) = H.rt0 ∧ ((β z : c.F) : ℂ) = zeta l.A) →
    χ ≫ Y.s = spMap (PowerSeries.C (R := K₁)) ≫ spMap b →
    (∀ x : Sp (PowerSeries K₁), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) →
    (∀ r : O, algebraMap c.F K₁ (β r) = b r) →
    (∀ r : c.F, algebraMap c.F (ArcS Dw K₁) r = arcι Dw K₁ (PowerSeries.C (R := K₁) (algebraMap c.F K₁ r))) →
    ArcLieBasis W e →
    ∃ yF : FrPt Xo c (ArcS Dw K₁), IsArcPt Y a χ W e yF
end Formalism.L2.Pj


