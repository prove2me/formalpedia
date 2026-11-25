-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PointDataQ
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_PointDataQ
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:07.959398+00:00
-- url     : https://prove2.me/theorems/e9e64763-ded4-4765-80e9-3127ec705c16
-- title:
--   Point Data Q
-- statement:
--   Definitions and structural lemmas for Point Data Q, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/PointDataQ.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt FB)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData
section ColVal
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
def colExp {κ : Type} [Fintype κ] {n : ℕ} (a : κ × Fin n →₀ ℕ) (i : Fin n) : κ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun l => a (l, i)
def colValOf (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O) (m : ℕ)
    {κ : Type} [Fintype κ] (u : κ → Fin d → k) {n : ℕ} (P : MvPolynomial (κ × Fin n) k) (f : Fin n → PS k 1 d) : k :=
  ∑ a ∈ P.support, P.coeff a * ∏ i, B.nabVal k h w0 m (f i) u (MvPolynomial.monomial (colExp a i) 1)
end ColVal
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}
structure PtData (P : PELUnif (maximalIdeal V) t) (F : Type) [Field F] [CharZero F] [Algebra (FractionRing V) F] where

  complete : IsAdicComplete (maximalIdeal V) V

  tors : P.TorsionIso

  ϖ : V
  irr : Irreducible ϖ

  Q_vw : P.D.toPre.X → ℤ
  isQ : DVR.QForm.IsQ P.D.toPre ϖ Q_vw
  algClosed : IsAlgClosed F

  v_vw : AddValuation F (WithTop ℚ)
  valOver : DVR.ValOver ϖ F v_vw

  d : ℕ
  x : GlobalTheory.JetSer.Fam t.G (Fin d)
  chart : Chart.IsUnivChart t.G d x

  j : t.PP.L.ι
  hj : ⊤ ≤ η[t.G].left ⁻¹ᵁ t.PP.L.U j

  u : ∀ a : 𝓞 E, LB.Gen (LB.LinComb t.PP.L (Out.rosatiφ t.G (t.act.act a) (t.act.act (H.bar a))) Out.rosatiε)
  u_norm : ∀ a, GlobalTheory.JetSer.IsNormRos t.PP.L _ _ (u a)

  ρ : LB.Gen (LB.LinComb t.PP.L (GlobalTheory.JetSer.primφ (t.act.act H.w0)) GlobalTheory.JetSer.primε)
  ρ_gen : ρ.IsGen
  ρ_rig : LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ ρ (eSec t.G)) t.PP.rig

  B : letI := H.starRing; FB V d (𝓞 E)
  isFB : letI := H.starRing; GlobalTheory.JetSer.IsFBOf t.PP t.cub t.act u x j B
def secL (P : PELUnif (maximalIdeal V) t) {q : ℕ} (σ : Out.H0 P.U.LG.L q) : Out.H0 t.PP.L q :=
  Eq.rec (motive := fun L _ => Out.H0 (RigLB.L L) q) σ P.bundle
namespace PtData
variable {P : PELUnif (maximalIdeal V) t} {F : Type} [Field F] [CharZero F] [Algebra (FractionRing V) F]
  (D : PtData P F)
def IsIntGerm (q : ℕ) (σ : Out.H0 t.PP.L q) (g : PS V 1 D.d) : Prop :=
  ∃ a r : PS V 1 D.d, GlobalTheory.JetSer.IsSer1 D.x _ (σ.f fun _ => D.j) a ∧
    GlobalTheory.JetSer.IsSer1 D.x _ (D.ρ.s fun _ => D.j).val r ∧ g * r ^ q = a
def IsGerm (q : ℕ) (s : Out.Fam P.D.toPre F q) (f : PS F 1 D.d) : Prop :=
  ∃ (n : ℕ) (c : Fin n → F) (σ : Fin n → Out.H0 P.U.LG.L q) (τ : Fin n → ∀ χ, P.D.toPre.SecB q χ)
    (g : Fin n → PS V 1 D.d),
    (∀ i e, P.U.toUnifPre.ExpandsAt e q (σ i) (τ i)) ∧
    (∀ χ, Out.GeneratorPullback.SecLin P.D.toPre.P.L (Out.DegPre.famφ P.D.toPre F χ) (Out.DegPre.famε q) (s.s χ)
      (P.D.toPre.famφB χ) (Out.DegPre.famε q) (fun i => τ i χ) (Out.DegPre.prB P.D.toPre F).left
      (fun i => Out.scal (fst (Out.TF (R := V) F) P.D.toPre.P.A).left (c i))) ∧
    (∀ i, D.IsIntGerm q (secL P (σ i)) (g i)) ∧
    f = ∑ i, c i • MvPowerSeries.map (DVR.TWO.algVF (V := V) (F := F)) (g i)
def Gauge : Type :=
  letI := H.starRing
  letI : Algebra V F := (DVR.TWO.algVF (V := V) (F := F)).toAlgebra
  {h : PS F 2 D.d // D.B.IsCanonGauge F h}
def colVal (h : D.Gauge) (m : ℕ) {κ : Type} [Fintype κ] (u : κ → Fin D.d → F) {n : ℕ}
    (Pol : MvPolynomial (κ × Fin n) F) (f : Fin n → PS F 1 D.d) : F :=
  letI := H.starRing
  letI : Algebra V F := (DVR.TWO.algVF (V := V) (F := F)).toAlgebra
  colValOf D.B F h.1 H.w0 m u Pol f
end PtData
def GermSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (F : Type) [Field F] [CharZero F] [Algebra (FractionRing V) F] (D : PtData P F) (q : ℕ), 1 ≤ q →
    (∀ s, ∃! f, D.IsGerm q s f) ∧
    (∀ s s' s'' f f', DVR.FamIsAdd P.D F s s' s'' → D.IsGerm q s f → D.IsGerm q s' f' → D.IsGerm q s'' (f + f')) ∧
    ∀ (ζ : F) s s' f, Out.Fam.IsSmul P.D.toPre F ζ s s' → D.IsGerm q s f → D.IsGerm q s' (ζ • f)
def GermValSt_vw : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (F : Type) [Field F] [CharZero F] [Algebra (FractionRing V) F] (D : PtData P F) (q : ℕ), 1 ≤ q →
    ∀ (s : Out.Fam P.D.toPre F q) (f : PS F 1 D.d), D.IsGerm q s f → ∀ r : ℚ,
      ((∀ χ, DVR.VGe P.D F D.v_vw q χ (s.s χ) r) →
        ∀ a, ((r : ℚ) : WithTop ℚ) ≤ D.v_vw (MvPowerSeries.coeff a f)) ∧
      ∀ (χ₀ : P.D.toPre.X) (y : F), DVR.Val0 P.D F q χ₀ (s.s χ₀) y →
        (∀ χ, χ ≠ χ₀ → ∃ r' : ℚ, r < r' ∧ DVR.VGe P.D F D.v_vw q χ (s.s χ) r') →
        ((r : ℚ) : WithTop ℚ) < D.v_vw (MvPowerSeries.constantCoeff f - y) ∧
          (D.v_vw y = ((r : ℚ) : WithTop ℚ) → D.v_vw (MvPowerSeries.constantCoeff f) = ((r : ℚ) : WithTop ℚ))
def PtDataExSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V →
    ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t), P.TorsionIso → ∀ ϖ : V, Irreducible ϖ →
    (∀ [CharZero (AlgebraicClosure (FractionRing V))],
      ∃ D : PtData P (AlgebraicClosure (FractionRing V)), D.ϖ = ϖ) ∧
    ∀ (F : Type) [Field F] [CharZero F] [Algebra (FractionRing V) F], IsAlgClosed F →
      ∀ v : AddValuation F (WithTop ℚ), DVR.ValOver ϖ F v → ∃ D : PtData P F, D.ϖ = ϖ ∧ D.v_vw = v
section Basic₂
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
end Basic₂
end GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData


