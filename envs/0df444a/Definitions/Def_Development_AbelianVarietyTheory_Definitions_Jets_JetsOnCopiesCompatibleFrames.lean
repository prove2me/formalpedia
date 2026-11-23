-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
-- name    : Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:55:59.154337+00:00
-- url     : https://prove2.me/theorems/fc2ee30a-9bd5-4a81-a814-da9123184f3d
-- title:
--   Jets On Copies Compatible Frames
-- statement:
--   Definitions and structural lemmas for Jets On Copies Compatible Frames, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/JetsOnCopiesCompatibleFrames.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_ColValMonomial
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BidegreeTwoJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FramedFamilyStatement
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_BoxTuple
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_BoxLeOfComp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PowGerm
section Jets
variable {V : Type} [CommRing V]
abbrev JetPts (G : Over (Sp V)) (κ : Type) : Type := ∀ m : ℕ, overAt (𝟙 (Sp V)) (Jet V κ m) ⟶ G
def IsUnivJ (G : Over (Sp V)) [GrpObj G] (κ : Type) (z : JetPts G κ) : Prop :=
  (∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) ≫ z (m + 1) = z m) ∧
  (∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V κ m →ₐ[V] V) ≫ z m = 1) ∧
  ∀ (A : Type) [CommRing A] [Algebra V A] (aug : A →ₐ[V] V) (m : ℕ), RingHom.ker aug ^ (m + 1) = ⊥ →
    ∀ y : overAt (𝟙 (Sp V)) A ⟶ G, Formalism.L2.Pj.homAt (𝟙 (Sp V)) aug ≫ y = 1 →
      ∃! ψ : Jet V κ m →ₐ[V] A, aug.comp ψ = jetAug ∧ y = Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ z m
def Match {G : Over (Sp V)} {κ : Type} {N : ℕ} (β : Fin N ≃ κ) (z : JetPts G κ) (x : JetSer.Fam G (Fin N)) : Prop :=
  ∀ m, ∃ ψ : Chart.JetR V (Fin N) m ≃ₐ[V] Jet V κ m,
    (∀ i, ψ (Chart.zR m i) = Ideal.Quotient.mk _ (MvPolynomial.X (β i))) ∧
      (z m).left = spMap (ψ : Chart.JetR V (Fin N) m →+* Jet V κ m) ≫ (x m).left
def oneCol (d : ℕ) : Fin d ≃ Fin 1 × Fin d := (Equiv.uniqueProd (Fin d) (Fin 1)).symm
abbrev Frames {G : Over (Sp V)} {κ : Type} (L : LB G.left) (z : JetPts G κ) : Type :=
  ∀ m : ℕ, LB.Gen (LB.LinComb L (Y := Sp (Jet V κ m)) (K := Fin 1) (fun _ => (z m).left) (fun _ => (1 : ℤ)))
def Frames.Gen {G : Over (Sp V)} {κ : Type} {L : LB G.left} {z : JetPts G κ} (τ : Frames L z) : Prop := ∀ m, (τ m).IsGen
def Frames.Trunc {G : Over (Sp V)} {κ : Type} {L : LB G.left} {z : JetPts G κ} (τ : Frames L z) : Prop :=
  ∀ (m : ℕ) (y : Sp (Jet V κ m)) (J : (Sp (Jet V κ m) ⟶ G.left) → L.ι), Good L y J →
    val (τ (m + 1)) (spMap ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m)) y J =
      val (τ m) (𝟙 _) y J
def GermA [IsDomain V] {I : Ideal V} {D : DegData V I} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Sp V)}
    [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) {κ : Type} [Fintype κ] [DecidableEq κ] (z : JetPts G κ)
    (τ : Frames U.LG.L z) (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] (q : ℕ) (σ' : U.SecGF F q)
    (f : MvPowerSeries κ F) : Prop :=
  ∀ m, ∃ zF : Sp (Jet F κ m) ⟶ (UnifPre.GF (R := V) (G := G) F).left,
    zF ≫ (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left = spMap (algebraMap F (Jet F κ m)) ∧
    zF ≫ UnifPre.gFK (R := V) (G := G) F = spMap (jetCoef (algebraMap V F) κ m) ≫ (z m).left ∧
    ∀ (y : Sp (Jet F κ m)) (J : (Sp (Jet F κ m) ⟶ G.left) → U.LG.L.ι), Good U.LG.L y J →
      sval σ' zF y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m f)) * (val (τ m) (spMap (jetCoef (algebraMap V F) κ m)) y J ^ q).val
def boxSer {k : Type} [CommRing k] {n d : ℕ} (f : Fin n → PS k 1 d) : PS k n d :=
  ∏ i : Fin n, MvPowerSeries.rename (fun p : Fin 1 × Fin d => ((i, p.2) : Fin n × Fin d)) (f i)
def diagSer {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O) (w0 : O) (ε : PS V 2 d) : PS V 1 d :=
  ev (n := 1) ![pt V (n := 1) d 0, comp1 (B.A.act w0) (pt V (n := 1) d 0)] ε
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def IsEL [IsDomain V] {I : Ideal V} {t : SAB H (Sp V)} (P : PELUnif I t) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (act : 𝓞 E → Fin d → PS V 1 d) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t)
    (τ : Frames P.U.LG.L (κ := Fin 1 × Fin d) xT) : Prop :=
  ∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → P.U.LG.L.ι), Good P.U.LG.L y J →
    val (τ m) (𝟙 _) y J =
      val (genCast (congrArg RigLB.L P.bundle).symm _ _ (eLG t (𝟙 (Sp V)) d xT act eT wPT m)) (𝟙 _) y J
def IsEps (t : SAB H (Sp V)) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m)
    (j : t.PP.L.ι) (ε : PS V 2 d) : Prop :=
  ∀ (m : ℕ) (y : Sp (Jet V (Fin 2 × Fin d) m)) (J : (Sp (Jet V (Fin 2 × Fin d) m) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L y J →
    (∀ I : ULift.{0} (Finset (Fin 2)), J (𝟙 _ ≫ cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I) = j) →
    (val (L := t.PP.L) (φ := cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (ε := cε 2)
      (eT m) (𝟙 (Sp (Jet V (Fin 2 × Fin d) m))) y J).val = gs (𝟙 _) y ⊤ (toΓ _ (psJet m ε))
end Jets
def famCast {R : Type} [CommRing R] [IsDomain R] {Dp : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k k' : ℕ}
    (e : k = k') (s : Fam Dp F k) : Fam Dp F k' :=
  e ▸ s
def ThFrame {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (Dd : DegData V (maximalIdeal V)) (ϖ : V)
    (F : Type) [Field F] [Algebra (FractionRing V) F] (θ : Fam Dd.toPre F 1) : Prop :=
  ∃ (σ : Dd.toPre.SecB 1 0)
    (σF : LB.Sec (LB.LinComb Dd.toPre.P.L (DegPre.famφ Dd.toPre F 0) (DegPre.famε 1))),
    GeneratorPullback.SecScal Dd.toPre.P.L (DegPre.famφ Dd.toPre F 0) (DegPre.famε 1) σF
      (Dd.toPre.famφB 0) (DegPre.famε 1) σ (DegPre.prB Dd.toPre F).left 1 ∧
    (∀ j, (θ.s 0).f j = σF.f j) ∧
    ¬ ∃ σ' : Dd.toPre.SecB 1 0, ∀ j, σ.f j = constFn Dd.toPre.P.A.hom _ ϖ * σ'.f j
def StarSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (inst : StarRing (𝓞 E)), (∀ a : 𝓞 E, inst.toStarMul.toInvolutiveStar.toStar.star a = H.bar a) → inst = H.starRing
def UnivConvSt : Prop := ∀ (V : Type) [CommRing V] (G : Over (Sp V)) [GrpObj G] (κ : Type) (z : JetPts G κ), IsUnivJ G κ z →
  ∀ (N : ℕ) (β : Fin N ≃ κ), ∃ x : JetSer.Fam G (Fin N), Chart.IsUnivChart G N x ∧ Match β z x
def UnivPowSt : Prop := ∀ (V : Type) [CommRing V] (G G' : Over (Sp V)) [GrpObj G] [GrpObj G'] (n d : ℕ) (pG : IsPowGrp G' G n)
  (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G), IsUnivJ G (Fin 1 × Fin d) xT → IsUnivJ G' (Fin n × Fin d) (zV pG xT)
def UnivSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), IsUnivJ C.I.G.G (Fin 1 × Fin (chD C.ch)) C.xT
def IntFBSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y),
  letI := io.toAlgebra
  ∃ BT : FB T.V (chD C.ch) (𝓞 E), BT.G.F = C.FT ∧ BT.A.act = C.actT ∧ BT.ph1 = C.ph1T ∧ BT.ph2 = C.ph2T ∧ BT.sy = C.syT ∧ BT.ad = C.adT ∧
    ∀ (F : Type) [Field F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F],
      BT.FK F = C.ch.B.FK F ∧ (∀ a, BT.actK F a = C.ch.B.actK F a) ∧
      (∀ h, BT.IsCanonGauge F h ↔ C.ch.B.IsCanonGauge F h) ∧
      C.ch.B.IsCanonGauge F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h)
def EigDirSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y),
  letI := io.toAlgebra
  ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (dAct T.Fr C.ch.B a).mulVec (C.ch.uvec ℓ) = io (embK c ℓ.1 a) • C.ch.uvec ℓ
def AGermSt : Prop := ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
    (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (κ : Type) [Fintype κ] [DecidableEq κ] (z : JetPts G κ), IsUnivJ G κ z →
  ∀ τ : Frames U.LG.L z, τ.Gen →
  ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ),
    (∀ σ' f f', GermA U.toUnifPre z τ F q σ' f → GermA U.toUnifPre z τ F q σ' f' → f = f') ∧
    (∀ (l : ℕ) (c : Fin l → F) (σ : Fin l → U.SecGF F q) (f : Fin l → MvPowerSeries κ F) (σ' : U.SecGF F q),
      (∀ i, GermA U.toUnifPre z τ F q (σ i) (f i)) →
      (∀ jj, σ'.f jj = ∑ i, resTop _ (scal (CartesianMonoidalCategory.fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i)) * (σ i).f jj) →
      GermA U.toUnifPre z τ F q σ' (∑ i, c i • f i)) ∧
    (τ.Trunc → ∀ σ', ∃ f, GermA U.toUnifPre z τ F q σ' f)
def AIntSt : Prop := ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀
    (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (κ : Type) [Fintype κ] [DecidableEq κ] (z : JetPts G κ), IsUnivJ G κ z →
  ∀ τ : Frames U.LG.L z, τ.Gen →
  ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ q : ℕ, 1 ≤ q →
  ∀ (σ' : U.SecGF F q) (s : Fam D.toPre F q) (f : MvPowerSeries κ F), U.ExpandsG F q σ' s → GermA U.toUnifPre z τ F q σ' f →
    (∀ α, VGe D F v q α (s.s α) 0) → ∀ e, 0 ≤ v (MvPowerSeries.coeff e f)
def AValSt : Prop := ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀
    (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (κ : Type) [Fintype κ] [DecidableEq κ] (z : JetPts G κ), IsUnivJ G κ z →
  ∀ τ : Frames U.LG.L z, τ.Gen →
  ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] [IsAlgClosed F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ q : ℕ, 1 ≤ q →
  ∀ (σ' : U.SecGF F q) (s : Fam D.toPre F q) (f : MvPowerSeries κ F), U.ExpandsG F q σ' s → GermA U.toUnifPre z τ F q σ' f →
    (∀ r : ℚ, (∀ α, VGe D F v q α (s.s α) r) → ∀ e, ((r : ℚ) : WithTop ℚ) ≤ v (MvPowerSeries.coeff e f)) ∧
    ∀ (χ : D.toPre.X) (x : F) (r r' : ℚ), Val0 D F q χ (s.s χ) x → v x = (r : ℚ) → r < r' →
      (∀ β, β ≠ χ → VGe D F v q β (s.s β) r') → v (MvPowerSeries.constantCoeff f) = (r : ℚ)
def AJetSt : Prop := ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀
    (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal V) D A G) (κ : Type) [Fintype κ] [DecidableEq κ] (z : JetPts G κ), IsUnivJ G κ z →
  ∀ τ : Frames U.LG.L z, τ.Gen → τ.Trunc →
  ∀ (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q → ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ D.toPre.X), 0 ≤ Φ → 0 ≤ M0 →
    (∀ j, (Q (b j) : ℝ) ≤ Φ) → (∀ j w, |((Q (b j + w) - Q (b j) - Q w : ℤ) : ℝ)| ≤ M0 * Q w) →
  ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] [IsAlgClosed F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ q Dg : ℕ, 4 * Dg + 4 ≤ q → (Dg : ℝ) * M0 < q →
  ∀ f : MvPowerSeries κ V, ∃ (s : Fam D.toPre F q) (σ' : U.SecGF F q) (g : MvPowerSeries κ F) (lam : F),
    NuGe D Q F v q s 0 ∧ U.ExpandsG F q σ' s ∧ GermA U.toUnifPre z τ F q σ' g ∧ lam ≠ 0 ∧
    (∃ ρ : ℚ, v lam = (ρ : WithTop ℚ) ∧ (ρ : ℝ) ≤ (Dg : ℝ) ^ 2 * Φ / q) ∧
    ∀ e : κ →₀ ℕ, e.degree ≤ Dg → MvPowerSeries.coeff e g = lam * algebraMap V F (MvPowerSeries.coeff e f)
def Frame1St : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (d : ℕ) (FT : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d)
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
    IsChartG t (𝟙 (Sp V)) d FT act tg (fun j : Fin d => Pi.single j (1 : V)) xT → IsFrameG t (𝟙 (Sp V)) d xT FT act ph1 ph2 sy ad eT → IsPrimG t wPT →
  ∃ τ : Frames P.U.LG.L (κ := Fin 1 × Fin d) xT, τ.Gen ∧ IsEL P xT act eT wPT τ ∧ (FrTrunc t (𝟙 (Sp V)) d xT eT → τ.Trunc)
def FrameNSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (d : ℕ) (FT : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d)
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
    IsChartG t (𝟙 (Sp V)) d FT act tg (fun j : Fin d => Pi.single j (1 : V)) xT → IsFrameG t (𝟙 (Sp V)) d xT FT act ph1 ph2 sy ad eT → IsPrimG t wPT →
  ∀ (n : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G']
    (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n)
    (U' : Unif (maximalIdeal V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U),
  ∃ τ : Frames U'.LG.L (κ := Fin n × Fin d) (zV pG xT), τ.Gen ∧ (FrTrunc t (𝟙 (Sp V)) d xT eT → τ.Trunc) ∧
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ) (σ' : U'.toUnifPre.SecGF F q) (f : PS F n d),
      IsGermN P xT act eT wPT pG PU.toUnifPowOf F q σ' f ↔ GermA U'.toUnifPre (κ := Fin n × Fin d) (zV pG xT) τ F q σ' f
def BoxGermSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t)
    (d : ℕ) (FT : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d)
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
    IsChartG t (𝟙 (Sp V)) d FT act tg (fun j : Fin d => Pi.single j (1 : V)) xT → IsFrameG t (𝟙 (Sp V)) d xT FT act ph1 ph2 sy ad eT → IsPrimG t wPT →
  ∀ τ : Frames P.U.LG.L (κ := Fin 1 × Fin d) xT, τ.Gen → IsEL P xT act eT wPT τ →
  ∀ (n : ℕ) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G']
    (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' t.G n)
    (U' : Unif (maximalIdeal V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (q : ℕ), 1 ≤ q →
  ∀ (σ : Fin n → P.U.toUnifPre.SecGF F q) (s : Fin n → Fam P.D.toPre F q) (f : Fin n → PS F 1 d)
    (σ' : U'.toUnifPre.SecGF F q) (S : Fam D'.toPre F q),
    (∀ i, P.U.toUnifPre.ExpandsG F q (σ i) (s i) ∧ GermA P.U.toUnifPre (κ := Fin 1 × Fin d) xT τ F q (σ i) (f i)) →
    IsBoxFam pD F q S s → U'.toUnifPre.ExpandsG F q σ' S → IsGermN P xT act eT wPT pG PU.toUnifPowOf F q σ' (boxSer f)
def LinkLawSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)),
  letI := H.starRing
  ∀ (d : ℕ) (BT : FB V d (𝓞 E))
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
    IsChartG t (𝟙 (Sp V)) d BT.G.F BT.A.act tg (fun j : Fin d => Pi.single j (1 : V)) xT →
    IsFrameG t (𝟙 (Sp V)) d xT BT.G.F BT.A.act BT.ph1 BT.ph2 BT.sy BT.ad eT → IsPrimG t wPT →
  ∀ x : JetSer.Fam t.G (Fin d), Chart.IsUnivChart t.G d x → Match (oneCol d) xT x → JetSer.IsLawOf x BT.G.F ∧ ∀ a, JetSer.IsMapOf x x (t.act.act a) (BT.A.act a)
def LinkEpsSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V))
    (d : ℕ) (FT : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (ph1 ph2 : PS V 3 d) (sy : PS V 2 d) (ad : 𝓞 E → PS V 2 d)
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
    IsChartG t (𝟙 (Sp V)) d FT act tg (fun j : Fin d => Pi.single j (1 : V)) xT → IsFrameG t (𝟙 (Sp V)) d xT FT act ph1 ph2 sy ad eT → IsPrimG t wPT → FrTrunc t (𝟙 (Sp V)) d xT eT →
  ∀ j : t.PP.L.ι, ⊤ ≤ η[t.G].left ⁻¹ᵁ t.PP.L.U j → ∃ ε : PS V 2 d, IsEps t xT eT j ε
def LinkRelSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)),
  Function.Surjective (t.G ⊗ t.G).hom.appTop.hom →
  letI := H.starRing
  ∀ (d : ℕ) (BT : FB V d (𝓞 E))
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
    IsChartG t (𝟙 (Sp V)) d BT.G.F BT.A.act tg (fun j : Fin d => Pi.single j (1 : V)) xT →
    IsFrameG t (𝟙 (Sp V)) d xT BT.G.F BT.A.act BT.ph1 BT.ph2 BT.sy BT.ad eT → IsPrimG t wPT →
  ∀ x : JetSer.Fam t.G (Fin d), Chart.IsUnivChart t.G d x → Match (oneCol d) xT x →
  ∀ j : t.PP.L.ι, ⊤ ≤ η[t.G].left ⁻¹ᵁ t.PP.L.U j →
  ∀ (u : ∀ a : 𝓞 E, LB.Gen (LB.LinComb t.PP.L (rosatiφ t.G (t.act.act a) (t.act.act (star a))) rosatiε)),
    (∀ a, JetSer.IsNormRos t.PP.L _ _ (u a)) → ∀ B : FB V d (𝓞 E), JetSer.IsFBOf t.PP t.cub t.act u x j B →
  ∀ ε : PS V 2 d, IsEps t xT eT j ε → JetSer.Related B BT (pt V (n := 1) d 0) (pt V (n := 1) d 0) ε
def LinkSecSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)),
  Function.Surjective t.G.hom.appTop.hom →
  letI := H.starRing
  ∀ (d : ℕ) (BT : FB V d (𝓞 E))
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
    IsChartG t (𝟙 (Sp V)) d BT.G.F BT.A.act tg (fun j : Fin d => Pi.single j (1 : V)) xT →
    IsFrameG t (𝟙 (Sp V)) d xT BT.G.F BT.A.act BT.ph1 BT.ph2 BT.sy BT.ad eT → IsPrimG t wPT →
  ∀ x : JetSer.Fam t.G (Fin d), Chart.IsUnivChart t.G d x → Match (oneCol d) xT x →
  ∀ j : t.PP.L.ι, ⊤ ≤ η[t.G].left ⁻¹ᵁ t.PP.L.U j →
  ∀ (ρ : LB.Gen (LB.LinComb t.PP.L (JetSer.primφ (t.act.act H.w0)) JetSer.primε)), ρ.IsGen →
    LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ ρ (eSec t.G)) t.PP.rig →
  ∀ ε : PS V 2 d, IsEps t xT eT j ε → ∀ (q : ℕ) (σ : H0 t.PP.L q) (r S g : PS V 1 d),
    JetSer.IsSer1 x _ (ρ.s (fun _ => j)).val r → JetSer.IsSer1 x _ (σ.f (fun _ => j)) S → g * (diagSer BT H.w0 ε * r) ^ q = S →
  ∀ (m : ℕ) (y : Sp (Jet V (Fin 1 × Fin d) m)) (J : (Sp (Jet V (Fin 1 × Fin d) m) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L y J →
    sval σ (xT m).left y J = gs (𝟙 _) y ⊤ (toΓ _ (psJet m g)) * (val (eLG t (𝟙 (Sp V)) d xT BT.A.act eT wPT m) (𝟙 (Sp (Jet V (Fin 1 × Fin d) m))) y J ^ q).val
def LinkSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (hc : IsAdicComplete (maximalIdeal V) V) (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (tors : P.TorsionIso)
    (ϖ : V) (hϖ : Irreducible ϖ) (Q : P.D.toPre.X → ℤ) (hQ : IsQ P.D.toPre ϖ Q)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v),
  letI := H.starRing
  ∀ (d : ℕ) (BT : FB V d (𝓞 E))
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (eT : ∀ m, FrTyG t (𝟙 (Sp V)) d xT m) (wPT : PrimTyG t),
    IsChartG t (𝟙 (Sp V)) d BT.G.F BT.A.act tg (fun j : Fin d => Pi.single j (1 : V)) xT →
    IsFrameG t (𝟙 (Sp V)) d xT BT.G.F BT.A.act BT.ph1 BT.ph2 BT.sy BT.ad eT → IsPrimG t wPT → IsUnivJ t.G (Fin 1 × Fin d) xT → FrTrunc t (𝟙 (Sp V)) d xT eT →
  ∀ τ : Frames P.U.LG.L (κ := Fin 1 × Fin d) xT, τ.Gen → IsEL P xT BT.A.act eT wPT τ →
  ∃ x hx j hj u hu B hB ρ hρ, ∃ ε : PS V 2 d, JetSer.Related B BT (pt V (n := 1) d 0) (pt V (n := 1) d 0) ε ∧
    ∀ (q : ℕ) (s : Fam P.D.toPre F q) (f f' : PS F 1 d),
      (FamGerm.Pt1.mk ϖ hϖ hc t P tors Q hQ v hv d x hx j hj u hu B hB ρ hρ : FamGerm.Pt1 E H V F).Germ q s f →
      f' * MvPowerSeries.map (algebraMap V F) (diagSer BT H.w0 ε) ^ q = f →
      ∃ σ' : P.U.toUnifPre.SecGF F q, P.U.toUnifPre.ExpandsG F q σ' s ∧ GermA P.U.toUnifPre (κ := Fin 1 × Fin d) xT τ F q σ' f'
def NabColSt : Prop := ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O), MvPowerSeries.constantCoeff h = 0 →
  ∀ (q n : ℕ) (f : Fin n → PS k 1 d) (Λ Ix : Type) [Fintype Λ] [Fintype Ix] (e : Λ × Fin n → Ix) (cp : Ix → Fin n)
    (u : Λ → Fin d → k) (u' : Ix → Fin d → k), (∀ p, cp (e p) = p.2) → (∀ p, u' (e p) = u p.1) →
  ∀ P : MvPolynomial (Λ × Fin n) k, nabValN B k h w0 q (boxSer f) cp u' (MvPolynomial.rename e P) =
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1)
def NabJetSt : Prop := ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d) (w0 : O) (q n : ℕ) (Ix : Type) [Fintype Ix]
    (cp : Ix → Fin n) (u : Ix → Fin d → k),
  (∀ (P : MvPolynomial Ix k) (f g : PS k n d),
    (∀ e : Fin n × Fin d →₀ ℕ, e.degree ≤ P.totalDegree → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g) →
    nabValN B k h w0 q f cp u P = nabValN B k h w0 q g cp u P) ∧
  (∀ (P : MvPolynomial Ix k) (J : Type) [Fintype J] (c : J → k) (f : J → PS k n d),
    nabValN B k h w0 q (∑ j, c j • f j) cp u P = ∑ j, c j * nabValN B k h w0 q (f j) cp u P) ∧
  ∀ (f : PS k n d) (J : Type) [Fintype J] (c : J → k) (P : J → MvPolynomial Ix k),
    nabValN B k h w0 q f cp u (∑ j, c j • P j) = ∑ j, c j * nabValN B k h w0 q f cp u (P j)
open Classical in

def MinorSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (K : Type) [CommRing K] (typ : (E →+* ℂ) → Prop)
    (m : (E →+* ℂ) → ℕ → ℕ) (n₁ n₂ : ℕ), (∀ τ s, m τ s ≠ 0 → 1 ≤ s ∧ s ≤ Dw.mult τ ∧ s ≤ (if typ τ then n₁ else n₂)) →
  ∃ (rk : (E →+* ℂ) → ℕ) (hrk : ∀ τ, rk τ ≤ Dw.mult τ) (col : ∀ τ, Fin (rk τ) → Fin (n₁ + n₂)) (m' : ∀ τ, Fin (rk τ) → ℕ),
    (∀ τ, Function.Injective (col τ)) ∧ (∀ τ i, (col τ i).val < n₁ ↔ typ τ) ∧
    ∑ τ, ∑ s : Fin (rk τ), m' τ s * (s.val + 1) = degOf Dw m ∧
    minorProd Dw K typ m n₁ (fun i => Fin.castAdd n₂ i) * minorProd Dw K (fun τ => ¬ typ τ) m n₂ (fun i => Fin.natAdd n₁ i) =
      MvPolynomial.rename (fun p : (Σ τ : E →+* ℂ, Fin (rk τ)) × Fin (n₁ + n₂) =>
        (⟨p.1.1, (Fin.castLE (hrk p.1.1) p.1.2, p.2)⟩ : LtN Dw (n₁ + n₂))) (FamGerm.minorsP K col m')
def BoxTupSt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ → ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ))
    (g g' : ℕ) (π : 𝓞 E), 1 ≤ g → 1 ≤ g' → π * star π = (g : 𝓞 E) →
  ∀ τ : Frames P.U.LG.L (κ := Fin 1 × Fin (chD C.ch)) C.xT, τ.Gen → IsEL P C.xT C.actT C.eT C.wPT τ →
  ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G']
    (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n)
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
  ∀ (s : Fin n → Fam P.D.toPre F g') (s₂ t₀ t : Fin n → Fam P.D.toPre F (g' * g)) (p : Fin n → QkPt P.D.toPre F (g' * g))
    (w : ∀ i, LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F (p i).g.b) (DegPre.lineε (g' * g)))) (ζ : Fin n → F)
    (x : Fin n → (TFK (R := T.V) F ⟶ P.A.A)) (σ : Fin n → P.U.toUnifPre.SecGF F (g' * g)) (f : Fin n → PS F 1 (chD C.ch)),
    (∀ i, NuGe P.D Q F v g' (s i) 0 ∧ PullAl P.D F P.oD (star π) g' g (s i) (s₂ i) ∧
      (w i).IsGen ∧ ζ i ≠ 0 ∧ FinOrd P.D F (g' * g) (p i) (w i) (ζ i) ∧ P.ToA F (g' * g) (p i) (x i) ∧ x i ≫ P.oA.act π = 1 ∧
      PhiRel P.D.toPre F (g' * g) (p i) (w i) (s₂ i) (t₀ i) ∧ Fam.IsSmul P.D.toPre F (ζ i) (t₀ i) (t i) ∧
      P.U.toUnifPre.ExpandsG F (g' * g) (σ i) (t i) ∧
      GermA P.U.toUnifPre (κ := Fin 1 × Fin (chD C.ch)) C.xT τ F (g' * g) (σ i) (f i)) →
  ∃ (S : Fam D'.toPre F g') (S₂ : Fam D'.toPre F (g' * g)) (p' : QkPt D'.toPre F (g' * g))
    (w' : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p'.g.b) (DegPre.lineε (g' * g)))) (ζ' : F) (x' : TFK (R := T.V) F ⟶ A'.A)
    (T₀ T₁ : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g)),
    BoxTup C P Q F v g g' π pG PU oD' S S₂ p' w' ζ' x' T₀ T₁ σ' (boxSer f) ∧ ∀ i, x' ≫ pA.pr i = x i
def RPointT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a) (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z)))
    (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G']
    (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n)
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) → 1 ≤ n →
  ∀ (α : 𝓞 E) (N Dg : ℕ), α * star α = (N : 𝓞 E) → (∃ u u' : 𝓞 E, u * α + u' * star α = 1) → IsUnit ((N : ℕ) : T.V) →
    4 * Dg + 4 ≤ N → (Dg : ℝ) * M0 < N →
  ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * N)), NuGe D' (sumQ pD.xe Q) F v 1 θ 0 → ThFrame D' ϖ F θ →
    PullAl D' F oD' α 1 N θ θα →
  ∀ (I : Type) [Fintype I] (Pi : I → MvPolynomial (LtN Dw n) F) (a : I → F), (∀ i, 0 ≤ v (a i)) →
    (∑ i, a i • Pi i).totalDegree ≤ Dg → ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f → ∀ gm : ℚ,
    letI := io.toAlgebra
    v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) (MvPowerSeries.map (algebraMap T.Fr F) f) (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (∑ i, a i • Pi i)) = (gm : WithTop ℚ) →
    ∃ (i : I) (p : QkPt D'.toPre F (1 * N)) (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (1 * N)))) (ζ : F)
      (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (1 * N)) (σ' : U'.toUnifPre.SecGF F (1 * N)) (h : PS F n (chD C.ch)) (ρ : ℚ),
      w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (1 * N) p w ζ ∧ QkToAkU U'.toUnifPre F (1 * N) p x ∧
      (∀ k, x ≫ pA.pr k ≫ P.oA.act (star α) = 1) ∧ PhiRel D'.toPre F (1 * N) p w θα t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
      U'.toUnifPre.ExpandsG F (1 * N) σ' t ∧ IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (1 * N) σ' h ∧
      v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (1 * N) h (fun ℓ : LtN Dw n => ℓ.2.2)
        (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) (Pi i)) = (ρ : WithTop ℚ) ∧
      (ρ : ℝ) ≤ gm + (Dg : ℝ) ^ 2 * Φ / N
def GenPointT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l),
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → y.IsAlg → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) → ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a) (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z)))
    (n : ℕ) (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr))) (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G']
    (pD : IsPowDeg D'.toPre P.D.toPre n) (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n)
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
  ∀ s s₂ p w ζ x t₀ t σ' h, BoxTup C P Q F v g g' π pG PU oD' s s₂ p w ζ x t₀ t σ' h →
  ∃ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * (g' * g))) (k : ℕ) (a : Fin k → F) (hh : Fin k → PS F n (chD C.ch)),
    NuGe D' (sumQ pD.xe Q) F v 1 θ 0 ∧ ThFrame D' ϖ F θ ∧ PullAl D' F oD' (star π * star π') 1 (g' * g) θ θα ∧
    (∀ i, 0 ≤ v (a i)) ∧ h = ∑ i, a i • hh i ∧
    ∀ i, ∃ (p₂ : QkPt D'.toPre F (1 * (g' * g))) (w₂ : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g)))))
      (ζ₂ : F) (x₂ : TFK (R := T.V) F ⟶ A'.A) (r₀ r₂ : Fam D'.toPre F (1 * (g' * g))) (σ₂ : U'.toUnifPre.SecGF F (g' * g)),
      QkToAkU U'.toUnifPre F (1 * (g' * g)) p₂ x₂ ∧ (∀ b, x₂ ≫ pA.pr b ≫ P.oA.act (star (star π * star π')) = 1) ∧
      w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd D' F (1 * (g' * g)) p₂ w₂ ζ₂ ∧
      PhiRel D'.toPre F (1 * (g' * g)) p₂ w₂ θα r₀ ∧ Fam.IsSmul D'.toPre F ζ₂ r₀ r₂ ∧
      U'.toUnifPre.ExpandsG F (g' * g) σ₂ (famCast (Dp := D'.toPre) (F := F) (one_mul (g' * g)) r₂) ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ₂ (hh i)
def GermOfFamT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (n : ℕ), 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ q : ℕ, 1 ≤ q →
    (∀ σ' : U'.toUnifPre.SecGF F q, ∃ g : PS F n (chD C.ch),
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' g) ∧
    ∀ (s : Fam D'.toPre F q) (σ' : U'.toUnifPre.SecGF F q), U'.toUnifPre.ExpandsG F q σ' s →
      NuGe D' (sumQ pD.xe Q) F v q s 0 → ∀ g : PS F n (chD C.ch),
        IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' g →
        ∀ e, 0 ≤ v (MvPowerSeries.coeff e g)
def JetsOnCopiesCompatibleFrames : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G) (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n : ℕ), 1 ≤ n → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n) (U' : Unif (maximalIdeal T.V) D' A' G')
    (PU : UnifPowOf3 pD pA pG U' P.U)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (q D : ℕ), 4 * D + 4 ≤ q → (D : ℝ) * M0 < q →
  ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f →
    ∃ (s : Fam D'.toPre F q) (σ' : U'.toUnifPre.SecGF F q) (g : PS F n (chD C.ch)) (lam : F),
      NuGe D' (sumQ pD.xe Q) F v q s 0 ∧ U'.toUnifPre.ExpandsG F q σ' s ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F q σ' g ∧
      lam ≠ 0 ∧ (∃ ρ : ℚ, v lam = (ρ : WithTop ℚ) ∧ (ρ : ℝ) ≤ (D : ℝ) ^ 2 * Φ / q) ∧
      ∀ e : Fin n × Fin (chD C.ch) →₀ ℕ, e.degree ≤ D →
        MvPowerSeries.coeff e g = MvPowerSeries.coeff e (lam • MvPowerSeries.map (algebraMap T.Fr F) f)
def OneColumnT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' → 5 ≤ g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
        (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))),
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (D₁ : DegData T.V (maximalIdeal T.V)) (A₁ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₁ : Over (Sp T.V)) [GrpObj G₁] [IsCommMonObj G₁] (pD : IsPowDeg D₁.toPre P.D.toPre 1)
    (pA : IsPowPolAV A₁ P.A 1) (pG : IsPowGrp G₁ C.I.G.G 1)
    (U₁ : Unif (maximalIdeal T.V) D₁ A₁ G₁) (PU : UnifPowOf3 pD pA pG U₁ P.U)
    [Module (𝓞 E) D₁.toPre.X] (oD₁ : D₁.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₁.toPre.X) (i : Fin 1), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin 1),
      oD₁.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∀ x : TFK (R := T.V) F ⟶ A₁.A, (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) →
    letI := io.toAlgebra
    ∃ (s : Fam D₁.toPre F g') (s₂ : Fam D₁.toPre F (g' * g)) (p : QkPt D₁.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D₁.toPre.P.L (DegPre.lineφ D₁.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (t₀ t : Fam D₁.toPre F (g' * g))
      (σ' : U₁.toUnifPre.SecGF F (g' * g)) (h : PS F 1 (chD C.ch)) (c₀ : F) (ρ₀ : ℚ),
      NuGe D₁ (sumQ pD.xe Q) F v g' s 0 ∧
      PullAl D₁ F oD₁ (star π) g' g s s₂ ∧
      (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D₁ F (g' * g) p w ζ) ∧
      QkToAkU U₁.toUnifPre F (g' * g) p x ∧
      PhiRel D₁.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D₁.toPre F ζ t₀ t ∧
      U₁.toUnifPre.ExpandsG F (g' * g) σ' t ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h ∧
      v c₀ = (ρ₀ : WithTop ℚ) ∧ (ρ₀ : ℝ) ≤ r * Φ / (4 * g') ∧
      (∀ e, v c₀ ≤ v (MvPowerSeries.coeff e h)) ∧ v (MvPowerSeries.constantCoeff h) = v c₀
def ColumnValueT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' → 5 ≤ g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (O : Type) [CommRing O] [Algebra O F] [Algebra T.V O] [IsScalarTower T.V O F],
    Function.Injective (algebraMap O F) → (∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) →
    IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O →
    ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
        (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))),
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (D₁ : DegData T.V (maximalIdeal T.V)) (A₁ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₁ : Over (Sp T.V)) [GrpObj G₁] [IsCommMonObj G₁] (pD : IsPowDeg D₁.toPre P.D.toPre 1)
    (pA : IsPowPolAV A₁ P.A 1) (pG : IsPowGrp G₁ C.I.G.G 1)
    (U₁ : Unif (maximalIdeal T.V) D₁ A₁ G₁) (PU : UnifPowOf3 pD pA pG U₁ P.U)
    [Module (𝓞 E) D₁.toPre.X] (oD₁ : D₁.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₁.toPre.X) (i : Fin 1), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin 1),
      oD₁.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∀ (u : PS F 1 (chD C.ch)), (∀ e, 0 ≤ v (MvPowerSeries.coeff e u)) → MvPowerSeries.constantCoeff u = 1 →
    ev (n := 2) ![fun j => MvPowerSeries.map (algebraMap T.V F) (C.FT j)] u =
      ev (n := 2) ![pt F (chD C.ch) 0] u * ev (n := 2) ![pt F (chD C.ch) 1] u →
    letI := io.toAlgebra
    ∃ (x : TFK (R := T.V) F ⟶ A₁.A) (s : Fam D₁.toPre F g') (s₂ : Fam D₁.toPre F (g' * g))
      (p : QkPt D₁.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D₁.toPre.P.L (DegPre.lineφ D₁.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (t₀ t : Fam D₁.toPre F (g' * g))
      (σ' : U₁.toUnifPre.SecGF F (g' * g)) (h : PS F 1 (chD C.ch)) (c₀ : F) (ρ₀ : ℚ),
      (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) ∧
      NuGe D₁ (sumQ pD.xe Q) F v g' s 0 ∧
      PullAl D₁ F oD₁ (star π) g' g s s₂ ∧
      (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D₁ F (g' * g) p w ζ) ∧
      QkToAkU U₁.toUnifPre F (g' * g) p x ∧
      PhiRel D₁.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D₁.toPre F ζ t₀ t ∧
      U₁.toUnifPre.ExpandsG F (g' * g) σ' t ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h ∧
      v c₀ = (ρ₀ : WithTop ℚ) ∧ (ρ₀ : ℝ) ≤ r * Φ / (4 * g') ∧
      (∀ e, v c₀ ≤ v (MvPowerSeries.coeff e h)) ∧ v (MvPowerSeries.constantCoeff h) = v c₀ ∧
      ∀ Pv : MvPolynomial (LtN Dw 1) F, (∀ mm, 0 ≤ v (Pv.coeff mm)) →
        (∀ ℓ ∈ Pv.vars, 0 < v (algebraMap T.Fr F (io (embK c ℓ.1 (star π))))) → Pv.totalDegree < g →
        v c₀ + v ((g : ℕ) : F) ≤
          v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h
              (fun ℓ : LtN Dw 1 => ℓ.2.2) (fun (ℓ : LtN Dw 1) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i)) Pv -
            MvPolynomial.eval (fun ℓ : LtN Dw 1 => MvPowerSeries.constantCoeff
                (DofN (fun j => MvPowerSeries.map (algebraMap T.V F) (C.FT j)) (0 : Fin 1)
                  (fun j => algebraMap T.V F (C.uvecT ⟨ℓ.1, ℓ.2.1⟩ j)) u)) Pv *
              MvPowerSeries.constantCoeff h)
def UnitTypeBlockCondition : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n₂ : ℕ) (D₂ : DegData T.V (maximalIdeal T.V)) (A₂ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₂ : Over (Sp T.V)) [GrpObj G₂] [IsCommMonObj G₂] (pD : IsPowDeg D₂.toPre P.D.toPre n₂)
    (pA : IsPowPolAV A₂ P.A n₂) (pG : IsPowGrp G₂ C.I.G.G n₂)
    (U₂ : Unif (maximalIdeal T.V) D₂ A₂ G₂) (PU : UnifPowOf3 pD pA pG U₂ P.U)
    [Module (𝓞 E) D₂.toPre.X] (oD₂ : D₂.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₂.toPre.X) (i : Fin n₂), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n₂),
      oD₂.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∀ (m : (E →+* ℂ) → ℕ → ℕ) (D : ℕ),
    (∀ τ s, m τ s ≠ 0 → ¬ 0 < v (algebraMap T.Fr F (io (embK c τ (star π)))) →
      1 ≤ s ∧ s ≤ Dw.mult τ ∧ s ≤ n₂) →
    degOf Dw m ≤ D → degOf Dw m < g → 4 * D + 4 ≤ g' → (D : ℝ) * M0 < g' →
    letI := io.toAlgebra
    ∃ (s : Fam D₂.toPre F g') (s₂ : Fam D₂.toPre F (g' * g)) (p : QkPt D₂.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D₂.toPre.P.L (DegPre.lineφ D₂.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (x : TFK (R := T.V) F ⟶ A₂.A) (t₀ t : Fam D₂.toPre F (g' * g))
      (σ' : U₂.toUnifPre.SecGF F (g' * g)) (h : PS F n₂ (chD C.ch)) (ρ₂ : ℚ),
      BoxTup C P Q F v g g' π pG PU oD₂ s s₂ p w ζ x t₀ t σ' h ∧
      v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h
          (fun ℓ : LtN Dw n₂ => ℓ.2.2) (fun (ℓ : LtN Dw n₂) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
          (minorProd Dw F (fun τ => ¬ 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₂ id)) =
        (ρ₂ : WithTop ℚ) ∧
      (ρ₂ : ℝ) ≤ (D : ℝ) ^ 2 * Φ / g'
def LemmaBT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg → ∀ (C : IntegralChartA3 Xo c T io y),
    FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT → ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E →
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
  ∀ (O : Type) [CommRing O] [Algebra O F] [Algebra T.V O] [IsScalarTower T.V O F],
    Function.Injective (algebraMap O F) → (∀ z : F, 0 ≤ v z ↔ z ∈ (algebraMap O F).range) →
    IsAdicComplete (Ideal.span {((g : ℕ) : O)}) O →
    ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
        (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))),
  ∀ (Φ M0 : ℝ) (r : ℕ) (b : Module.Basis (Fin r) ℤ P.D.toPre.X), 0 ≤ Φ → (∀ j, (Q (b j) : ℝ) ≤ Φ) →
    (∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) →
  ∀ (n₁ n₂ : ℕ), 1 ≤ n₁ + n₂ → ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre (n₁ + n₂))
    (pA : IsPowPolAV A' P.A (n₁ + n₂)) (pG : IsPowGrp G' C.I.G.G (n₁ + n₂))
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin (n₁ + n₂)), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin (n₁ + n₂)),
      oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∀ (m : (E →+* ℂ) → ℕ → ℕ),
    (∀ τ s, m τ s ≠ 0 → 1 ≤ s ∧ s ≤ Dw.mult τ ∧
      s ≤ (if 0 < v (algebraMap T.Fr F (io (embK c τ (star π)))) then n₁ else n₂)) →
    degOf Dw m < g - 1 → 4 * degOf Dw m + 4 ≤ g' → (degOf Dw m : ℝ) * M0 < g' →
  ∀ (ρg : ℚ), v ((g : ℕ) : F) = (ρg : WithTop ℚ) →
    letI := io.toAlgebra
    ∃ (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
      (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F (n₁ + n₂) (chD C.ch)) (ρ : ℚ),
      NuGe D' (sumQ pD.xe Q) F v g' s 0 ∧
      PullAl D' F oD' (star π) g' g s s₂ ∧
      (w.IsGen ∧ ζ ≠ 0 ∧ FinOrd D' F (g' * g) p w ζ) ∧
      QkToAkU U'.toUnifPre F (g' * g) p x ∧ (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) ∧
      PhiRel D'.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
      U'.toUnifPre.ExpandsG F (g' * g) σ' t ∧
      IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h ∧
      v (nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h
          (fun ℓ : LtN Dw (n₁ + n₂) => ℓ.2.2) (fun (ℓ : LtN Dw (n₁ + n₂)) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
          (minorProd Dw F (fun τ => 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₁
              (fun i => Fin.castAdd n₂ i) *
            minorProd Dw F (fun τ => ¬ 0 < v (algebraMap T.Fr F (io (embK c τ (star π))))) m n₂
              (fun i => Fin.natAdd n₁ i))) = (ρ : WithTop ℚ) ∧
      (ρ : ℝ) ≤ (ρg : ℝ) * degOf Dw m / (g - 1) + n₁ * r * Φ / (4 * g') + 2 * degOf Dw m ^ 2 * Φ / g'
def BoxAssemblyT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y)
    (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso → ∀ (ϖ : T.V), Irreducible ϖ →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q → ∀
    (F : Type) [Field F] [IsAlgClosed F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ (g g' : ℕ) (π : 𝓞 E), 1 ≤ g → 1 ≤ g' → π * star π = (g : 𝓞 E) →
  ∀ (n₁ n₂ : ℕ)
    (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre (n₁ + n₂))
    (pA : IsPowPolAV A' P.A (n₁ + n₂)) (pG : IsPowGrp G' C.I.G.G (n₁ + n₂))
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin (n₁ + n₂)), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin (n₁ + n₂)),
      oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) →
  ∃ (D₁ : DegData T.V (maximalIdeal T.V)) (A₁ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₁ : Over (Sp T.V)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (pD₁ : IsPowDeg D₁.toPre P.D.toPre 1)
    (pA₁ : IsPowPolAV A₁ P.A 1) (pG₁ : IsPowGrp G₁ C.I.G.G 1)
    (U₁ : Unif (maximalIdeal T.V) D₁ A₁ G₁) (PU₁ : UnifPowOf3 pD₁ pA₁ pG₁ U₁ P.U)
    (_ : Module (𝓞 E) D₁.toPre.X) (oD₁ : D₁.toPre.OAct (𝓞 E))
    (D₂ : DegData T.V (maximalIdeal T.V)) (A₂ : PolAV (Spec (CommRingCat.of T.Fr)))
    (G₂ : Over (Sp T.V)) (_ : GrpObj G₂) (_ : IsCommMonObj G₂) (pD₂ : IsPowDeg D₂.toPre P.D.toPre n₂)
    (pA₂ : IsPowPolAV A₂ P.A n₂) (pG₂ : IsPowGrp G₂ C.I.G.G n₂)
    (U₂ : Unif (maximalIdeal T.V) D₂ A₂ G₂) (PU₂ : UnifPowOf3 pD₂ pA₂ pG₂ U₂ P.U)
    (_ : Module (𝓞 E) D₂.toPre.X) (oD₂ : D₂.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D₁.toPre.X) (i : Fin 1), pD₁.xe (a • x) i = a • pD₁.xe x i) ∧
    (∀ (a : 𝓞 E) (i : Fin 1),
      oD₁.onB.act a ≫ pD₁.pw.pr i = pD₁.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) ∧
    (∀ (a : 𝓞 E) (x : D₂.toPre.X) (i : Fin n₂), pD₂.xe (a • x) i = a • pD₂.xe x i) ∧
    (∀ (a : 𝓞 E) (i : Fin n₂),
      oD₂.onB.act a ≫ pD₂.pw.pr i = pD₂.pw.pr i ≫ (letI := H.starRing; P.oD.onB.act a)) ∧
    ∀ (s₁ : Fin n₁ → Fam D₁.toPre F g') (s₂₁ : Fin n₁ → Fam D₁.toPre F (g' * g))
      (p₁ : Fin n₁ → QkPt D₁.toPre F (g' * g))
      (w₁ : ∀ i, LB.Gen (LB.LinComb D₁.toPre.P.L (DegPre.lineφ D₁.toPre F (p₁ i).g.b) (DegPre.lineε (g' * g))))
      (ζ₁ : Fin n₁ → F) (x₁ : Fin n₁ → (TFK (R := T.V) F ⟶ A₁.A)) (t₀₁ t₁ : Fin n₁ → Fam D₁.toPre F (g' * g))
      (σ₁ : Fin n₁ → U₁.toUnifPre.SecGF F (g' * g)) (h₁ : Fin n₁ → PS F 1 (chD C.ch)),
      (∀ i, BoxTup C P Q F v g g' π pG₁ PU₁ oD₁ (s₁ i) (s₂₁ i) (p₁ i) (w₁ i) (ζ₁ i) (x₁ i) (t₀₁ i) (t₁ i)
        (σ₁ i) (h₁ i)) →
    ∀ (sb : Fam D₂.toPre F g') (s₂b : Fam D₂.toPre F (g' * g)) (pb : QkPt D₂.toPre F (g' * g))
      (wb : LB.Gen (LB.LinComb D₂.toPre.P.L (DegPre.lineφ D₂.toPre F pb.g.b) (DegPre.lineε (g' * g))))
      (ζb : F) (xb : TFK (R := T.V) F ⟶ A₂.A) (t₀b tb : Fam D₂.toPre F (g' * g))
      (σb : U₂.toUnifPre.SecGF F (g' * g)) (hb : PS F n₂ (chD C.ch)),
      BoxTup C P Q F v g g' π pG₂ PU₂ oD₂ sb s₂b pb wb ζb xb t₀b tb σb hb →
    ∃ (s : Fam D'.toPre F g') (s₂ : Fam D'.toPre F (g' * g)) (p : QkPt D'.toPre F (g' * g))
      (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
      (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A) (t₀ t : Fam D'.toPre F (g' * g))
      (σ' : U'.toUnifPre.SecGF F (g' * g)) (h : PS F (n₁ + n₂) (chD C.ch)),
      BoxTup C P Q F v g g' π pG PU oD' s s₂ p w ζ x t₀ t σ' h ∧
      h = (∏ i : Fin n₁, MvPowerSeries.rename
            (fun q : Fin 1 × Fin (chD C.ch) => ((Fin.castAdd n₂ i, q.2) : Fin (n₁ + n₂) × Fin (chD C.ch))) (h₁ i)) *
          MvPowerSeries.rename
            (fun q : Fin n₂ × Fin (chD C.ch) => ((Fin.natAdd n₁ q.1, q.2) : Fin (n₁ + n₂) × Fin (chD C.ch))) hb ∧
      (∀ i : Fin n₁, x ≫ pA.pr (Fin.castAdd n₂ i) = x₁ i ≫ pA₁.pr 0) ∧
      ∀ i : Fin n₂, x ≫ pA.pr (Fin.natAdd n₁ i) = xb ≫ pA₂.pr i
def PowPELF : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (n : ℕ),
    letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg →
  ∀ (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)) (ϖ : T.V), Irreducible ϖ → ValOver ϖ F v →
  ∀ (_I : TateIso Dw F (TFK (R := T.V) F ⟶ P.A.A) (fun a x => x ≫ P.oA.act a)
        (fun k x x' z => WeilIs P.A.A P.A.L k x x' (unitOn z))),
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n)
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
  ∃ (oA' : A'.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (i : Fin n), oA'.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a) ∧
    IsQ D'.toPre ϖ (sumQ pD.xe Q) ∧
    (∃ Dw' : Datum H, Nonempty (TateIso Dw' F (TFK (R := T.V) F ⟶ A'.A) (fun a x => x ≫ oA'.act a)
        (fun k x x' z => WeilIs A'.A A'.L k x x' (unitOn z)))) ∧
    ∃ (t' : SAB H (Sp T.V)) (P' : PELUnif (maximalIdeal T.V) t'),
      P'.TorsionIso ∧ t'.G = G' ∧ HEq t'.grp (inferInstance : GrpObj G') ∧
      HEq t'.comm (inferInstance : IsCommMonObj G') ∧ P'.D = D' ∧
      HEq P'.mod (inferInstance : Module (𝓞 E) D'.toPre.X) ∧ HEq P'.oD oD' ∧ P'.A = A' ∧
      HEq P'.oA oA' ∧ HEq P'.U U'
def ThetaFrameF : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (n : ℕ),
    letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg →
  ∀ (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)) (ϖ : T.V), Irreducible ϖ → ValOver ϖ F v →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n)
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
  ∃ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * g')),
    NuGe D' (sumQ pD.xe Q) F v 1 θ 0 ∧ ThFrame D' ϖ F θ ∧ PullAl D' F oD' (star π') 1 g' θ θα
def DescentIdF : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (n : ℕ),
    letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg →
  ∀ (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)) (ϖ : T.V), Irreducible ϖ → ValOver ϖ F v →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n)
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
  ∀ (oA' : A'.OAct (𝓞 E)), (∀ (a : 𝓞 E) (i : Fin n), oA'.act a ≫ pA.pr i = pA.pr i ≫ P.oA.act a) →
  ∀ (θ : Fam D'.toPre F 1) (θα : Fam D'.toPre F (1 * g')), PullAl D' F oD' (star π') 1 g' θ θα →
  ∀ (pb : QkPt D'.toPre F (1 * g'))
    (wb : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F pb.g.b) (DegPre.lineε (1 * g'))))
    (ζb : F) (xb : TFK (R := T.V) F ⟶ A'.A) (tb₀ tb : Fam D'.toPre F (1 * g')),
    QkToAkU U'.toUnifPre F (1 * g') pb xb → xb ≫ oA'.act (star (star π')) = 1 →
    wb.IsGen → ζb ≠ 0 → FinOrd D' F (1 * g') pb wb ζb →
    PhiRel D'.toPre F (1 * g') pb wb θα tb₀ → Fam.IsSmul D'.toPre F ζb tb₀ tb →
  ∀ (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
    (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A),
    w.IsGen → ζ ≠ 0 → FinOrd D' F (g' * g) p w ζ →
    QkToAkU U'.toUnifPre F (g' * g) p x → (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) →
  ∀ (s₂ t₀ r : Fam D'.toPre F (g' * g)),
    PullAl D' F oD' (star π) g' g (famCast (Dp := D'.toPre) (F := F) (one_mul g') tb) s₂ → PhiRel D'.toPre F (g' * g) p w s₂ t₀ →
    Fam.IsSmul D'.toPre F ζ t₀ r →
    ∃ (θα₂ : Fam D'.toPre F (1 * (g' * g))) (p₂ : QkPt D'.toPre F (1 * (g' * g)))
      (w₂ : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p₂.g.b) (DegPre.lineε (1 * (g' * g)))))
      (ζ₂ : F) (x₂ : TFK (R := T.V) F ⟶ A'.A) (r₀ r₂ : Fam D'.toPre F (1 * (g' * g))),
      PullAl D' F oD' (star π * star π') 1 (g' * g) θ θα₂ ∧
      QkToAkU U'.toUnifPre F (1 * (g' * g)) p₂ x₂ ∧ x₂ ≫ oA'.act (star (star π * star π')) = 1 ∧
      w₂.IsGen ∧ ζ₂ ≠ 0 ∧ FinOrd D' F (1 * (g' * g)) p₂ w₂ ζ₂ ∧
      PhiRel D'.toPre F (1 * (g' * g)) p₂ w₂ θα₂ r₀ ∧ Fam.IsSmul D'.toPre F ζ₂ r₀ r₂ ∧
      r = famCast (Dp := D'.toPre) (F := F) (one_mul (g' * g)) r₂
def GPairF : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (n : ℕ),
    letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), y.IsAlg →
  ∀ (C : IntegralChartA3 Xo c T io y), FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT →
  ∀ (P : PELUnif (maximalIdeal T.V) C.I.G), P.TorsionIso →
  ∀ (g g' : ℕ), g.Prime → g'.Prime → g ≠ g' → Odd g → Odd g' →
  ∀ (π π' : 𝓞 E), π * star π = (g : 𝓞 E) → π' * star π' = (g' : 𝓞 E) →
    (∃ u u' : 𝓞 E, u * π + u' * star π = 1) → (∃ u u' : 𝓞 E, u * π' + u' * star π' = 1) →
    ¬ IsUnit ((g : ℕ) : T.V) →
  ∀ (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra T.Fr F] [Algebra T.V F] [IsScalarTower T.V T.Fr F]
    (v : AddValuation F (WithTop ℚ)) (ϖ : T.V), Irreducible ϖ → ValOver ϖ F v →
  ∀ (Q : P.D.toPre.X → ℤ), IsQ P.D.toPre ϖ Q →
  ∀ (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Spec (CommRingCat.of T.Fr)))
    (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre P.D.toPre n)
    (pA : IsPowPolAV A' P.A n) (pG : IsPowGrp G' C.I.G.G n)
    (U' : Unif (maximalIdeal T.V) D' A' G') (PU : UnifPowOf3 pD pA pG U' P.U)
    [Module (𝓞 E) D'.toPre.X] (oD' : D'.toPre.OAct (𝓞 E)),
    (∀ (a : 𝓞 E) (x : D'.toPre.X) (i : Fin n), pD.xe (a • x) i = a • pD.xe x i) →
    (∀ (a : 𝓞 E) (i : Fin n), oD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ P.oD.onB.act a) →
  ∀ (p : QkPt D'.toPre F (g' * g))
    (w : LB.Gen (LB.LinComb D'.toPre.P.L (DegPre.lineφ D'.toPre F p.g.b) (DegPre.lineε (g' * g))))
    (ζ : F) (x : TFK (R := T.V) F ⟶ A'.A),
    w.IsGen → ζ ≠ 0 → FinOrd D' F (g' * g) p w ζ →
    QkToAkU U'.toUnifPre F (g' * g) p x → (∀ i, x ≫ pA.pr i ≫ P.oA.act π = 1) →
  ∀ Ppol : MvPolynomial (LtN Dw n) F,
    letI := io.toAlgebra
    ∃ ℓ : Fam D'.toPre F g' →ₗ[F] F,
      (∀ (s : Fam D'.toPre F g') (s₂ t₀ t : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g))
          (h : PS F n (chD C.ch)),
        PullAl D' F oD' (star π) g' g s s₂ → PhiRel D'.toPre F (g' * g) p w s₂ t₀ → Fam.IsSmul D'.toPre F ζ t₀ t →
        U'.toUnifPre.ExpandsG F (g' * g) σ' t →
        IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h →
        nabValN C.ch.B F (MvPowerSeries.map (algebraMap T.Fr F) C.ch.h) H.w0 (g' * g) h
          (fun ℓ : LtN Dw n => ℓ.2.2)
          (fun (ℓ : LtN Dw n) i => algebraMap T.Fr F (C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩ i))
          Ppol = ℓ s) ∧
      ∀ s : Fam D'.toPre F g', ∃ (s₂ t₀ t : Fam D'.toPre F (g' * g)) (σ' : U'.toUnifPre.SecGF F (g' * g))
          (h : PS F n (chD C.ch)),
        PullAl D' F oD' (star π) g' g s s₂ ∧ PhiRel D'.toPre F (g' * g) p w s₂ t₀ ∧ Fam.IsSmul D'.toPre F ζ t₀ t ∧
        U'.toUnifPre.ExpandsG F (g' * g) σ' t ∧
        IsGermN P C.xT C.actT C.eT C.wPT pG PU.toUnifPowOf F (g' * g) σ' h
end GlobalTheory.PowGerm


