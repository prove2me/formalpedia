-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartTransportSt
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartTransportSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:18.099496+00:00
-- url     : https://prove2.me/theorems/76d715cc-79fb-4437-87aa-fcdcbebcec39
-- title:
--   Chart Transport St
-- statement:
--   Definitions and structural lemmas for Chart Transport St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartTransportSt.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
def ChartTransportSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (B : Germ.FB T.V d (𝓞 E)) (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G) (eT : ∀ m, FrTyG I.G (𝟙 (Sp T.V)) d xT m) (wPT : PrimTyG I.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d B.G.F B.A.act tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    IsFrameG I.G (𝟙 (Sp T.V)) d xT B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad eT → IsPrimG I.G wPT →
    FrTrunc I.G (𝟙 (Sp T.V)) d xT eT → Rig0G I.G (𝟙 (Sp T.V)) d xT B.A.act eT wPT →
    letI := io.toAlgebra
    ∃ (B' : Germ.FB T.Fr d (𝓞 E)) (uvec : Lt1 Dw → Fin d → T.Fr) (x : ∀ m, jO y.1 d m 1 ⟶ Xo.univ.t.G)
      (e : ∀ m, FrTy y.1 d x m) (wP : PrimTy H Xo) (h : Germ.PS T.Fr 2 d)
      (hch : IsChart y.1 d B'.G.F B'.A.act uvec x)
      (hfr : IsFrame y.1 d x B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e) (hpr : IsPrim wP)
      (hg : B'.IsCanonGauge T.Fr h)
      (hr : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y.1 d x B'.A.act e wP 0)
          (homAt y.1.x (jetAug : Jet T.Fr (Fin 1 × Fin d) 0 →ₐ[T.Fr] T.Fr)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.1.x T.Fr) 1)),
      IsGenFibreChart (⟨d, B', uvec, x, e, wP, h, hch, hfr, hpr, hg, hr⟩ : ChartAt Xo c y.1) I
        B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad uvecT xT eT wPT
def FBMapSt : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (ψ : R →+* R') (d : ℕ) (O : Type) [CommRing O] [StarRing O]
    (B : Germ.FB R d O), ∃ B' : Germ.FB R' d O,
      (∀ j, B'.G.F j = MvPowerSeries.map ψ (B.G.F j)) ∧ (∀ a j, B'.A.act a j = MvPowerSeries.map ψ (B.A.act a j)) ∧
      B'.ph1 = MvPowerSeries.map ψ B.ph1 ∧ B'.ph2 = MvPowerSeries.map ψ B.ph2 ∧ B'.sy = MvPowerSeries.map ψ B.sy ∧
      ∀ a, B'.ad a = MvPowerSeries.map ψ (B.ad a)
def ChartJetTrSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (FT : Fin d → Germ.PS T.V 2 d) (actT : 𝓞 E → Fin d → Germ.PS T.V 1 d)
    (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left)) (uvecT : Lt1 Dw → Fin d → T.V)
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G),
    ((∀ j, IsTanAtG I.G (𝟙 (Sp T.V)) (tgT j)) ∧
      ∀ w, IsTanAtG I.G (𝟙 (Sp T.V)) w → ∃! a : Fin d → T.V, IsCombAtG I.G (𝟙 (Sp T.V)) tgT a w) →
    IsChartG I.G (𝟙 (Sp T.V)) d FT actT tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    (∀ ℓ : Lt1 Dw, IsCombAtG I.G (𝟙 (Sp T.V))
      (fun j : Fin d => (homAt (𝟙 (Sp T.V))
        (jetTan ((0 : Fin 1), j) : Jet T.V (Fin 1 × Fin d) (0 + 1) →ₐ[T.V] DualNumber T.V) ≫ xT 1).left)
      (uvecT ℓ) (I.ub ℓ.1 ℓ.2).left) →
    letI := io.toAlgebra
    ∃ (x : ∀ m, jO y.1 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G),
      IsChart y.1 d (fun j => MvPowerSeries.map (algebraMap T.V T.Fr) (FT j))
        (fun a j => MvPowerSeries.map (algebraMap T.V T.Fr) (actT a j))
        (fun ℓ i => algebraMap T.V T.Fr (uvecT ℓ i)) x ∧
      (∀ m, (x' m).left ≫ I.m2.φ = spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin d) m) ≫ (xT m).left) ∧
      ∀ m, (x' m).left ≫ I.m1.φ = (x m).left
def ChartFrameTrSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (d : ℕ)
    (B : Germ.FB T.V d (𝓞 E)) (B' : Germ.FB T.Fr d (𝓞 E)) (tgT : Fin d → (Sp (DualNumber T.V) ⟶ I.G.G.left))
    (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G) (eT : ∀ m, FrTyG I.G (𝟙 (Sp T.V)) d xT m) (wPT : PrimTyG I.G),
    (∀ j, B'.G.F j = MvPowerSeries.map (algebraMap T.V T.Fr) (B.G.F j)) →
    (∀ a j, B'.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (B.A.act a j)) →
    B'.ph1 = MvPowerSeries.map (algebraMap T.V T.Fr) B.ph1 → B'.ph2 = MvPowerSeries.map (algebraMap T.V T.Fr) B.ph2 →
    B'.sy = MvPowerSeries.map (algebraMap T.V T.Fr) B.sy →
    (∀ a, B'.ad a = MvPowerSeries.map (algebraMap T.V T.Fr) (B.ad a)) →
    IsChartG I.G (𝟙 (Sp T.V)) d B.G.F B.A.act tgT (fun j : Fin d => Pi.single j (1 : T.V)) xT →
    IsFrameG I.G (𝟙 (Sp T.V)) d xT B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad eT → IsPrimG I.G wPT →
    FrTrunc I.G (𝟙 (Sp T.V)) d xT eT → Rig0G I.G (𝟙 (Sp T.V)) d xT B.A.act eT wPT →
    letI := io.toAlgebra
    ∀ (x : ∀ m, jO y.1 d m 1 ⟶ Xo.univ.t.G) (x' : ∀ m, jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G),
      (∀ m, (x' m).left ≫ I.m2.φ = spMap (jetCoef (algebraMap T.V T.Fr) (Fin 1 × Fin d) m) ≫ (xT m).left) →
      (∀ m, (x' m).left ≫ I.m1.φ = (x m).left) →
      ∃ (e : ∀ m, FrTy y.1 d x m) (wP : PrimTy H Xo),
        IsFrame y.1 d x B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e ∧ IsPrim wP ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ (eL y.1 d x B'.A.act e wP 0)
            (homAt y.1.x (jetAug : Jet T.Fr (Fin 1 × Fin d) 0 →ₐ[T.Fr] T.Fr)).left)
          (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.1.x T.Fr) 1) ∧
        (∃ e' : ∀ m, FrTyG I.t' (𝟙 (Sp T.Fr)) d x' m, ∀ m, (e' m).IsGen ∧
          (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L
              (fun J => cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)] J ≫ I.m2.φ) (cε 2)),
            LB.Gen.Corr I.G.PP.L _ _ _ _ c₂
              (LB.pullGen I.G.PP.L _ _ (eT m) (spMap (jetCoef (algebraMap T.V T.Fr) (Fin 2 × Fin d) m))) ∧
            LB.Gen.Maps (LB.linCombIso I.w2 (cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)]) (cε 2)) (e' m)
              (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
          ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L
              (fun J => cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)] J ≫ I.m1.φ) (cε 2)),
            LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (e m) ∧
            LB.Gen.Maps (LB.linCombIso I.w1 (cφG I.t' ![jptG I.t' (𝟙 (Sp T.Fr)) d x' m (0 : Fin 2),
                jptG I.t' (𝟙 (Sp T.Fr)) d x' m (1 : Fin 2)]) (cε 2)) (e' m)
              (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)) ∧
        ∃ wP' : LB.Gen (LB.LinComb I.t'.PP.L (primφ I.t') primε), wP'.IsGen ∧
          (∃ c₂ : LB.Gen (LB.LinComb I.G.PP.L (fun k => primφ I.t' k ≫ I.m2.φ) primε),
            LB.Gen.Corr I.G.PP.L _ _ _ _ c₂ (LB.pullGen I.G.PP.L _ _ wPT I.m2.φ) ∧
            LB.Gen.Maps (LB.linCombIso I.w2 (primφ I.t') primε) wP' (flatGen I.G.PP.L I.m2.φ _ _ c₂)) ∧
          ∃ c₁ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (fun k => primφ I.t' k ≫ I.m1.φ) primε),
            LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ c₁ (LB.pullGen Xo.univ.t.PP.L _ _ wP I.m1.φ) ∧
            LB.Gen.Maps (LB.linCombIso I.w1 (primφ I.t') primε) wP' (flatGen Xo.univ.t.PP.L I.m1.φ _ _ c₁)
omit [StarRing (𝓞 E)] in

def FrTanBasisSt : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
    IsTanAt y.x w →
    ∃! a : Lt1 Dw → S, IsCombAt y.x (m := Fintype.card (Lt1 Dw))
      (fun i => y.u ((Fintype.equivFin (Lt1 Dw)).symm i).1 ((Fintype.equivFin (Lt1 Dw)).symm i).2)
      (fun i => a ((Fintype.equivFin (Lt1 Dw)).symm i)) w
end Formalism.MainNotions.ModuliIntegralCharts.H1


