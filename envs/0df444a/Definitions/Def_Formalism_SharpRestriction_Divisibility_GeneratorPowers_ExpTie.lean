-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:31.667047+00:00
-- url     : https://prove2.me/theorems/8d86c16d-6cd0-431d-ba36-56fad2940561
-- title:
--   Exp Tie
-- statement:
--   Definitions and structural lemmas for Exp Tie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTie.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
section Defs
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
variable {S : Type} [CommRing S]
def compL {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (g : MvPowerSeries (Fin 1 × Fin d) S) :
    MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  MvPowerSeries.subst (fun p : Fin 1 × Fin d => φ p.2) g
def atPt {n : ℕ} (b : Fin n) (g : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) :
    MvPowerSeries (Fin n × Fin (dL Dw)) S :=
  MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) => (MvPowerSeries.X (b, q.2) : MvPowerSeries (Fin n × Fin (dL Dw)) S)) g
structure IsExpOf {d : ℕ} (F : Fin d → MvPowerSeries (Fin 2 × Fin d) S) (uvec : Lt1 Dw → Fin d → S)
    (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) : Prop where
  const : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0
  lin : ∀ ℓ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1) (φ j) = uvec ℓ j
  hom : ∀ j, MvPowerSeries.subst (fun p : Fin 2 × Fin d => atPt p.1 (φ p.2)) (F j) =
    MvPowerSeries.subst (fun q : Fin 1 × Fin (dL Dw) =>
      (MvPowerSeries.X ((0 : Fin 2), q.2) + MvPowerSeries.X ((1 : Fin 2), q.2) :
        MvPowerSeries (Fin 2 × Fin (dL Dw)) S)) (φ j)
variable [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)]
def jφ {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin (dL Dw)) m :=
  jetSubstPS (fun p : Fin 1 × Fin d => φ p.2)
def xExp (y : FrPt Xo c S) (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    jO y (dL Dw) m 1 ⟶ Xo.univ.t.G :=
  homAt y.x (jφ φ m) ≫ C.x m
def FrTruncC (y : FrPt Xo c S) (C : ChartAt Xo c y) : Prop :=
  ∀ m, LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
    (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
      (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
    (C.e m)
def IsExpGaugeOf (y : FrPt Xo c S) (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (e : ∀ m, ExpFr y (xExp y C φ) m) : Prop :=
  ∀ m, ∃ u : (Jet S (Fin 1 × Fin (dL Dw)) m)ˣ,
    (u : Jet S (Fin 1 × Fin (dL Dw)) m) = psJet m (Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0)))) ∧
    LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e m)
      (scaleGen _ _ (unitΓ u) (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act C.e C.wP m)
        (homAt y.x (jφ φ m)).left))
end Defs
def ExpOfChartSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y), FrTruncC y C →
    ∃ φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S, IsExpOf C.B.G.F C.uvec φ ∧
      IsExpChart y (xExp y C φ) ∧
      ∃ e : ∀ m, ExpFr y (xExp y C φ) m, IsExpGauge y (xExp y C φ) e ∧ IsExpGaugeOf y C φ e
def ExpChartOfSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
    (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y),
    ∃ φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S, IsExpOf C.B.G.F C.uvec φ ∧ IsExpChart y (xExp y C φ)
def ExpGaugeOfSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y), FrTruncC y C →
    ∀ (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ → IsExpChart y (xExp y C φ) →
      ∃ e : ∀ m, ExpFr y (xExp y C φ) m, IsExpGauge y (xExp y C φ) e ∧ IsExpGaugeOf y C φ e
def TieSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ →
    ∀ e : ∀ m, ExpFr y (xExp y C φ) m, IsExpGaugeOf y C φ e →
    ∀ (k : ℕ) (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x)))
      (f : MvPowerSeries (Fin 1 × Fin C.d) S), IsGerm y C.d C.x C.B.A.act C.e C.wP k F f →
      ∃ g : MvPowerSeries (Fin 1 × Fin (dL Dw)) S, IsExpGerm y (xExp y C φ) e k F g ∧
        ∀ α : Lt1 Dw →₀ ℕ, C.B.nabVal S C.h H.w0 k f C.uvec (MvPolynomial.monomial α 1) = expVal g α
end Formalism.MainNotions.ModuliIntegralCharts.H1


