-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_UnitIdSt
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_UnitIdSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:44.256923+00:00
-- url     : https://prove2.me/theorems/3c2356d6-2f72-4bd5-99b0-ee71bce4fad6
-- title:
--   Unit Id St
-- statement:
--   Definitions and structural lemmas for Unit Id St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/UnitIdSt.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
section Defs
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {S : Type} [CommRing S]
def actPS (c : Coeff l) [Algebra c.F S] (a : 𝓞 E) : Fin 1 × Fin (dL Dw) → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  fun q => algebraMap c.F S (embK c ((ltIdx Dw).symm q.2).1 a) • MvPowerSeries.X q
def φa (c : Coeff l) [Algebra c.F S] {d : ℕ} (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (a : 𝓞 E) :
    Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  fun j => MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)
def atP {d n : ℕ} (P : Fin n → Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (f : MvPowerSeries (Fin n × Fin d) S) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  MvPowerSeries.subst (fun p : Fin n × Fin d => P p.1 p.2) f
end Defs
def UnitIdSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
      (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S), IsExpOf C.B.G.F C.uvec φ →
      (∀ (a : 𝓞 E) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
        MvPowerSeries.subst (actPS (Dw := Dw) c a) (φ j)) →
      ∀ a : 𝓞 E,
        Germ.FB.expS S (-(compL (φa c φ (1 + a * H.bar a)) (C.B.hL S C.h H.w0))) *
            atP ![φa c φ a, φa c φ H.w0] (C.B.ad (H.bar a)) =
          atP ![φ, φa c φ (a * H.bar a), φa c φ ((1 + a * H.bar a) * H.w0)] C.B.ph1 *
            atP ![φ, φa c φ H.w0, φa c φ (a * H.bar a * H.w0)] C.B.ph2 *
            atP ![φa c φ (a * H.bar a), φa c φ H.w0, φa c φ (a * H.bar a * H.w0)] C.B.ph2 *
            atP ![φ, φa c φ (a * H.w0)] (C.B.ad a) *
            Germ.FB.expS S (-(compL (φa c φ a) (C.B.hL S C.h H.w0))) ^ 2 *
            Germ.FB.expS S (-(compL φ (C.B.hL S C.h H.w0))) *
            Germ.FB.expS S (-(compL (φa c φ (a * H.bar a)) (C.B.hL S C.h H.w0)))
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU


