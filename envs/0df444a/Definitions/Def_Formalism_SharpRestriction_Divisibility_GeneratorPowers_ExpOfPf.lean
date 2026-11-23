-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:27.833815+00:00
-- url     : https://prove2.me/theorems/0f728e8a-bc47-427a-ae5d-2aeaf5b860f1
-- title:
--   Exp Of Pf
-- statement:
--   Definitions and structural lemmas for Exp Of Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpOfPf.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace ExpOf
variable {R : Type} [CommRing R]
end ExpOf
def LinEigSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    (y : FrPt Xo c S) (C : ChartAt Xo c y) (a : 𝓞 E) (ℓ : Lt1 Dw) (i : Fin C.d),
    ∑ j, dLin (C.B.A.act a) i j * C.uvec ℓ j = algebraMap c.F S (embK c ℓ.1 a) * C.uvec ℓ i
namespace ExpOf
variable {S : Type} [CommRing S]
def linPt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d n : ℕ}
    (uvec : Lt1 Dw → Fin d → S) (b : Fin n) (i : Fin d) : MvPowerSeries (Fin n × Fin (dL Dw)) S :=
  ∑ ℓ : Lt1 Dw, MvPowerSeries.C (uvec ℓ i) * MvPowerSeries.X (b, ltIdx Dw ℓ)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}
def expPhi (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (j : Fin d) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S :=
  subst (fun p : Fin 1 × Fin d => linPt uvec (0 : Fin 1) p.2) (ε j)
end ExpOf
namespace ExpOf
variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}
end ExpOf
namespace ExpOf
variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}
end ExpOf
namespace ExpOf
variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}
end ExpOf
end Formalism.MainNotions.ModuliIntegralCharts.H1


