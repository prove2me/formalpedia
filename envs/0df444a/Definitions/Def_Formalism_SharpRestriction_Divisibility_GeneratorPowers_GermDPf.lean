-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:56.734846+00:00
-- url     : https://prove2.me/theorems/0855c355-9c3f-43e6-8345-8ab420c3e538
-- title:
--   Germ DPf
-- statement:
--   Definitions and structural lemmas for Germ DPf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermDPf.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
namespace GermD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
abbrev ρT (m : ℕ) : jOG x0 d m 1 ⟶ jOG x0 d (m + 1) 1 :=
  homAt x0 (jetTrunc : Jet S (Fin 1 × Fin d) (m + 1) →ₐ[S] Jet S (Fin 1 × Fin d) m)
variable {t x0 d x}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
end GermD
end Formalism.MainNotions.ModuliIntegralCharts.H1


