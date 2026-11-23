-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:31.909996+00:00
-- url     : https://prove2.me/theorems/29cd4310-04f0-44bd-bef0-99c3a8bbc5dc
-- title:
--   Germ BSer
-- statement:
--   Definitions and structural lemmas for Germ BSer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBSer.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
section JetSubst
variable {S : Type} [CommRing S] {κ κ' : Type}
end JetSubst
section Series
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ)
abbrev ρn (n m : ℕ) : jOG x0 d m n ⟶ jOG x0 d (m + 1) n :=
  homAt x0 (jetTrunc : Jet S (Fin n × Fin d) (m + 1) →ₐ[S] Jet S (Fin n × Fin d) m)
end Series
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB


