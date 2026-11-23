-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:07:12.832176+00:00
-- url     : https://prove2.me/theorems/5241951b-a63c-4faa-b84f-0125fc7c81a6
-- title:
--   Germ BPrim
-- statement:
--   Definitions and structural lemmas for Germ BPrim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermBPrim.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer
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
section Base
variable {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
def divLinB (φ : K → (X ⟶ X)) (ε : K → ℤ) (w : LB.Gen (LB.div (LB.LinComb L φ ε) L)) :
    LB.Gen (LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)) :=
  ⟨fun j => res (fun _ hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k),
      Set.mem_iInter.1 hy (Sum.inl 0)⟩ :
    LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j ≤ (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)))
    (w.s (j ∘ Sum.inr, j (Sum.inl 0)))⁻¹⟩
end Base
section Tools
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
end Tools
section Prim
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
abbrev zz : 𝟙_ (Over X0) ⟶ t.G ⊗ t.G := lift (η[t.G] : 𝟙_ (Over X0) ⟶ t.G) (η[t.G] : 𝟙_ (Over X0) ⟶ t.G)
end Prim
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB


