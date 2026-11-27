-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_JetAt0ProdRename
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_JetAt0ProdRename
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-27T04:59:21.614162+00:00
-- url     : https://prove2.me/theorems/5821e55c-a489-595e-a8b0-8ac5d8c6e052
-- title:
--   Jet At0 Prod Rename
-- statement:
--   Definitions and structural lemmas for Jet At0 Prod Rename, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/JetAt0ProdRename.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.JetProd
open Finsupp
section General
variable {C : Type} [Field C] {ι τ : Type} [Fintype ι] {σ : ι → Type} (e : ∀ i, σ i ↪ τ)
end General
section Rows
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]
def rowEmb {N : ℕ} (ρ : Fin N) : WV I ↪ Fin N × WV I :=
  ⟨fun w => (ρ, w), fun _ _ h => congrArg Prod.snd h⟩
noncomputable def rowSer (hL : Fin 2 → ZMod d → ZMod d → MvPowerSeries (WV I) C) (k : Knd d)
    (g : MvPowerSeries (WV I) C) : MvPowerSeries (WV I) C :=
  g * mvExp (match k with
      | Option.some (g, a, a') => hL g a a'
      | none => 0)
end Rows
end GlobalTheory.JetProd


