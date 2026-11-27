-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCH
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieCH
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-27T04:45:58.129676+00:00
-- url     : https://prove2.me/theorems/c9a34aaf-55c8-4e05-86fe-4dcf3f5fc46d
-- title:
--   Row Tie CH
-- statement:
--   Definitions and structural lemmas for Row Tie CH, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCH.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieTop
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.PGsh.Up CharacteristicFromRanks ValuationFitting
def RawChart.HTDPack {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
    [Fintype κ] {X : RawChart C d I κ} (Hc : ∀ g, X.CartHyp V g) : Prop :=
  ∃ (rh : ℕ) (h : Fin 2 → ℕ) (ht : ∀ g, Fin (h g) → I g → C) (vm : Valuation C NNReal)
    (R : Type) (_ : CommRing R) (_ : Algebra R C) (_ : Algebra ℤ_[V.l] R)
    (O : Type) (_ : CommRing O) (_ : Algebra ℤ_[V.l] O) (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (Hh : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp Hh),
    (∀ g i x, V.Ge 0 (ht g i x)) ∧ HodgeTateSetting V.l vm R O σ cp ∧
    Nonempty (Comparison₂ (fun g => RawChart.cart (Hc g)) X.big rh h ht vm R O σ cp gB Hh U) ∧
    ∀ g (i : Fin (h g)) (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈ IntGerm V t
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
def HodgeTateAllCharts : Prop := AllCharts Xo c fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.HTDPack Hc
end Formalism.L2.FormalSeriesBounds


