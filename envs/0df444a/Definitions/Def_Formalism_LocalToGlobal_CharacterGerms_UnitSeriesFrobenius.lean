-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_UnitSeriesFrobenius
-- name    : Formalism_LocalToGlobal_CharacterGerms_UnitSeriesFrobenius
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:52:37.997034+00:00
-- url     : https://prove2.me/theorems/9fd50b61-ba87-4b79-a3ef-fea611283d75
-- title:
--   Unit Series Frobenius
-- statement:
--   Definitions and structural lemmas for Unit Series Frobenius, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/UnitSeriesFrobenius.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoefficientIdentityOfCurve
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
section Geo
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
def FBChart.nmul (Y : FBChart C V O dd) : ℕ → Pt C 1 dd
  | 0 => fun _ => 0
  | k + 1 => addOf Y.B.G.F (Y.nmul k) (pt C dd 0)
def FBChart.u2 (Y : FBChart C V O dd) : PS C 2 dd :=
  FB.expS C (ev (n := 2) ![pt C dd 0, comp1 (Y.nmul V.l) (pt C dd 1)] Y.h - MvPowerSeries.C (V.l : C) * Y.h)
def FBChart.V1 (Y : FBChart C V O dd) (j i : Fin dd) : C :=
  MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (Y.nmul V.l j)
def FBChart.fS (Y : FBChart C V O dd) (i : Fin dd) : PS C 1 dd := fun ν =>
  MvPowerSeries.coeff (ν.mapDomain (fun p : Fin 1 × Fin dd => ((0 : Fin 2), p.2)) +
    Finsupp.single ((1 : Fin 2), i) V.l) Y.u2
def FBChart.cS (Y : FBChart C V O dd) (j : Fin dd) : PS C 2 dd :=
  ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] (Y.sgP (Pi.single j 1)) -
    ev (n := 2) ![pt C dd 0] (Y.sgP (Pi.single j 1)) - ev (n := 2) ![pt C dd 1] (Y.sgP (Pi.single j 1))
end Geo
section Closed
def UnitSeriesIntegral : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd), IntS V Y.u2
def LMulFrobFBSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (j : Fin dd) (μ : Fin 1 × Fin dd →₀ ℕ), (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) →
      V.MM (MvPowerSeries.coeff μ (Y.nmul V.l j))
def UnitSeriesFrobenius : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (μ : Fin 2 × Fin dd →₀ ℕ), (∃ i, ¬ V.l ∣ μ ((1 : Fin 2), i)) →
      V.MM (MvPowerSeries.coeff μ Y.u2)
def CocycleFBSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (i : Fin dd) (μ : Fin 2 × Fin dd →₀ ℕ),
      V.MM (MvPowerSeries.coeff μ (ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] (Y.fS i) +
        ∑ j, Y.cS j * MvPowerSeries.C (Y.V1 j i) - ev (n := 2) ![pt C dd 0] (Y.fS i) -
          ev (n := 2) ![pt C dd 1] (Y.fS i) - Y.cS i ^ V.l))
def PsiCurveStepSt : Prop :=
  UnitSeriesIntegral → LMulFrobFBSt → UnitSeriesFrobenius → CocycleFBSt → FrobPowSt → PsiCurveFBSt
end Closed
end Formalism.L2.FormalSeriesBounds


