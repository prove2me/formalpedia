-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieValL
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:31.245921+00:00
-- url     : https://prove2.me/theorems/667aa960-f9e0-542c-a7d7-5b9b3ba8c177
-- title:
--   Row Tie Val L
-- statement:
--   Definitions and structural lemmas for Row Tie Val L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValL.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqSelfOfUnitGerm
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
def RawChart.TCoordSt {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
    {X : RawChart C d I κ} (Hc : ∀ g, X.CartHyp V g) : Prop :=
  ∀ (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
    ∀ (g : Fin 2) (c : I g), ∃ T : MvPowerSeries κ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst (fun x => X.expPt g x) T = upG g (t g c)
namespace VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type}
  [∀ o g, Fintype (I o g)]
end VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb]
section Pairs
variable {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
def ProjPullSt (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : Prop :=
  PairsSep Y p → ∀ (o : Orb) (g : Fin 2), ∃ π : Fin dd → PS C 1 dd, (∀ i, IntS V (π i)) ∧
    (∀ i, MvPowerSeries.constantCoeff (π i) = 0) ∧ ∀ i, pull1 Y p (π i) = toAllS o ((Y.raw (p o)).expPt g i)
end Pairs
section Self
variable {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
def ProjSelfSt (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : Prop :=
  SelfSep Y p → ∀ (o : Orb) (g : Fin 2), ∃ π : Fin 2 × Fin dd → PS C 2 dd, (∀ x, IntS V (π x)) ∧
    (∀ x, MvPowerSeries.constantCoeff (π x) = 0) ∧
    ∀ x, pull2 Y p (π x) = toAllS (I := IS I0) o ((Y.rawSelf (p o)).expPt g x)
end Self
end Formalism.L2.FormalSeriesBounds


