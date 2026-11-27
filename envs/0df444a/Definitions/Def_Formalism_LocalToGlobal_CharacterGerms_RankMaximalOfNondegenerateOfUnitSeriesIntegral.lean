-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerateOfUnitSeriesIntegral
-- name    : Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerateOfUnitSeriesIntegral
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-27T05:24:15.867726+00:00
-- url     : https://prove2.me/theorems/5b9ca9b7-14b5-54a1-b449-911ff8f02a83
-- title:
--   Rank Maximal Of Nondegenerate Of Unit Series Integral
-- statement:
--   Definitions and structural lemmas for Rank Maximal Of Nondegenerate Of Unit Series Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerateOfUnitSeriesIntegral.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstStepSecondHalfCondition
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieProj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_u1

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
section Defs
variable {C : Type} [Field C]
def mulL {dd : ℕ} (F : Fin dd → PS C 2 dd) : ℕ → Pt C 1 dd
  | 0 => fun _ => 0
  | n + 1 => addOf F (mulL F n) (pt C dd 0)
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
def FBChart.u1 (Y : FBChart C V O dd) : PS C 2 dd :=
  FB.expS C (ev (n := 2) ![comp1 (mulL Y.B.G.F V.l) (pt C (n := 2) dd 0), pt C dd 1] Y.h - (V.l : C) • Y.h)
def FBChart.aOf (Y : FBChart C V O dd) (u : Fin dd → C) : PS C 1 dd :=
  fun ν => ∑ i, u i ^ V.l * MvPowerSeries.coeff
    (Finsupp.single ((0 : Fin 2), i) V.l + ν.mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1
end Defs
def FirstUnitSeriesIntegral : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd), IntS V Y.u1
def FirstUnitSeriesFrobenius : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (μ : Fin 2 × Fin dd →₀ ℕ), (∃ i, ¬ V.l ∣ μ ((0 : Fin 2), i)) →
      V.MM (MvPowerSeries.coeff μ Y.u1)
def MulLFrobSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (k : Fin dd) (μ : Fin 1 × Fin dd →₀ ℕ), (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) →
      V.MM (MvPowerSeries.coeff μ (mulL Y.B.G.F V.l k))
def GoodAll (Φ : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)], FBChart C V O dd → (Fin dd → C) → Prop) : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, (Y.raw p).AltC →
    ∀ (g : Fin 2) (a : ZMod d), (Y.raw p).big g a →
    ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (Hc g)).Good a w x →
    (∀ q, V.MM ((RawChart.cart (Hc g)).c0' x q)) →
    ∀ (γ : Fin dd → PowerSeries C) (lam : JJ I g → PowerSeries C), (Y.raw p).TyWit V g x γ lam →
      Φ C V O dd d I Y (fun i => PowerSeries.coeff 1 (γ i))
def GoodVectorsMulPrimePowerCoefficientsVanish : Prop :=
  GoodAll fun _ _ _ V _ _ _ dd _ _ _ Y u => ∀ k : Fin dd,
    V.MM (∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) (mulL Y.B.G.F V.l k) * u i ^ V.l)
def NoLinSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    ProjSt Y p → (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, (Y.raw p).AltC →
    ∀ (g : Fin 2) (a : ZMod d), (Y.raw p).big g a →
    ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (Hc g)).Good a w x →
    (∀ q, V.MM ((RawChart.cart (Hc g)).c0' x q)) →
    ∀ (γ : Fin dd → PowerSeries C) (lam : JJ I g → PowerSeries C), (Y.raw p).TyWit V g x γ lam →
      ∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)
        (Y.aOf (fun i => PowerSeries.coeff 1 (γ i))))
def FunEqSt : Prop :=
  GoodAll fun _ _ _ V _ _ _ _ _ _ _ Y u => ∀ μ,
    V.MM (MvPowerSeries.coeff μ (cobd Y.B.G.F (Y.aOf u) - frobTw V.l (Y.chartLinearTerm u)))
end Formalism.L2.FormalSeriesBounds


