-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstStepSecondHalfCondition
-- name    : Formalism_LocalToGlobal_CharacterGerms_FirstStepSecondHalfCondition
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-27T05:12:53.529747+00:00
-- url     : https://prove2.me/theorems/f72686ac-4d58-46bb-9072-3fb78bbd44a5
-- title:
--   First Step Second Half Condition
-- statement:
--   Definitions and structural lemmas for First Step Second Half Condition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FirstStepSecondHalfCondition.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
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
def frobTw {σ : Type} (l : ℕ) (c : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun μ => if ∀ s, l ∣ μ s then (MvPowerSeries.coeff (μ.mapRange (fun n => n / l) (Nat.zero_div l)) c) ^ l else 0
def cobd {dd : ℕ} (F : Fin dd → PS C 2 dd) (b : PS C 1 dd) : PS C 2 dd :=
  ev (n := 2) ![addOf F (pt C dd 0) (pt C dd 1)] b - ev (n := 2) ![pt C dd 0] b - ev (n := 2) ![pt C dd 1] b
end Defs
def FirstStepFirstHalfCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, (Y.raw p).AltC →
    ∀ (g : Fin 2) (a : ZMod d), (Y.raw p).big g a →
    ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (Hc g)).Good a w x →
    (∀ q, V.MM ((RawChart.cart (Hc g)).c0' x q)) →
    ∀ (γ : Fin dd → PowerSeries C) (lam : JJ I g → PowerSeries C), (Y.raw p).TyWit V g x γ lam →
      ∃ A : PS C 1 dd, IntS V A ∧
        (∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A)) ∧
        ∀ μ, V.MM (MvPowerSeries.coeff μ
          (cobd Y.B.G.F A - frobTw V.l (Y.chartLinearTerm (fun i => PowerSeries.coeff 1 (γ i)))))
def FirstStepSecondHalfCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C), IsAlgClosed C →
    ∀ (dd : ℕ) (G : FGLaw C dd), (∀ i, IntS V (G.F i)) →
    ∀ (A : PS C 1 dd) (c : PS C 2 dd), IntS V A → IntS V c →
      (∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A)) →
      (∀ μ, V.MM (MvPowerSeries.coeff μ (cobd G.F A - frobTw V.l c))) →
      ∃ b : PS C 1 dd, IntS V b ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (c - cobd G.F b))
end Formalism.L2.FormalSeriesBounds


