-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
-- name    : Formalism_LocalToGlobal_CharacterGerms_RankMaximalOfNondegenerate
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T04:55:56.87894+00:00
-- url     : https://prove2.me/theorems/6b1c7691-d221-46a2-9d68-06a32d059706
-- title:
--   Rank Maximal Of Nondegenerate
-- statement:
--   Definitions and structural lemmas for Rank Maximal Of Nondegenerate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RankMaximalOfNondegenerate.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
section Agr
variable {C : Type} [Field C]
def Agr {τ : Type} (k : ℕ) (f g : MvPowerSeries τ C) : Prop :=
  ∀ e : τ →₀ ℕ, e.degree < k → MvPowerSeries.coeff e f = MvPowerSeries.coeff e g
end Agr
section Wit
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
def RawChart.TyWit (X : RawChart C d I κ) (V : VF C) (g : Fin 2) (x : ℕ → I g ⊕ JJ I g → C)
    (γ : κ → PowerSeries C) (lam : JJ I g → PowerSeries C) : Prop :=
  IsCv V γ ∧ IsCv V lam ∧
    (∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c))) ∧
    ∀ q : JJ I g, tyS V.l (fun s => x s (Sum.inr q)) =
      lam q - alongCv γ (X.sg (X.u (1 - g) q)) +
        ∑ c : I g, if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x s (Sum.inl c)) else 0
end Wit
def RankMaximalInitialCoefficient : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, (Y.raw p).AltC →
    ∀ (g : Fin 2) (a : ZMod d), (Y.raw p).big g a →
    ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (Hc g)).Good a w x →
    (∀ q, V.MM ((RawChart.cart (Hc g)).c0' x q)) →
    ∀ (γ : Fin dd → PowerSeries C) (lam : JJ I g → PowerSeries C), (Y.raw p).TyWit V g x γ lam →
      ∃ b : PS C 1 dd, IntS V b ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ
        (Y.chartLinearTerm (fun i => PowerSeries.coeff 1 (γ i)) -
          (ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] b - ev (n := 2) ![pt C dd 0] b -
            ev (n := 2) ![pt C dd 1] b)))
section MM
variable {C : Type} [Field C] {V : VF C}
end MM
section Step2
variable {C : Type} [Field C]
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)]
end Step2
end Formalism.L2.FormalSeriesBounds


