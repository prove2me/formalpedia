-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieChar
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieChar
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-27T04:46:56.721346+00:00
-- url     : https://prove2.me/theorems/ac2a7f77-11a3-4a04-a2f1-4c2811895d69
-- title:
--   Row Tie Char
-- statement:
--   Definitions and structural lemmas for Row Tie Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieChar.lean

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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]
def FBChart.IsChar (Y : FBChart C V O dd) (χ : PS C 1 dd) : Prop :=
  IntS V χ ∧ MvPowerSeries.constantCoeff χ = 1 ∧
    ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] χ = ev (n := 2) ![pt C dd 0] χ * ev (n := 2) ![pt C dd 1] χ
def dlogC (χ : PS C 1 dd) (i : Fin dd) : C := MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) 1) χ
def PairData.yOf {Y : FBChart C V O dd} (p : PairData Y d I) (g : Fin 2) (χ : PS C 1 dd) (x : I g) : C :=
  ∑ i, dlogC χ i * p.u g x i
def CharGermSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I)
    (Hc : ∀ g, (Y.raw p).CartHyp V g) (χ : PS C 1 dd), Y.IsChar χ →
    ∀ (g : Fin 2) (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈ IntGerm V t
def CHCharSt (Y : FBChart C V O dd) (p : PairData Y d I) : Prop :=
  ∀ g a, p.big g a → ∀ w : Fin p.n → I g → C, IsSat V w → (∀ c x, p.ty g x ≠ a → w c x = 0) →
    ∃ χ : Fin p.n → PS C 1 dd, (∀ ρ, Y.IsChar (χ ρ)) ∧
      ((Y.raw p).AltC →
        V.v (Matrix.of fun ρ c : Fin p.n => ∑ x, p.yOf g (χ ρ) x * w c x).det ≤
          (((p.n : ℝ) * gam V.l + ((p.j : ℝ) + p.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ)) ∧
      ((∀ a, p.big g a) →
        V.v (Matrix.of fun ρ c : Fin p.n => ∑ x, p.yOf g (χ ρ) x * w c x).det ≤
          ((((p.j : ℝ) + p.j') / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ))
section Chart
open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]
def CharacterHypothesisCharts : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d) (ha : LabArith V io ι lab) (hg : LabGeo C3 ι Y lab),
    lab.RankOK Dw → ∀ o, CHCharSt Y (pairOfLab ha hg o)
end Chart
end Formalism.L2.FormalSeriesBounds


