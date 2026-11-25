-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieDesc
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:15:23.839871+00:00
-- url     : https://prove2.me/theorems/62e7132d-18b6-4e1a-9c75-c00310e2a749
-- title:
--   Row Tie Desc
-- statement:
--   Definitions and structural lemmas for Row Tie Desc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieDesc.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_HostTraceIdentity
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
section Chart
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
def chartDerivativeCoefficient (C3 : IntChart T io y) (k n : ℕ) (f : PS T.Fr n (chD C3.ch)) (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  nabValN (a3B C3) T.Fr (a3h C3) H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => chartUnitVectors C3 ⟨ℓ.1, ℓ.2.1⟩) P
end Chart
section Val
variable {C : Type} [Field C] {V : VF C}
end Val
variable (Xo c)
def NabMapSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C)
    (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : PS T.Fr n (chD C3.ch)) (P : MvPolynomial (LtN Dw n) T.Fr),
      Y.nab (chartLetterSystem C3 V ι a) n (MvPowerSeries.map ι f) (MvPolynomial.map ι P) = ι (chartDerivativeCoefficient C3 k n f P)
def DescSpanSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ P ∈ (chartLetterSystem C3 V ι a).FF n, ∀ f : PS C n (chD C3.ch), IntS V f →
      ∃ (m : ℕ) (r : Fin m → C) (Pi : Fin m → MvPolynomial (LtN Dw n) T.Fr) (fi : Fin m → PS T.Fr n (chD C3.ch)),
        (∀ i, V.Ge 0 (r i)) ∧ (∀ i, Pi i ∈ FFV (Dw := Dw) T a n) ∧ (∀ i, IsIntPS T (fi i)) ∧
        Y.nab (chartLetterSystem C3 V ι a) n f P =
          ∑ i, r i * Y.nab (chartLetterSystem C3 V ι a) n (MvPowerSeries.map ι (fi i)) (MvPolynomial.map ι (Pi i))
def NvalEqSt : Prop :=
  ∀ (T : CDVR) (C : Type) [Field C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ x : T.Fr, (WithBot.some (V.v (ι x)) : WithBot (WithTop ℝ)) = nval T.V (eOf T V) x
variable {Xo c}
end Formalism.L2.FormalSeriesBounds


