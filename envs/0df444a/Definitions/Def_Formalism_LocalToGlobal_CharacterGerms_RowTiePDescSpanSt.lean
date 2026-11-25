-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:31:09.282468+00:00
-- url     : https://prove2.me/theorems/7b602257-6674-4c4a-a508-e9b4a928d93c
-- title:
--   Row Tie PDesc Span St
-- statement:
--   Definitions and structural lemmas for Row Tie PDesc Span St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePDescSpanSt.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescJet
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
def HaSpanSt : Prop :=
  ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (K : Type) [Field K] [CharZero K] (O : Subring K), ∀ P ∈ HaO r n K O cc isX a,
    ∃ (m : ℕ) (c : Fin m → K) (Z : Fin m → MvPolynomial (Letter Ty r n) ℤ), (∀ i, c i ∈ O) ∧
      (∀ i (K' : Type) [Field K'] [CharZero K'], MvPolynomial.map (Int.castRingHom K') (Z i) ∈ HHa r n K' cc isX a) ∧
      P = ∑ i, c i • MvPolynomial.map (Int.castRingHom K) (Z i)
section Nab
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
def gofY (Y : FBChart C V O dd) (n : ℕ) : PS C n dd :=
  FB.expS C (((Y.k : ℕ) : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0))
end Nab
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
end Formalism.L2.FormalSeriesBounds


