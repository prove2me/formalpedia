-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
-- name    : Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:17:59.227549+00:00
-- url     : https://prove2.me/theorems/9e5e570c-02cb-46df-b80f-6305a740c85a
-- title:
--   Constant Coeff Single Point Zero
-- statement:
--   Definitions and structural lemmas for Constant Coeff Single Point Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ConstantCoeffSinglePointZero.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SubstSubst
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
namespace VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
section Pull
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))
end Pull
section Emb
variable {n : ℕ}
def eRow (b : Fin n) : WVO I ↪ Fin n × WVO I := ⟨fun w => (b, w), Prod.mk_right_injective b⟩
def eAll (n : ℕ) (o : Orb) : Fin n × WV (I o) ↪ Fin n × WVO I :=
  ⟨fun x => (x.1, (⟨o, x.2⟩ : WVO I)), fun x y h => by
    have h1 : x.1 = y.1 := (Prod.ext_iff.1 h).1
    have h2 : (⟨o, x.2⟩ : WVO I) = ⟨o, y.2⟩ := (Prod.ext_iff.1 h).2
    exact Prod.ext h1 (eq_of_heq (Sigma.mk.inj h2).2)⟩
end Emb
end VP
end Formalism.L2.FormalSeriesBounds


