-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:23.717939+00:00
-- url     : https://prove2.me/theorems/6ad44ceb-74ce-4e3e-b9c9-a8959b1a4de3
-- title:
--   Det Pow Diagonal Rows Block Jet Restrict
-- statement:
--   Definitions and structural lemmas for Det Pow Diagonal Rows Block Jet Restrict, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/DetPowDiagonalRowsBlockJetRestrict.lean

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators
noncomputable section
namespace GlobalTheory.DiagBlock
lemma embV_inj {n0 n : ℕ} (hn : n0 ≤ n) : Function.Injective (embV hn) :=
  ((Fin.castLE_injective hn).prodMap (Fin.castLE_injective hn)).sumMap
    ((Fin.castLE_injective hn).prodMap (Fin.castLE_injective hn))
section Kill
variable {R : Type} [CommRing R] {σ : Type}
def kill (S : σ → Prop) [DecidablePred S] : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval fun x => if S x then 0 else MvPolynomial.X x
end Kill
end GlobalTheory.DiagBlock


