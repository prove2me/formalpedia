-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassTwoFactorsLe
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassTwoFactorsLe
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:46:28.766072+00:00
-- url     : https://prove2.me/theorems/71d54bd0-c5f6-589f-a14e-9f816e0ca63b
-- title:
--   Squarefree Label Torus Mass Two Factors Le
-- statement:
--   Definitions and structural lemmas for Squarefree Label Torus Mass Two Factors Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SquarefreeLabelTorusMassTwoFactorsLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassUnionBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PowPadicValEqOneOfPrimePow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare.TwoFactors
variable {g : ℕ} [Fact g.Prime]
def PairAt (d e : ℕ) (x y : AlgebraicClosure (ZMod g)) (f : (ZMod g)[X]) : Prop :=
  (minpoly (ZMod g) x).natDegree = d ∧ (minpoly (ZMod g) y).natDegree = e ∧ minpoly (ZMod g) x ≠ minpoly (ZMod g) y ∧
    minpoly (ZMod g) x ∣ f ∧ minpoly (ZMod g) y ∣ f
def PairFor (d e l : ℕ) (f : (ZMod g)[X]) : Prop :=
  ∃ x y : AlgebraicClosure (ZMod g), x ^ (g ^ d - 1) = 1 ∧ y ^ (g ^ e - 1) = 1 ∧ SamePart l x y ∧ PairAt d e x y f
end GlobalTheory.BadShare.TwoFactors


