-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:28.233889+00:00
-- url     : https://prove2.me/theorems/0eeeb5cb-2fe3-48d1-8943-122fd24e0465
-- title:
--   Statement A
-- statement:
--   Definitions and structural lemmas for Statement A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/StatementA.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
def LemmaA : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu → ∀ (F : Type) [Field F],
    LinearIndependent F (fun I : {I : TIdx mu // StdT I} => mapCoord (n := n) F (brk mu I.1))
def SBasis : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ), Dominant mu →
    LinearIndependent ℤ (fun I : {I : TIdx mu // StdT I} => brk mu I.1) ∧
    Submodule.span ℤ (Set.range fun I : {I : TIdx mu // StdT I} => brk mu I.1) = SMu mu
end Formalism.InvariantFactorPaths.ColumnFamilies


