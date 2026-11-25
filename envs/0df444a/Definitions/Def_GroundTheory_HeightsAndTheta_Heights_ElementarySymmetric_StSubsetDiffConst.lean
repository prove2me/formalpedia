-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StSubsetDiffConst
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StSubsetDiffConst
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:27:56.736825+00:00
-- url     : https://prove2.me/theorems/8e076eac-8c12-44fd-ad80-92665e9a8956
-- title:
--   St Subset Diff Const
-- statement:
--   Definitions and structural lemmas for St Subset Diff Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/StSubsetDiffConst.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperCutObj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
def subsetDiff (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ) (m : ℕ) (c : ℤ) : ℚ :=
  ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) *
    f (Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m) c
def SubsetDiffConst.Statement : Prop :=
  ∀ (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ), IsNumPolyLT (n + 1) (n + 1) f →
    (∀ (m m' : ℕ) (c c' : ℤ), subsetDiff n f m c = subsetDiff n f m' c') ∧
      (IsNumPolyLT (n + 1) n f → ∀ (m : ℕ) (c : ℤ), subsetDiff n f m c = 0)
end
end GroundTheory.Heights₂.Heights.Kleiman


