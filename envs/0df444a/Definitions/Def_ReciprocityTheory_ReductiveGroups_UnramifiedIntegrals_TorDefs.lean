-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_TorDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:56.998041+00:00
-- url     : https://prove2.me/theorems/6564a6dc-af2b-4dd5-8893-b64952cdca4b
-- title:
--   Tor Defs
-- statement:
--   Definitions and structural lemmas for Tor Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/TorDefs.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_CMGoodModels_CM4
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM Formalism.ELL WeierstrassCurve
open Formalism.L2.Th1.E (px py IntCurve)
open Formalism.L2.Th1.A (shortW)
def InSub {C : Type} [Field C] (K : Subfield C) {W : WeierstrassCurve C} : W.toAffine.Point → Prop
  | .zero => True
  | .some x y _ => x ∈ K ∧ y ∈ K
def CoeffSub {C : Type} [Field C] (K : Subfield C) (W : WeierstrassCurve C) : Prop :=
  W.a₁ ∈ K ∧ W.a₂ ∈ K ∧ W.a₃ ∈ K ∧ W.a₄ ∈ K ∧ W.a₆ ∈ K
structure GoodPair (l : ℕ) [Fact l.Prime] (g2 g3 : ℂ_[l]) : Prop where
  five : 5 ≤ l
  mem2 : g2 ∈ MaximalUnramifiedExtension l
  mem3 : g3 ∈ MaximalUnramifiedExtension l
  norm2 : ‖g2‖ ≤ 1
  norm3 : ‖g3‖ ≤ 1
  disc : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1
def TorPt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (lam : ℂ_[l]), lam ≠ 0 →
    ∀ (z : ℂ) (N : ℕ), (N : ℂ) * z ∈ L.lattice → z ∉ L.lattice →
      ∃ h : (shortW (lam ^ 4 * ι L.g₂) (lam ^ 6 * ι L.g₃)).toAffine.Nonsingular
          (lam ^ 2 * ι (L.weierstrassP z)) (lam ^ 3 * ι (L.derivWeierstrassP z) / 2),
        N • WeierstrassCurve.Affine.Point.some _ _ h = 0
end ReciprocityTheory.ChartRestriction.L1


