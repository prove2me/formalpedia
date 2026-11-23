-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
-- name    : Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:13.169671+00:00
-- url     : https://prove2.me/theorems/86d34f41-a483-4509-afc8-21e55d2e6f81
-- title:
--   Formal Group Points Torsion Free
-- statement:
--   Definitions and structural lemmas for Formal Group Points Torsion Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/FormalGroupPointsTorsionFree.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
namespace Formalism.ELL
open WeierstrassCurve
def InFormalGroupPoints {K : Type u} [NormedField K] {W : WeierstrassCurve K} : W.toAffine.Point → Prop
  | .zero => True
  | .some x _ _ => 1 < ‖x‖
open Classical in

def FormalGroupPointsSubgroup' : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntegralModel W → ‖W.Δ‖ = 1 →
    ∀ P Q : W.toAffine.Point, InFormalGroupPoints P → InFormalGroupPoints Q → InFormalGroupPoints (P + Q) ∧ InFormalGroupPoints (-P)
open Classical in

def FormalGroupPointsTorsionFree : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntegralModel W → ‖W.Δ‖ = 1 →
    ∀ (n : ℕ), ‖(n : K)‖ = 1 → ∀ P : W.toAffine.Point, InFormalGroupPoints P → n • P = 0 → P = 0
open Classical in

def TorsionIntegral : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntegralModel W → ‖W.Δ‖ = 1 →
    ∀ (n : ℕ), ‖(n : K)‖ = 1 → ∀ (x y : K) (h : W.toAffine.Nonsingular x y),
      n • (Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1 ∧ ‖y‖ ≤ 1
end Formalism.ELL


