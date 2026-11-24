-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementU
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementU
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T22:07:08.253047+00:00
-- url     : https://prove2.me/theorems/b4ff1ee1-5505-4e26-83e0-922de6041c7c
-- title:
--   Statement U
-- statement:
--   Definitions and structural lemmas for Statement U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/RamifiedCurveKernels/StatementU.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementT
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
namespace Formalism.L2.Th1.G
open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (jetPair)
def CurveKernelUnram : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (W : WeierstrassCurve K),
    CoeffIn (unitBall K) W → ‖(2 : K)‖ = 1 →
    ∀ (s2 al albar : K) (t : ℤ) (ι : Type) [Fintype ι] (neg : ι → ι) (xP yP : ι → K),
    IsEndoCurve W neg xP yP al → (∀ P, ‖xP P‖ ≤ 1) → (∀ P, ‖yP P‖ ≤ 1) →
    al * albar = (Fintype.card ι : K) + 1 → ‖al‖ = 1 → al + albar = (t : K) →
    ‖al - albar‖ = 1 → ‖(al ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 →
    al * (al - albar) * s2 = ∑ P, (xP P + W.b₂ / 12) →
    ∀ (n : Type) [Fintype n] (c : n → K), (∀ i, ‖c i‖ ≤ 1) →
    ∀ G : MvPowerSeries n K, IntMv (unitBall K) G →
    ∀ P : MvPolynomial n K, (∀ m, ‖MvPolynomial.coeff m P‖ ≤ 1) →
      ‖jetPair P (toZ (expSer W) (mvExp (-(phSum c (Formalism.L2.Th1.B.phO s2 (wpReg W) (logSer W)))) * G))‖ ≤ 1
end Formalism.L2.Th1.G


