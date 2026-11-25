-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_PairsK
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_PairsK
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:10:01.319476+00:00
-- url     : https://prove2.me/theorems/4593c644-2761-5740-8256-bca527f829ab
-- title:
--   Pairs K
-- statement:
--   Definitions and structural lemmas for Pairs K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/UniformGaussModels/PairsK.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_UniformGaussModels_GoodModelAll
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
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
namespace Formalism.L2.Th1.Top
open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer)
open Formalism.G (unitBall)
def pairsK (dK p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Set.range fun mn : ℤ × ℤ =>
    (ι ((mn.1 : ℂ) + (mn.2 : ℂ) * omegaK dK), ι ((mn.1 : ℂ) + (mn.2 : ℂ) * (1 - omegaK dK))))
def CalcP : Prop :=
  ∀ (dK : ℕ) (L : PeriodPair), dK % 4 = 3 → HasCMBy dK L →
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ι : ℂ ≃+* ℂ_[p], IntCurve (curveL p L ι) →
    Formalism.L2.Th1.C.Frame (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) ∧
    Formalism.L2.Th1.C.F1 (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) ∧
    (∀ a b : ℂ_[p], (a, b) ∈ pairsK dK p ι →
      Formalism.L2.Th1.C.EndInt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) a ∧
      Formalism.L2.Th1.C.PhNormAt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) a b ∧
      Formalism.L2.Th1.C.AdjAt (unitBall ℂ_[p]) (logSer (curveL p L ι)) (expSer (curveL p L ι)) (phC p L ι) a b) ∧
    (∀ a : ℂ_[p], (a, a) ∈ pairsK dK p ι → Formalism.L2.Th1.C.IsBinomScalar (unitBall ℂ_[p]) a)
end Formalism.L2.Th1.Top


