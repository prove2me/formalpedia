-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_PadicMult
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_PadicMult
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:20.838581+00:00
-- url     : https://prove2.me/theorems/c0268df8-9d51-42ac-98b8-8c6bbff39479
-- title:
--   Padic Mult
-- statement:
--   Definitions and structural lemmas for Padic Mult, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/PadicMult.lean

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
namespace Formalism.ELL.PadicMultiplication
open Formalism.G Formalism.G.LogP
section Ring
variable {R : Type*} [CommRing R]
def mulN (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | m + 1 => MvPowerSeries.subst (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R)
      F.toPowerSeries
end Ring
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
end Formalism.ELL.PadicMultiplication
namespace Formalism.ELL.PadicMultiplication
open Formalism.G Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
def coeffPoly (l e : PowerSeries K) (n : ℕ) : Polynomial K :=
  ∑ d ∈ Finset.range (n + 1),
    Polynomial.C (coeff d e * coeff n (l ^ d)) * Polynomial.X ^ d
end Formalism.ELL.PadicMultiplication
namespace Formalism.ELL
open Formalism.G Formalism.ELL.PadicMultiplication
end Formalism.ELL


