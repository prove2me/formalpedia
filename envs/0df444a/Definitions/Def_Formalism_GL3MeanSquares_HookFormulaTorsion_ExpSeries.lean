-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_ExpSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:03:08.586908+00:00
-- url     : https://prove2.me/theorems/5ecf0a87-aad6-4d45-84e3-45605a764b35
-- title:
--   Exp Series
-- statement:
--   Definitions and structural lemmas for Exp Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/ExpSeries.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_LegendreCoefficient
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
open Finset Formalism.G Formalism.HermitianLattices.ExpSeriesBivariate
section Alg
variable {σ K : Type} [Field K] [Algebra ℚ K]
def Low (m : ℕ) (x : MvPowerSeries σ K) : Prop :=
  ∀ d : σ →₀ ℕ, d.degree < m → MvPowerSeries.coeff d x = 0
end Alg
section Normed
variable {σ K : Type} [NormedField K]
def CT (F : ℕ → MvPowerSeries σ K) (f : MvPowerSeries σ K) : Prop :=
  ∀ n, Filter.Tendsto (fun k => MvPowerSeries.coeff n (F k)) Filter.atTop
    (nhds (MvPowerSeries.coeff n f))
end Normed
end Formalism.HermitianLattices.ExpSeriesBivariate.ExpSeriesAddition
namespace Formalism.HermitianLattices.ExpSeriesBivariate
open ExpSeriesAddition
end Formalism.HermitianLattices.ExpSeriesBivariate


