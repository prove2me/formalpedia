-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
-- name    : Formalism_GaussJetBounds_GaussJetProofs_OrbMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:29.558358+00:00
-- url     : https://prove2.me/theorems/8684771b-9213-42e0-822a-6658398a04bf
-- title:
--   Orb Mul
-- statement:
--   Definitions and structural lemmas for Orb Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
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
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace OrbMul
section Pair
variable {K : Type} [Field K] {σ ι : Type}
end Pair
section Exps
variable {ι₁ ι₂ : Type}
def jn (a : ι₁ →₀ ℕ) (b : ι₂ →₀ ℕ) : ι₁ ⊕ ι₂ →₀ ℕ :=
  a.mapDomain Sum.inl + b.mapDomain Sum.inr
end Exps
section Along
variable {K : Type} [Field K] {ι₁ ι₂ σ₁ σ₂ : Type} [Finite ι₁] [Finite ι₂]
end Along
section Trunc
variable {K : Type} [Field K] {σ ι : Type} [Finite ι]
end Trunc
section Norm
variable {K : Type} [NormedField K] [IsUltrametricDist K] {σ₁ σ₂ : Type}
end Norm
end OrbMul
namespace OrbMul
end OrbMul
end Formalism.DworkPowerSeriesWeights


