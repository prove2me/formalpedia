-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:12:19.324379+00:00
-- url     : https://prove2.me/theorems/249a6924-2329-480b-bfdc-7de255d7fbe7
-- title:
--   Vandermonde Ratio Harmonic
-- statement:
--   Definitions and structural lemmas for Vandermonde Ratio Harmonic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
end Formalism.FourierDecayAlt.P.Sz3
namespace Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
noncomputable def NF (J : ℕ) (de : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Icc 1 J, (∑ i ∈ Ioc d J, de i - ∑ i ∈ Icc 1 (J - d), de i) / (d : ℝ)
end Formalism.FourierDecayAlt.P.Sz3
namespace Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz
noncomputable def hs (n : ℕ) : ℝ := ∑ d ∈ Ioc 0 n, 1 / (d : ℝ)
noncomputable def xx (de : ℕ → ℝ) (i i' : ℕ) : ℝ := (de i' - de i) / (4 * ((i' : ℝ) - (i : ℝ)))
end Formalism.FourierDecayAlt.P.Sz3
namespace Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.Sz Sz3
end Formalism.FourierDecayAlt.P


