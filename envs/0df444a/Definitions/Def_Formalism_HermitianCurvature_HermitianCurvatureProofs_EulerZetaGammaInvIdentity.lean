-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:17.499824+00:00
-- url     : https://prove2.me/theorems/2f1a8600-784e-4d72-bb69-db7840ae95b2
-- title:
--   Euler Zeta Gamma Inv Identity
-- statement:
--   Definitions and structural lemmas for Euler Zeta Gamma Inv Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EulerZetaGammaInvIdentity.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
noncomputable def sR (P : Par) (l : ℕ) : Matrix (Ty P) (Ty P) ℝ :=
  Matrix.of fun π' π => if Up P l π π' then Real.sqrt (Nrm P l π) else 0
noncomputable def ioR (P : Par) : Matrix (Ty P) (Ty P) ℝ →+* A P :=
  ((algebraMap ℂ (Pr P.r)).comp Complex.ofRealHom).mapMatrix
end Formalism.FourierDecayAlt.P.Mx4
namespace Formalism.FourierDecayAlt.P
open Mx4
end Formalism.FourierDecayAlt.P


