-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:17:13.2438+00:00
-- url     : https://prove2.me/theorems/8fd8e673-1170-4774-a9b9-4d0a0bb7ca52
-- title:
--   Herglotz
-- statement:
--   Definitions and structural lemmas for Herglotz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Herglotz.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.Herglotz
open Real Filter Topology Finset
variable {d : ℕ}
noncomputable def ee (x : Fin d → ℝ) (σ : Fin d → ℤ) : ℂ :=
  Complex.exp (2 * π * Complex.I * ∑ j, ((σ j : ℝ) : ℂ) * (x j : ℂ))
noncomputable def box (d N : ℕ) : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Finset.Ico (0 : ℤ) N)
noncomputable def fac (N : ℕ) (t : ℤ) : ℝ := (((N : ℤ) - |t|).toNat : ℝ) / N
noncomputable def wt (N : ℕ) (τ : Fin d → ℤ) : ℝ := ∏ j, fac N (τ j)
end Formalism.FourierDecayAlt.P.Herglotz
namespace Formalism.FourierDecayAlt.P
open Real Filter Topology Finset Formalism.FourierDecayAlt.P.Herglotz
end Formalism.FourierDecayAlt.P


