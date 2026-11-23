-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:42.739542+00:00
-- url     : https://prove2.me/theorems/b414b0d5-f407-44cb-a537-48702da5486a
-- title:
--   Rho Dot Self
-- statement:
--   Definitions and structural lemmas for Rho Dot Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/RhoDotSelf.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.FundamentalDomainD5
open Matrix ComplexConjugate
variable {ι : Type} [Fintype ι] {r N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2)
def rho (w : ι → Fin r → ℂ) : Fin N → ℝ := fun k =>
  if (eqv k).2.2 = 0 then (w (eqv k).1 (eqv k).2.1).re else (w (eqv k).1 (eqv k).2.1).im
end Formalism.L2.Pj.FundamentalDomainD5


