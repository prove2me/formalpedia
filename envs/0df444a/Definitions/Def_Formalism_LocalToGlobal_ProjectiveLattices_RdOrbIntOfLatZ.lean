-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:41:49.734235+00:00
-- url     : https://prove2.me/theorems/14fb6f57-dbf8-490a-b87a-8aae89a9788e
-- title:
--   Rd Orb Int Of Lat Z
-- statement:
--   Definitions and structural lemmas for Rd Orb Int Of Lat Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RdOrbIntOfLatZ.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
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
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate
namespace Formalism.L2.Pj.FJ
section Core
variable {r ρ : ℕ}
def cM {m n : Type} (A : Matrix m n ℂ) : Matrix m n ℂ := A.map (starRingEnd ℂ)
end Core
section FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
def Fm (τ : E →+* ℂ) (e : Fin ρ → Fin r → E) : Matrix (Fin r) (Fin ρ) ℂ :=
  Matrix.of fun k a => τ (e a k)
end FD
end Formalism.L2.Pj.FJ


