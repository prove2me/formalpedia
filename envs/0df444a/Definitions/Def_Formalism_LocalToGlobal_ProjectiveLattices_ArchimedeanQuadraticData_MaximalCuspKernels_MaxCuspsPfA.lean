-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:25:30.027651+00:00
-- url     : https://prove2.me/theorems/7db8238e-0d99-48b0-b697-4f7ca2d254f0
-- title:
--   Max Cusps Pf A
-- statement:
--   Definitions and structural lemmas for Max Cusps Pf A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/MaximalCuspKernels/MaxCuspsPfA.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
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
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix Formalism.L2.Pj.FJ Complex
open scoped ComplexConjugate
namespace Formalism.L2.Pj.QAt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
def mcMη (η : Fin ρ → E) : Matrix (Fin ρ) (Fin ρ) E := Matrix.of fun a b => η a * cc (η b)
def mcMηc (τ : E →+* ℂ) (η : Fin ρ → E) : Matrix (Fin ρ) (Fin ρ) ℂ :=
  Matrix.of fun a b => τ (η a) * conj (τ (η b))
def mcBeta (X : Data E r) (la : Wt X.Ψ r) (η : Fin ρ → E) (a : E) : Matrix (Fin ρ) (Fin ρ) E :=
  ((X.m : E) * ((X.chiOrd la : E) * a) * X.κ0) • mcMη η
end Formalism.L2.Pj.QAt


