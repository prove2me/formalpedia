-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:01.950114+00:00
-- url     : https://prove2.me/theorems/9a9b1d84-84f7-40cc-bee1-4d07267bf0db
-- title:
--   HQsmul Right
-- statement:
--   Definitions and structural lemmas for HQsmul Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/HQsmulRight.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_RhoDotSelf
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
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
open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}
def Phi (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ) (v : Fin r → K) : ι → Fin r → ℂ :=
  fun i => Q i *ᵥ embVec (σ i) v
def Theta (p : ℕ) (w : ι → Fin r → ℂ) : ι → Fin r → ℂ := fun i a => sgn p a * w i a
section Herm
variable (S : HermForm K r)
end Herm
end Formalism.L2.Pj.FundamentalDomainD5


