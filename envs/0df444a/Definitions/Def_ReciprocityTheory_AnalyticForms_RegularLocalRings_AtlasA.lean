-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AtlasA
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_AtlasA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:18.332851+00:00
-- url     : https://prove2.me/theorems/ffc4f559-331e-43b5-8c06-7222cab1f8c5
-- title:
--   Atlas A
-- statement:
--   Definitions and structural lemmas for Atlas A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/AtlasA.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
def AlgRes.GoodChart (R : AlgRes ι P D e) (ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)) : Prop :=
  ∃ i, ψ.source ⊆ R.src i ∧
    (∃ r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ, ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y)) ∧
    ∃ g : (Fin e → ℂ) → Fin (R.amb i) → ℂ, AnalyticOnNhd ℂ g ψ.target ∧
      ∀ w ∈ ψ.target, R.coord i (ψ.symm w) = g w
end ReciprocityTheory.AnForm.R


