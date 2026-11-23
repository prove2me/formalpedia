-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_MemConePtsIffChartIdeal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:40.813918+00:00
-- url     : https://prove2.me/theorems/a768f55a-915f-4943-99a4-3087fae29235
-- title:
--   Mem Cone Pts Iff Chart Ideal
-- statement:
--   Definitions and structural lemmas for Mem Cone Pts Iff Chart Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/MemConePtsIffChartIdeal.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def IsMultiHomogIdeal (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Prop :=
  ∃ S : Set (MvPolynomial (Σ k, ι k) ℂ), (∀ f ∈ S, ∃ a, IsMultiHomog f a) ∧ P = Ideal.span S
def IsRelevant (W : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Prop :=
  ∀ k, ∃ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ W
def chartIdeal (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  P ⊔ Ideal.span (Set.range fun k => (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ))
abbrev chartRing (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) : Type :=
  MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p
end
end ReciprocityTheory.AnForm.R


