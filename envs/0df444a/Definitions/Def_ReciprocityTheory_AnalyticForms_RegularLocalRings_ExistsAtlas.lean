-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsAtlas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:02.576155+00:00
-- url     : https://prove2.me/theorems/2d386077-d64a-44b3-9a48-7ca6c77a7fcd
-- title:
--   Exists Atlas
-- statement:
--   Definitions and structural lemmas for Exists Atlas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsAtlas.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AnChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_AtlasA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def AlgRes.IsGoodAtlas {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : AlgRes ι P D e)
    (A : FinHolAtlas e R.M) : Prop :=
      (∀ i (h : MvPolynomial (Fin (R.amb i)) ℂ),
        A.HoloOn (R.src i) fun x => eval (R.coord i x) h) ∧
      ∀ i, ∀ x ∈ R.src i, ∀ (r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ),
        Ideal.span (Set.range fun l => algebraMap _ (locRing (R.ideal i) (R.coord i x)) (r l)) =
          Ideal.map (algebraMap _ (locRing (R.ideal i) (R.coord i x))) (ptIdeal (R.coord i x)) →
        ∀ O : Set R.M, IsOpen O → x ∈ O →
          ∃ ψ : OpenPartialHomeomorph R.M (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
            ψ.source ⊆ O ∩ R.src i ∧ ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y)
end ReciprocityTheory.AnForm.R


