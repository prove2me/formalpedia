-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjLogResCOfCR
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjLogResCOfCR
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:05.39148+00:00
-- url     : https://prove2.me/theorems/f3da97ff-0a1e-4d1b-8939-cb59ae4d5727
-- title:
--   Proj Log Res COf CR
-- statement:
--   Definitions and structural lemmas for Proj Log Res COf CR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ProjLogResCOfCR.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjHyp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
namespace ReciprocityTheory.AnForm.R
namespace FinalTheorems
def GFLogStC : Prop :=
  ∀ (X : Scheme.{0}) [IsNoetherian X], (∃ f : X ⟶ Spec (CommRingCat.of ℂ), LocallyOfFiniteType f) →
    QE X → IsReduced X → FFinRes X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ → LogResStC X B
end FinalTheorems
def ProjLogResC : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P), IsMultiHomogIdeal D → P.IsRadical →
    (∀ (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval y h = 0) →
      ¬ IsRegularLocalRing (chartLocRing P p y) → ∀ f ∈ D, eval y f = 0) →
    (∀ q ∈ P.minimalPrimes, IsRelevant q → ¬ D ≤ q) → FinalTheorems.LogResStC (projX P hP) (projB P D hP)
end ReciprocityTheory.AnForm.R


