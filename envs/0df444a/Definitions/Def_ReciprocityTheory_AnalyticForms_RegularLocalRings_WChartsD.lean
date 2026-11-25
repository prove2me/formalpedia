-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsD
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:53:32.351869+00:00
-- url     : https://prove2.me/theorems/9e312903-8353-5962-b477-02b1825560fc
-- title:
--   WCharts D
-- statement:
--   Definitions and structural lemmas for WCharts D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/WChartsD.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open MvPolynomial AlgebraicGeometry CategoryTheory
noncomputable section
def fracR {R : Type} [CommRing R] {m : ℕ} (g : Fin m → R) (i k : Fin m) : FinalTheorems.reesChart g i :=
  ⟨IsLocalization.mk' (Localization.Away (g i)) (g k)
    (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)), Algebra.subset_adjoin ⟨k, rfl⟩⟩
variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
def yC {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k) {m : ℕ}
    (g : Fin m → Γ(projX P hP, (chartOpen hP p).1)) (i : Fin m) :
    Fin (Fintype.card (Σ k, ι k) + m) → FinalTheorems.reesChart g i :=
  fun l => Sum.elim (fun a => algebraMap _ (FinalTheorems.reesChart g i)
    (chartCoord hP p ((Fintype.equivFin _).symm a))) (fracR g i) (finSumFinEquiv.symm l)
end
end ReciprocityTheory.AnForm.R


