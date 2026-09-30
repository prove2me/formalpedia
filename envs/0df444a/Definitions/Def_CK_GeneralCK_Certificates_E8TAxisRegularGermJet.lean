-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisRegularGermJet
-- name    : CK_GeneralCK_Certificates_E8TAxisRegularGermJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:30:53.69315+00:00
-- url     : https://prove2.me/theorems/0ee8bbc9-8745-4648-b8b9-8a0f58c774b2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisRegularGermJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisRegularGermJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisRegularGermJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisRegularGermJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisRegularGermJet.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8PositiveAxisGermJet
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisDeltaDirectionalJet
import Definitions.Def_CK_GeneralCK_Certificates_DyadicJet5Bounds

-- ===== source module GeneralCK.Certificates.E8TAxisRegularGermJet =====
section

/-!
# Regular endpoint jet for E8 t-axis certificates

The positive-range inverse recurrence cannot be evaluated as a smooth jet at
slope zero.  This module glues it to the proved analytic inverse germ on the
nonpositive side and proves the resulting raw order-five jet is sound at the
endpoint.
-/

namespace GeneralCK.Certificates.E8TAxisRegularGermJet

open Set Filter GeneralCK E8AnalyticGerm
open E8InverseJet5Bridge E8TAxisDeltaDirectionalJet E8PositiveAxisGermJet

noncomputable def analyticComponent (n : ℕ) (y : ℝ) : ℝ :=
  (iteratedDeriv n qGerm (y : ℂ)).re

noncomputable def patchComponent (f : ℝ → ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  if 0 < y then f y else analyticComponent n y

private theorem hasDerivAt_iteratedDeriv_qGerm (n : ℕ) {z : ℂ}
    (h : AnalyticAt ℂ qGerm z) :
    HasDerivAt (iteratedDeriv n qGerm) (iteratedDeriv (n + 1) qGerm z) z := by
  rw [iteratedDeriv_succ]
  have hcd : ContDiffAt ℂ (⊤ : WithTop ℕ∞) qGerm z := h.contDiffAt
  have hd : DifferentiableAt ℂ (iteratedDeriv n qGerm) z := by
    unfold iteratedDeriv
    exact (ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => ℂ) ℂ
      (fun _ => 1)).hasFDerivAt.differentiableAt.comp z
        (hcd.differentiableAt_iteratedFDeriv (by norm_num))
  exact hd.hasDerivAt

theorem hasDerivAt_analyticComponent (n : ℕ) :
    HasDerivAt (analyticComponent n) (analyticComponent (n + 1) 0) 0 := by
  change HasDerivAt (fun y : ℝ => (iteratedDeriv n qGerm (y : ℂ)).re)
    (iteratedDeriv (n + 1) qGerm 0).re 0
  exact (hasDerivAt_iteratedDeriv_qGerm n analyticAt_qGerm).real_of_complex

theorem patchComponent_eventually_eq_analytic {f : ℝ → ℝ} {n : ℕ}
    (h : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (f y : ℂ) = iteratedDeriv n qGerm (y : ℂ)) :
    patchComponent f n =ᶠ[nhds 0] analyticComponent n := by
  have hpos : patchComponent f n =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)] analyticComponent n := by
    filter_upwards [h, self_mem_nhdsWithin] with y hy hypos
    simp only [mem_Ioi] at hypos
    rw [patchComponent, if_pos hypos]
    exact_mod_cast congrArg Complex.re hy
  have hnon : patchComponent f n =ᶠ[nhdsWithin (0 : ℝ) (Iic 0)] analyticComponent n := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [mem_Iic] at hy
    simp [patchComponent, not_lt.mpr hy]
  rw [← nhdsWithin_univ, ← Ioi_union_Iic, nhdsWithin_union]
  exact ⟨hpos, hnon⟩

theorem patchComponent_hasDerivAt_zero {f g : ℝ → ℝ} {n : ℕ}
    (h : ∀ᶠ y : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      (f y : ℂ) = iteratedDeriv n qGerm (y : ℂ)) :
    HasDerivAt (patchComponent f n) (patchComponent g (n + 1) 0) 0 := by
  rw [patchComponent, if_neg (lt_irrefl 0)]
  exact (hasDerivAt_analyticComponent n).congr_of_eventuallyEq
    (patchComponent_eventually_eq_analytic h)

noncomputable def regularQJet : Jet5 :=
  ⟨patchComponent qJet.d0 0, patchComponent qJet.d1 1,
   patchComponent qJet.d2 2, patchComponent qJet.d3 3,
   patchComponent qJet.d4 4, patchComponent qJet.d5 5⟩

theorem regularQJet_soundAt_zero : regularQJet.SoundAt 0 := by
  let h := eventually_e8QCanonicalJet5_eq_analytic_all
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact patchComponent_hasDerivAt_zero h.d0
  · exact patchComponent_hasDerivAt_zero h.d1
  · exact patchComponent_hasDerivAt_zero h.d2
  · exact patchComponent_hasDerivAt_zero h.d3
  · exact patchComponent_hasDerivAt_zero h.d4

theorem patchComponent_hasDerivAt_of_pos {f g : ℝ → ℝ} {n : ℕ} {y : ℝ}
    (hy : 0 < y) (h : HasDerivAt f (g y) y) :
    HasDerivAt (patchComponent f n) (patchComponent g (n + 1) y) y := by
  have heq : patchComponent f n =ᶠ[nhds y] f := by
    filter_upwards [Ioi_mem_nhds hy] with z hz
    rw [patchComponent, if_pos (show 0 < z from hz)]
  simpa [patchComponent, hy] using h.congr_of_eventuallyEq heq

theorem regularQJet_soundAt_of_mem {y : ℝ} (hy : y ∈ e8SlopeRange) :
    regularQJet.SoundAt y := by
  have hp : 0 < y := e8SlopeRange_subset_pos hy
  have h := qJet_soundAt hy
  exact ⟨patchComponent_hasDerivAt_of_pos hp h.1,
    patchComponent_hasDerivAt_of_pos hp h.2.1,
    patchComponent_hasDerivAt_of_pos hp h.2.2.1,
    patchComponent_hasDerivAt_of_pos hp h.2.2.2.1,
    patchComponent_hasDerivAt_of_pos hp h.2.2.2.2⟩

theorem regularQJet_soundAt {y : ℝ} (hy : y = 0 ∨ y ∈ e8SlopeRange) :
    regularQJet.SoundAt y := by
  rcases hy with rfl | hy
  · exact regularQJet_soundAt_zero
  · exact regularQJet_soundAt_of_mem hy

theorem regularQJet_d0_eq_regular (y : ℝ) : regularQJet.d0 y = e8RegularQ y := by
  by_cases hy : 0 < y
  · simp [regularQJet, patchComponent, hy, qJet, e8RegularQ,
      E8InverseJet5Bridge.e8QJet5]
  · simp [regularQJet, patchComponent, hy, analyticComponent, iteratedDeriv_zero,
      e8RegularQ]

theorem regularQJet_d1_eq_deriv {y : ℝ} (hy : y = 0 ∨ y ∈ e8SlopeRange) :
    regularQJet.d1 y = deriv e8RegularQ y := by
  have heq : regularQJet.d0 = e8RegularQ := funext regularQJet_d0_eq_regular
  rw [← heq, (regularQJet_soundAt hy).1.deriv]

/-- At the regular endpoint, each analytic component is the corresponding
factorial-normalized Taylor coefficient multiplied back by its factorial. -/
theorem analyticComponent_zero_eq_factorial_mul (n : ℕ) :
    analyticComponent n 0 = (n.factorial : ℝ) * (qTaylorCoeff n).re := by
  have h : iteratedDeriv n qGerm 0 =
      qTaylorCoeff n * (n.factorial : ℂ) := by
    have hn : (n.factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    rw [qTaylorCoeff]
    field_simp [hn]
  change (iteratedDeriv n qGerm (0 : ℂ)).re =
    (n.factorial : ℝ) * (qTaylorCoeff n).re
  rw [h]
  simp [mul_comm]

theorem regularQJet_d2_zero : regularQJet.d2 0 = 0 := by
  rw [show regularQJet.d2 0 = analyticComponent 2 0 by
    simp [regularQJet, patchComponent]]
  rw [analyticComponent_zero_eq_factorial_mul,
    qTaylorCoeff_eq_zero_of_even (show Even 2 by decide)]
  norm_num

theorem regularQJet_d4_zero : regularQJet.d4 0 = 0 := by
  rw [show regularQJet.d4 0 = analyticComponent 4 0 by
    simp [regularQJet, patchComponent]]
  rw [analyticComponent_zero_eq_factorial_mul,
    qTaylorCoeff_eq_zero_of_even (show Even 4 by decide)]
  norm_num

theorem regularQJet_d0_zero : regularQJet.d0 0 = 0 := by
  rw [regularQJet_d0_eq_regular, e8RegularQ_zero]

theorem regularQJet_d1_zero : regularQJet.d1 0 = Real.log 2 / 8 := by
  rw [regularQJet_d1_eq_deriv (Or.inl rfl), hasDerivAt_e8RegularQ_zero.deriv]

theorem regularQJet_d3_zero :
    regularQJet.d3 0 = 6 * (qTaylorCoeff 3).re := by
  rw [show regularQJet.d3 0 = analyticComponent 3 0 by
    simp [regularQJet, patchComponent],
    analyticComponent_zero_eq_factorial_mul]
  norm_num

theorem regularQJet_d5_zero :
    regularQJet.d5 0 = 120 * (qTaylorCoeff 5).re := by
  rw [show regularQJet.d5 0 = analyticComponent 5 0 by
    simp [regularQJet, patchComponent],
    analyticComponent_zero_eq_factorial_mul]
  norm_num

/-- Punctured agreement in the exact component form used by interval boxes. -/
theorem regularQJet_eq_qJet_at_pos {y : ℝ} (hy : 0 < y) :
    regularQJet.d0 y = qJet.d0 y ∧ regularQJet.d1 y = qJet.d1 y ∧
    regularQJet.d2 y = qJet.d2 y ∧ regularQJet.d3 y = qJet.d3 y ∧
    regularQJet.d4 y = qJet.d4 y ∧ regularQJet.d5 y = qJet.d5 y := by
  simp [regularQJet, patchComponent, hy]

theorem DyadicJet5Enclosure.Contains.regular_of_pos {p : ℕ}
    {b : DyadicJet5Enclosure p} {y : ℝ}
    (h : b.Contains qJet y) (hy : 0 < y) :
    b.Contains regularQJet y := by
  rcases regularQJet_eq_qJet_at_pos hy with ⟨h0, h1, h2, h3, h4, h5⟩
  simpa only [DyadicJet5Enclosure.Contains, h0, h1, h2, h3, h4, h5] using h

/-- Glue an exact endpoint enclosure to any punctured positive enclosure. -/
theorem DyadicJet5Enclosure.contains_regular_of_nonneg {p : ℕ}
    {b : DyadicJet5Enclosure p} {y : ℝ} (hy : 0 ≤ y)
    (hzero : b.Contains regularQJet 0)
    (hpos : 0 < y → b.Contains qJet y) :
    b.Contains regularQJet y := by
  rcases hy.eq_or_lt with rfl | hy
  · exact hzero
  · exact DyadicJet5Enclosure.Contains.regular_of_pos (hpos hy) hy

#print axioms regularQJet_soundAt_zero
#print axioms regularQJet_soundAt_of_mem
#print axioms regularQJet_d0_eq_regular
#print axioms regularQJet_d1_eq_deriv
#print axioms analyticComponent_zero_eq_factorial_mul
#print axioms regularQJet_d2_zero
#print axioms regularQJet_d4_zero
#print axioms regularQJet_d3_zero
#print axioms regularQJet_d5_zero
#print axioms regularQJet_eq_qJet_at_pos
#print axioms DyadicJet5Enclosure.Contains.regular_of_pos
#print axioms DyadicJet5Enclosure.contains_regular_of_nonneg

end GeneralCK.Certificates.E8TAxisRegularGermJet

end


