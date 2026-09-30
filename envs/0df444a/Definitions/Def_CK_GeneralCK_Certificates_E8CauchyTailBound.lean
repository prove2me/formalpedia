-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8CauchyTailBound
-- name    : CK_GeneralCK_Certificates_E8CauchyTailBound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:59:08.494982+00:00
-- url     : https://prove2.me/theorems/c73afb31-41ce-46ad-8393-260c00b406f7
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8CauchyTailBound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8CauchyTailBound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8CauchyTailBound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8CauchyTailBound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8CauchyTailBound.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8AnalyticTaylor17
import Definitions.Def_CK_GeneralCK_Certificates_E8OriginRemainder
import Mathlib.Analysis.Complex.Liouville

-- ===== source module GeneralCK.Certificates.E8CauchyTailBound =====
section

/-!
# A Cauchy handoff for the E8 origin remainder

The retained origin checker assumes a uniform bound for the seventeenth
derivative of the inverse germ on the real interval reached by the four
arguments of `Delta`.  This file derives that kind of bound from ordinary,
noncircular complex-disc data: holomorphy on one larger disc and a uniform
bound for the function there.

Thus a later numerical certificate need only establish a domain of the
inverse branch and a sup-norm bound for `qGerm`; it need not assume any Taylor
coefficient or Taylor remainder estimate.
-/

namespace GeneralCK.Certificates.E8CauchyTailBound

open Metric Set
open E8AnalyticGerm
open E8OriginRemainder

/-- Cauchy's estimate at every point of an inner closed disc, obtained from
one holomorphic outer disc.  The positive clearance `rho` is the radius of
the Cauchy circle placed around each inner point. -/
theorem norm_iteratedDeriv_le_on_inner_closedBall
    {f : ℂ → ℂ} {outer inner rho C : ℝ} (n : ℕ)
    (hrho : 0 < rho) (hfit : inner + rho ≤ outer)
    (hf : DiffContOnCl ℂ f (ball 0 outer))
    (hC : ∀ z ∈ closedBall (0 : ℂ) outer, ‖f z‖ ≤ C) :
    ∀ y ∈ closedBall (0 : ℂ) inner,
      ‖iteratedDeriv n f y‖ ≤ n.factorial * C / rho ^ n := by
  intro y hy
  have hy_norm : ‖y‖ ≤ inner := by
    simpa [mem_closedBall, dist_zero_right] using hy
  have hcenters : rho + dist y 0 ≤ outer := by
    simpa [dist_zero_right, add_comm] using add_le_add_left hy_norm rho |>.trans hfit
  have hlocal : DiffContOnCl ℂ f (ball y rho) :=
    hf.mono (ball_subset_ball' hcenters)
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hrho hlocal
  intro z hz
  apply hC z
  exact (sphere_subset_closedBall.trans
    (closedBall_subset_closedBall' hcenters)) hz

/-- Coefficient form of Cauchy's estimate.  Coefficients use the same
`iteratedDeriv / n!` convention as the E8 inverse-jet checker. -/
theorem norm_iteratedDeriv_div_factorial_le
    {f : ℂ → ℂ} {R C : ℝ} (n : ℕ)
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball 0 R))
    (hC : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C) :
    ‖iteratedDeriv n f 0 / (n.factorial : ℂ)‖ ≤ C / R ^ n := by
  have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    n hR hf hC
  have hfac : (0 : ℝ) < n.factorial := by positivity
  rw [norm_div]
  calc
    ‖iteratedDeriv n f 0‖ / ‖(n.factorial : ℂ)‖ ≤
        (n.factorial * C / R ^ n) / (n.factorial : ℝ) := by
      simpa using (div_le_div_of_nonneg_right hd hfac.le)
    _ = C / R ^ n := by
      field_simp

/-- Direct Cauchy bound for the concrete analytic E8 Taylor coefficient. -/
theorem norm_qTaylorCoeff_le_of_disc_bound
    {R C : ℝ} (n : ℕ) (hR : 0 < R)
    (hf : DiffContOnCl ℂ qGerm (ball 0 R))
    (hC : ∀ z ∈ sphere (0 : ℂ) R, ‖qGerm z‖ ≤ C) :
    ‖qTaylorCoeff n‖ ≤ C / R ^ n := by
  simpa [qTaylorCoeff] using
    norm_iteratedDeriv_div_factorial_le n hR hf hC

/-- Order-18 specialization matching the remainder multiplier in
`E8AnalyticTaylor17.exists_qGerm_degree17_remainder`: the omitted coefficient
is bounded directly by outer-disc data. -/
theorem norm_qTaylorCoeff_eighteen_le_of_disc_bound
    {R C : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ qGerm (ball 0 R))
    (hC : ∀ z ∈ sphere (0 : ℂ) R, ‖qGerm z‖ ≤ C) :
    ‖qTaylorCoeff 18‖ ≤ C / R ^ 18 :=
  norm_qTaylorCoeff_le_of_disc_bound 18 hR hf hC

/-- The exact source-checker obligation follows from an explicit complex
disc certificate.  The inner radius `4/25` covers every inverse-germ argument
used when `s+t ≤ 2/25`: the largest argument is `2s+t ≤ 4/25`.

The final premise is only scalar arithmetic relating the certified disc
bound to the checker's conservative constant `2.9e14`; it contains no
derivative, coefficient, or remainder assertion. -/
theorem qGerm_seventeenth_derivative_le_source_bound
    {outer rho C : ℝ} (hrho : 0 < rho)
    (hfit : (4 / 25 : ℝ) + rho ≤ outer)
    (hf : DiffContOnCl ℂ qGerm (ball 0 outer))
    (hC : ∀ z ∈ closedBall (0 : ℂ) outer, ‖qGerm z‖ ≤ C)
    (harith : (Nat.factorial 17) * C / rho ^ 17 ≤ (q17AbsBound : ℝ)) :
    ∀ y ∈ closedBall (0 : ℂ) (4 / 25 : ℝ),
      ‖iteratedDeriv 17 qGerm y‖ ≤ (q17AbsBound : ℝ) := by
  intro y hy
  exact (norm_iteratedDeriv_le_on_inner_closedBall 17 hrho hfit hf hC y hy).trans harith

/-- The same handoff with the checker's decimal expanded, making the exact
certified target visible without unfolding any source-data definition. -/
theorem qGerm_seventeenth_derivative_le_290e12
    {outer rho C : ℝ} (hrho : 0 < rho)
    (hfit : (4 / 25 : ℝ) + rho ≤ outer)
    (hf : DiffContOnCl ℂ qGerm (ball 0 outer))
    (hC : ∀ z ∈ closedBall (0 : ℂ) outer, ‖qGerm z‖ ≤ C)
    (harith : (Nat.factorial 17) * C / rho ^ 17 ≤ 290000000000000) :
    ∀ y ∈ closedBall (0 : ℂ) (4 / 25 : ℝ),
      ‖iteratedDeriv 17 qGerm y‖ ≤ 290000000000000 := by
  simpa [q17AbsBound] using
    qGerm_seventeenth_derivative_le_source_bound hrho hfit hf hC harith

end GeneralCK.Certificates.E8CauchyTailBound

end


