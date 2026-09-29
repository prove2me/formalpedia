-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionComplexDiscElementary
-- name    : CK_GeneralCK_ReflectionComplexDiscElementary
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:13:43.825877+00:00
-- url     : https://prove2.me/theorems/670d7250-664a-4b40-af05-dfa0e6b9d202
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionComplexDiscElementary` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionComplexDiscElementary` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionComplexDiscElementary` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionComplexDiscElementary (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionComplexDiscElementary.lean)

import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.MetricSpace.Lipschitz
import Definitions.Def_GeneralCK_complex_contact

-- ===== source module GeneralCK.ReflectionComplexDiscElementary =====
section

/-!
# Exact elementary constants for the small-bias complex contraction

This file isolates the algebraic and metric-space part of the proposed
complex-disc construction.  The analytic estimates on the complex entropy
remain premises here: once they give the bounds `1103 / 1000` and `7 / 5`,
the results below prove that multiplication by a parameter of norm at most
`7 / 10` maps the closed `4 / 5` disc to itself and has Lipschitz constant
`49 / 50`.

No complex logarithm, fixed-point existence, or holomorphic dependence is
asserted by this module.
-/

namespace GeneralCK.Reflection.ComplexDiscElementary

open Set




/-- Exact multiplication of the parameter and entropy sup-norm bounds. -/
theorem contactMap_norm_le
    {E : ℂ → ℂ} {τ c : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hE : ‖E c‖ ≤ (1103 / 1000 : ℝ)) :
    ‖contactMap E τ c‖ ≤ (7721 / 10000 : ℝ) := by
  rw [contactMap, Complex.norm_mul]
  calc
    ‖τ‖ * ‖E c‖ ≤ (7 / 10 : ℝ) * (1103 / 1000 : ℝ) :=
      mul_le_mul hτ hE (norm_nonneg _) (by norm_num)
    _ = (7721 / 10000 : ℝ) := by norm_num

/-- The image bound has strict room inside the chosen contact disc. -/
theorem contactMap_norm_lt_contactRadius
    {E : ℂ → ℂ} {τ c : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hE : ‖E c‖ ≤ (1103 / 1000 : ℝ)) :
    ‖contactMap E τ c‖ < (4 / 5 : ℝ) :=
  (contactMap_norm_le hτ hE).trans_lt (by norm_num)

/-- A uniform entropy bound on the contact disc makes the scaled map a
self-map of that closed disc. -/
theorem contactMap_mapsTo_closedBall
    {E : ℂ → ℂ} {τ : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hE : ∀ c ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ),
      ‖E c‖ ≤ (1103 / 1000 : ℝ)) :
    MapsTo (contactMap E τ) (Metric.closedBall 0 (4 / 5 : ℝ))
      (Metric.closedBall 0 (4 / 5 : ℝ)) := by
  intro c hc
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (contactMap_norm_lt_contactRadius hτ (hE c hc)).le

/-- In fact the same hypotheses put the image strictly inside the contact
disc, which supplies the margin needed by later analytic arguments. -/
theorem contactMap_mapsTo_ball
    {E : ℂ → ℂ} {τ : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hE : ∀ c ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ),
      ‖E c‖ ≤ (1103 / 1000 : ℝ)) :
    MapsTo (contactMap E τ) (Metric.closedBall 0 (4 / 5 : ℝ))
      (Metric.ball 0 (4 / 5 : ℝ)) := by
  intro c hc
  rw [Metric.mem_ball, dist_zero_right]
  exact contactMap_norm_lt_contactRadius hτ (hE c hc)

/-- Exact multiplication of the parameter and entropy difference bounds. -/
theorem contactMap_dist_le
    {E : ℂ → ℂ} {τ c d : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hE : dist (E c) (E d) ≤ (7 / 5 : ℝ) * dist c d) :
    dist (contactMap E τ c) (contactMap E τ d) ≤
      (49 / 50 : ℝ) * dist c d := by
  simp only [contactMap, dist_eq_norm] at hE ⊢
  rw [← mul_sub, Complex.norm_mul]
  calc
    ‖τ‖ * ‖E c - E d‖ ≤ (7 / 10 : ℝ) * ((7 / 5 : ℝ) * ‖c - d‖) :=
      mul_le_mul hτ hE (norm_nonneg _) (by norm_num)
    _ = (49 / 50 : ℝ) * ‖c - d‖ := by ring

/-- The entropy difference estimate composes to the advertised `49/50`
Lipschitz constant on the contact disc. -/
theorem contactMap_lipschitzOnWith
    {E : ℂ → ℂ} {τ : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hE : LipschitzOnWith (7 / 5 : NNReal) E
      (Metric.closedBall 0 (4 / 5 : ℝ))) :
    LipschitzOnWith (49 / 50 : NNReal) (contactMap E τ)
      (Metric.closedBall 0 (4 / 5 : ℝ)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro c hc d hd
  simpa using contactMap_dist_le hτ (hE.dist_le_mul c hc d hd)

/-- The exact Lipschitz constant is strictly below one. -/
theorem contractionFactor_lt_one : ((49 / 50 : NNReal) : ℝ) < 1 := by
  norm_num

/-- A `49/50`-Lipschitz self-map has at most one fixed point in the contact
disc.  Completeness and existence are deliberately separate from this
elementary uniqueness statement. -/
theorem fixedPoint_unique
    {f : ℂ → ℂ} {c d : ℂ}
    (hf : LipschitzOnWith (49 / 50 : NNReal) f
      (Metric.closedBall 0 (4 / 5 : ℝ)))
    (hc : c ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ))
    (hd : d ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ))
    (hfc : f c = c) (hfd : f d = d) : c = d := by
  by_contra hcd
  have hpos : 0 < dist c d := dist_pos.mpr hcd
  have hcontract := hf.dist_le_mul c hc d hd
  rw [hfc, hfd] at hcontract
  norm_num at hcontract
  nlinarith

/-- The complete elementary conclusion needed before applying a closed-ball
fixed-point theorem.  Its two premises are precisely the remaining analytic
entropy estimates. -/
theorem contactMap_contractionPackage
    {E : ℂ → ℂ} {τ : ℂ}
    (hτ : ‖τ‖ ≤ (7 / 10 : ℝ))
    (hBound : ∀ c ∈ Metric.closedBall (0 : ℂ) (4 / 5 : ℝ),
      ‖E c‖ ≤ (1103 / 1000 : ℝ))
    (hLip : LipschitzOnWith (7 / 5 : NNReal) E
      (Metric.closedBall 0 (4 / 5 : ℝ))) :
    MapsTo (contactMap E τ) (Metric.closedBall 0 (4 / 5 : ℝ))
        (Metric.closedBall 0 (4 / 5 : ℝ)) ∧
      LipschitzOnWith (49 / 50 : NNReal) (contactMap E τ)
        (Metric.closedBall 0 (4 / 5 : ℝ)) :=
  ⟨contactMap_mapsTo_closedBall hτ hBound,
    contactMap_lipschitzOnWith hτ hLip⟩

/-- The source-radius estimate: a numerator in the `21/50` disc divided by
a denominator of norm at least `3/5` lies in the parameter `7/10` disc. -/
theorem norm_div_le_parameterRadius
    {a e : ℂ} (ha : ‖a‖ ≤ (21 / 50 : ℝ))
    (he : (3 / 5 : ℝ) ≤ ‖e‖) :
    ‖a / e‖ ≤ (7 / 10 : ℝ) := by
  rw [Complex.norm_div, div_le_iff₀ (lt_of_lt_of_le (by norm_num) he)]
  nlinarith

end GeneralCK.Reflection.ComplexDiscElementary

end


