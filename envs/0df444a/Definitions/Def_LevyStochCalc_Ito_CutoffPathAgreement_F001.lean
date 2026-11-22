-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CutoffPathAgreement_F001
-- name    : LevyStochCalc_Ito_CutoffPathAgreement_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:42:33.012735+00:00
-- url     : https://prove2.me/theorems/9636ef69-3c3f-4290-8d73-01add5413274
-- title:
--   Source declarations: LevyStochCalc.Ito.CutoffPathAgreement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.CutoffPathAgreement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_AtomJumpRelation_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F001
import Definitions.Def_LevyStochCalc_Probability_OpenExitTime_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Agreement of the continuous integrands with their cut-off, along a confined path

`JumpFormulaCutoff.integrands_cutoffFun₂_eq_of_mem` compares all five integrands of a state
function with those of its cut-off, and for the two jump integrands it needs the jump coefficient
itself bounded over the window, for every mark. That hypothesis is not available in general: the
jump coefficient is only square integrable against the intensity, so `x + γ(s, x, e)` leaves
every ball however large the cut-off radius.

The three *continuous* integrands need no such hypothesis. They are read at path values only, so
a path confined to a ball is enough. `integrands_cutoffFun₂_eq_of_boundedPath` records that,
adding the gradient, which the pathwise form of the jump part also reads at path values.

For the Brownian transfer the confinement has to come from a stopping time rather than an event,
so the same agreement is restated below `min (openExitTime …) T`: strictly below the exit time
the path is in the ball, and strictly below `T` the time cut-off is inactive. That is exactly the
hypothesis shape of `stochasticIntegralBrownian_congr_of_lt`.

## Main statements

* `integrands_cutoffFun₂_eq_of_boundedPath` — drift, diffusion, path value and gradient agree
  with their cut-off along a path confined to the ball, with no hypothesis on the jumps.
* `boundedPathSet_subset_le_openExitTime` — a path confined to the ball over the window has not
  exited by the end of it.
* `diffusionIntegrand_cutoffFun₂_eq_of_lt` — the agreement in the form the strict locality
  transfer consumes.
* `stochasticIntegralBrownian_cutoffFun₂_eq_of_le`, `multidimIntegral_cutoffFun₂_eq_of_mem` —
  the Brownian term of the cut-off and of the function itself agree almost surely on the event
  that the path has not left the ball, componentwise and in the vector form.
* `ae_continuousSide_cutoffFun₂_eq` — the whole continuous side, endpoints and drift integral
  included, agrees on that event.
* `norm_leftLimPathAt_le_of_boundedPath`,
  `gradient_cutoffFun₂_leftLim_eq_of_boundedPath` — a confined path has its left limits in the
  ball, where the gradient of the cut-off is that of the function.
* `cutoffFun₂_leftLim_eq_of_boundedPath`,
  `jumpIncrement_sub_eq_compensatorDrift_sub_of_boundedPath` — the cut-off changes the jump
  increment and the compensator-drift integrand by the same amount at the left limits.
* `jumpIncrement_cutoffFun₂_eq_of_boundedPath`,
  `ae_setIntegral_jumpIncrement_cutoffFun₂_eq`, `ae_setIntegral_jumpIncrement_sub_eq_zero` — the
  jump increment agrees with its cut-off at every atom of a window of finite intensity, because
  the state reached by the jump is a value of the path; hence the two integrals against the
  random measure agree and their difference integrates to zero.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.CutoffPath

open LevyStochCalc.Ito.JumpFormulaCutoff

universe u v

variable {Ω : Type u} {n d : ℕ} {E : Type v}

section BrownianTransfer

open MeasureTheory
open LevyStochCalc.Ito.JumpFormula (diffusionIntegrand)

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {E : Type v}

end BrownianTransfer

open LevyStochCalc.Ito.JumpSplitting (leftLimPathAt tendsto_nhdsLT_leftLimPathAt jumpSumLeftAt
  ae_exists_atomEnum_jump_eq_gamma)

/-- The left limit of a path confined to the ball over the window is in the ball. -/
theorem norm_leftLimPathAt_le_of_boundedPath {Xp : ℝ → Ω → Fin n → ℝ} {T : ℝ} {m : ℕ} {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m) {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) T)
    (hleft : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] θ) (𝓝 L)) :
    ‖leftLimPathAt Xp θ ω‖ ≤ (m : ℝ) :=
  norm_le_of_tendsto_nhdsLT hθ
    (tendsto_pi_nhds.mpr fun i => tendsto_nhdsLT_leftLimPathAt hleft i) hb
/-- The time window and the ball of a path confined to it sit inside the plateau of the cut-off
of radius `2m`. -/
theorem abs_le_of_mem_Ioc {T : ℝ} {m : ℕ} (hTm : T < 3 * (m : ℝ)) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc (0 : ℝ) T) : |θ| ≤ 3 * (2 * (m : ℝ)) / 2 := by
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  rw [hrad, abs_of_nonneg hθ.1.le]
  exact le_of_lt (lt_of_le_of_lt hθ.2 hTm)
/-- The gradient agrees with that of the cut-off at the left limits of a path confined to the
ball. -/
theorem gradient_cutoffFun₂_leftLim_eq_of_boundedPath {Xp : ℝ → Ω → Fin n → ℝ}
    (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ} (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m) {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) T)
    (hleft : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] θ) (𝓝 L)) :
    JumpFormula.gradient (cutoffFun₂ u (2 * (m : ℝ))) θ (leftLimPathAt Xp θ ω)
      = JumpFormula.gradient u θ (leftLimPathAt Xp θ ω) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  refine gradient_cutoffFun₂ u hR (abs_le_of_mem_Ioc hTm hθ) ?_
  rw [hrad]
  exact lt_of_le_of_lt (norm_leftLimPathAt_le_of_boundedPath hb hθ hleft) (by linarith)
/-- The cut-off agrees with the function at the left limits of a path confined to the ball. -/
theorem cutoffFun₂_leftLim_eq_of_boundedPath {Xp : ℝ → Ω → Fin n → ℝ}
    (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ} (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m) {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) T)
    (hleft : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] θ) (𝓝 L)) :
    cutoffFun₂ u (2 * (m : ℝ)) θ (leftLimPathAt Xp θ ω) = u θ (leftLimPathAt Xp θ ω) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  refine cutoffFun₂_eq hR (abs_le_of_mem_Ioc hTm hθ) ?_
  rw [hrad]
  exact le_trans (norm_leftLimPathAt_le_of_boundedPath hb hθ hleft) (by linarith)
/-- **The cut-off changes the jump increment and the compensator-drift integrand by the same
amount**, at the left limits of a path confined to the ball: both differences are the value of
the difference of the two state functions at the state reached by the jump, because the
difference and its gradient vanish at the left limit itself. -/
theorem jumpIncrement_sub_eq_compensatorDrift_sub_of_boundedPath {Xp : ℝ → Ω → Fin n → ℝ}
    {coeffs : Setting.JumpDiffusionCoeffs n d E} (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m) {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) T)
    (hleft : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] θ) (𝓝 L)) (e : E) :
    (cutoffFun₂ u (2 * (m : ℝ)) θ
          (leftLimPathAt Xp θ ω + coeffs.γ θ (leftLimPathAt Xp θ ω) e)
        - cutoffFun₂ u (2 * (m : ℝ)) θ (leftLimPathAt Xp θ ω))
        - (u θ (leftLimPathAt Xp θ ω + coeffs.γ θ (leftLimPathAt Xp θ ω) e)
          - u θ (leftLimPathAt Xp θ ω))
      = JumpFormula.compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ θ
            (leftLimPathAt Xp θ ω) e
        - JumpFormula.compensatorDriftIntegrand u coeffs.γ θ (leftLimPathAt Xp θ ω) e := by
  have hval := cutoffFun₂_leftLim_eq_of_boundedPath u hm hTm hb hθ hleft
  have hgrad := gradient_cutoffFun₂_leftLim_eq_of_boundedPath u hm hTm hb hθ hleft
  simp only [JumpFormula.compensatorDriftIntegrand, hval, hgrad]
  ring
/-- **The jump increment agrees with its cut-off at an atom of the window, along a path confined
to the ball.** The state reached by the jump is the value of the path at the arrival time, so the
cut-off is inactive at the shifted point as well as at the base point, and no bound on the jump
coefficient is needed. -/
theorem jumpIncrement_cutoffFun₂_eq_of_boundedPath {Xp : ℝ → Ω → Fin n → ℝ}
    {coeffs : Setting.JumpDiffusionCoeffs n d E} (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) T)
    (hleft : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] θ) (𝓝 L)) {e : E}
    (hjump : Xp θ ω = leftLimPathAt Xp θ ω + coeffs.γ θ (leftLimPathAt Xp θ ω) e) :
    cutoffFun₂ u (2 * (m : ℝ)) θ (leftLimPathAt Xp θ ω + coeffs.γ θ (leftLimPathAt Xp θ ω) e)
        - cutoffFun₂ u (2 * (m : ℝ)) θ (leftLimPathAt Xp θ ω)
      = u θ (leftLimPathAt Xp θ ω + coeffs.γ θ (leftLimPathAt Xp θ ω) e)
        - u θ (leftLimPathAt Xp θ ω) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  have hsabs : |θ| ≤ 3 * (2 * (m : ℝ)) / 2 := abs_le_of_mem_Ioc hTm hθ
  have hbase : ‖leftLimPathAt Xp θ ω‖ ≤ 3 * (2 * (m : ℝ)) / 2 := by
    rw [hrad]
    exact le_trans (norm_leftLimPathAt_le_of_boundedPath hb hθ hleft) (by linarith)
  have hshift : ‖leftLimPathAt Xp θ ω + coeffs.γ θ (leftLimPathAt Xp θ ω) e‖
      ≤ 3 * (2 * (m : ℝ)) / 2 := by
    rw [← hjump, hrad]
    exact le_trans (hb θ ⟨hθ.1.le, hθ.2⟩) (by linarith)
  rw [cutoffFun₂_eq hR hsabs hshift, cutoffFun₂_eq hR hsabs hbase]
section JumpTransfer

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- **The cut-off does not change the jump integral against the random measure, on the event the
path stays in the ball.** At finite activity that integral is the sum over the atoms of the
window, and at each atom both the base point and the state reached by the jump are values of the
path, hence in the ball. -/
theorem ae_setIntegral_jumpIncrement_cutoffFun₂_eq
    (coeffs : Setting.JumpDiffusionCoeffs n d E)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ)
    (A : Set E)
    (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ} (hm : 0 < m) (hTm : T < 3 * (m : ℝ))
    (hjump : ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ j : Fin K,
        Xp (θ j) ω
          = leftLimPathAt Xp (θ j) ω + coeffs.γ (θ j) (leftLimPathAt Xp (θ j) ω) (ε j))
    (hleft : ∀ᵐ ω ∂P, ∀ (t : ℝ) (i : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L)) :
    ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          (cutoffFun₂ u (2 * (m : ℝ)) q.1
              (leftLimPathAt Xp q.1 ω + coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2)
            - cutoffFun₂ u (2 * (m : ℝ)) q.1 (leftLimPathAt Xp q.1 ω)) ∂(N.N ω)
        = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
            (u q.1 (leftLimPathAt Xp q.1 ω + coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2)
              - u q.1 (leftLimPathAt Xp q.1 ω)) ∂(N.N ω) := by
  filter_upwards [hjump, hleft] with ω hω hlω hb
  obtain ⟨K, θ, ε, -, hmem, hg, hjump⟩ := hω
  rw [hg, hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact jumpIncrement_cutoffFun₂_eq_of_boundedPath u hm hTm hb (hmem j).1
    (fun i => hlω (θ j) i) (hjump j)
omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- **The difference of the cut-off's jump increment and the function's integrates to zero
against the random measure** on the event that the path stays in the ball: every atom
contributes zero. -/
theorem ae_setIntegral_jumpIncrement_sub_eq_zero
    (coeffs : Setting.JumpDiffusionCoeffs n d E)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ)
    (A : Set E)
    (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ} (hm : 0 < m) (hTm : T < 3 * (m : ℝ))
    (hjump : ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ j : Fin K,
        Xp (θ j) ω
          = leftLimPathAt Xp (θ j) ω + coeffs.γ (θ j) (leftLimPathAt Xp (θ j) ω) (ε j))
    (hleft : ∀ᵐ ω ∂P, ∀ (t : ℝ) (i : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L)) :
    ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          ((cutoffFun₂ u (2 * (m : ℝ)) q.1
                (leftLimPathAt Xp q.1 ω + coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2)
              - cutoffFun₂ u (2 * (m : ℝ)) q.1 (leftLimPathAt Xp q.1 ω))
            - (u q.1 (leftLimPathAt Xp q.1 ω + coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2)
              - u q.1 (leftLimPathAt Xp q.1 ω))) ∂(N.N ω) = 0 := by
  filter_upwards [hjump, hleft] with ω hω hlω hb
  obtain ⟨K, θ, ε, -, hmem, hg, hjump⟩ := hω
  rw [hg]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [jumpIncrement_cutoffFun₂_eq_of_boundedPath u hm hTm hb (hmem j).1
    (fun i => hlω (θ j) i) (hjump j)]
  exact sub_self _
end JumpTransfer

end LevyStochCalc.Ito.CutoffPath


