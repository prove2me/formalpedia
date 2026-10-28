-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_Multidim
-- name    : KLSModular_LevyStochCalc_Brownian_Multidim
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:45:47.944998+00:00
-- url     : https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3
-- title:
--   Finite-dimensional Brownian motion structure
-- statement:
--   Vendored from LevyStochCalc, repository https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `MultidimBrownianMotion P d` packages a Fin d-indexed family of one-dimensional Brownian motions on the same probability space, with mutually independent component processes and almost-sure continuity of the joint path t ↦ (W i t ω)ᵢ. The auxiliary definition `project_BM` lifts a one-dimensional Brownian motion on (Ω₀, P₀) to the product space Fin d → Ω₀ by evaluating at one coordinate, with the product probability measure.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.Existence
--   import LevyStochCalc.Brownian.Martingale
--   import LevyStochCalc.Probability.Transport
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure MultidimBrownianMotion (P : Measure Ω) [IsProbabilityMeasure P]
--       (d : ℕ) where
--     /-- The component-wise Brownian motions. -/
--     W : Fin d → LevyStochCalc.Brownian.BrownianMotion P
--     /-- The components are mutually independent — each component, viewed as a
--     random variable into the path space `ℝ → ℝ` (with the product measurable
--     structure), is jointly independent across `i : Fin d`. -/
--     components_independent :
--       ProbabilityTheory.iIndepFun
--         (fun (i : Fin d) (ω : Ω) (t : ℝ) => (W i).W t ω) P
--     /-- The joint d-dim
--     path `t ↦ (W i ω t)_{i ∈ Fin d}` is continuous a.s. P. Follows from
--     the component-wise `continuous_paths` + the finite-intersection-of-
--     a.s.-sets being a.s., plus `continuous_pi_iff`: a `Fin d → ℝ`-valued
--     map is continuous iff each component is. Previously this was implicit
--     (a downstream caller had to derive it from `(W i).continuous_paths`
--     for each i); now made explicit per Karatzas-Shreve §2.5's definition
--     of multidim BM as "vector-valued process with continuous paths". -/
--     joint_continuous_paths :
--       ∀ᵐ ω ∂P, Continuous (fun (t : ℝ) (i : Fin d) => (W i).W t ω)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/Existence`](https://prove2.me/theorems/10f8be28-ef23-4221-869d-2a746f8fe042), [`LevyStochCalc/Brownian/Martingale`](https://prove2.me/theorems/686b7353-6b84-44dd-a71a-de96639579a2), [`LevyStochCalc/Probability/Transport`](https://prove2.me/theorems/d3f6d68e-2e8d-4a0b-a790-2ab66ed28419).
--
--   Theorems in source order:
--
--   - [`MultidimBrownianMotion.exists`](https://prove2.me/theorems/7d8b284a-c9b3-4927-9d3c-74473785d55c)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/Multidim.lean) · `LevyStochCalc.Brownian.Multidim` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/Multidim.lean#L47-L166 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.Multidim`, definition bundle `KLSModular_LevyStochCalc_Brownian_Multidim`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Existence
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Martingale
import Definitions.Def_KLSModular_LevyStochCalc_Probability_Transport

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/Multidim.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace LevyStochCalc
namespace Brownian
namespace Multidim
universe u
section Definition
variable {Ω : Type u} [MeasurableSpace Ω]
/-- A `d`-dimensional Brownian motion: a `Fin d`-tuple of independent
1-dimensional Brownian motions on the same probability space. -/
structure MultidimBrownianMotion (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) where
  /-- The component-wise Brownian motions. -/
  W : Fin d → LevyStochCalc.Brownian.BrownianMotion P
  /-- The components are mutually independent — each component, viewed as a
  random variable into the path space `ℝ → ℝ` (with the product measurable
  structure), is jointly independent across `i : Fin d`. -/
  components_independent :
    ProbabilityTheory.iIndepFun
      (fun (i : Fin d) (ω : Ω) (t : ℝ) => (W i).W t ω) P
  /-- The joint d-dim
  path `t ↦ (W i ω t)_{i ∈ Fin d}` is continuous a.s. P. Follows from
  the component-wise `continuous_paths` + the finite-intersection-of-
  a.s.-sets being a.s., plus `continuous_pi_iff`: a `Fin d → ℝ`-valued
  map is continuous iff each component is. Previously this was implicit
  (a downstream caller had to derive it from `(W i).continuous_paths`
  for each i); now made explicit per Karatzas-Shreve §2.5's definition
  of multidim BM as "vector-valued process with continuous paths". -/
  joint_continuous_paths :
    ∀ᵐ ω ∂P, Continuous (fun (t : ℝ) (i : Fin d) => (W i).W t ω)
end Definition
section MeasurePreserving
variable {Ω : Type u} [MeasurableSpace Ω]
/-- Lift a 1-dimensional Brownian motion `W₀` on `(Ω₀, P₀)` to a 1-D BM on the
product space `(Fin d → Ω₀, Measure.pi)` along the `i`-th coordinate. -/
 noncomputable def project_BM
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    (W₀ : LevyStochCalc.Brownian.BrownianMotion P₀)
    (d : ℕ) (i : Fin d) :
    @LevyStochCalc.Brownian.BrownianMotion (Fin d → Ω₀) MeasurableSpace.pi
      (MeasureTheory.Measure.pi (fun _ => P₀))
      (by infer_instance) where
  W := fun t (ω : Fin d → Ω₀) => W₀.W t (ω i)
  measurable_eval := fun t =>
    (W₀.measurable_eval t).comp (measurable_pi_apply i)
  joint_measurable := by
    -- Joint measurability inherits from 1D BM's joint measurability via
    -- the measurable evaluation map at coordinate i.
    have h₀ := W₀.joint_measurable
    -- Function.uncurry (fun t ω => W₀.W t (ω i)) = (fun p => W₀.W p.1 (p.2 i))
    -- = h₀ ∘ (fun p => (p.1, p.2 i))
    have h_eval_meas : Measurable (fun (p : ℝ × (Fin d → Ω₀)) => (p.1, p.2 i)) := by
      refine Measurable.prodMk (measurable_fst) ?_
      exact (measurable_pi_apply i).comp measurable_snd
    exact h₀.comp h_eval_meas
  initial_zero := by
    -- W₀.initial_zero : ∀ᵐ ω₀ ∂P₀, W₀.W 0 ω₀ = 0; lift via
    --   measure-preserving eval i.
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    exact mp.quasiMeasurePreserving.ae W₀.initial_zero
  increment_gaussian := by
    intro s t hs hst
    -- Pushforward through eval_i preserves the Gaussian increment law.
    have h_eval : (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)).map
        (Function.eval i) = P₀ :=
      (MeasureTheory.measurePreserving_eval (fun _ : Fin d => P₀) i).map_eq
    have h_inc := W₀.increment_gaussian hs hst
    rw [show (fun ω : Fin d → Ω₀ => W₀.W t (ω i) - W₀.W s (ω i))
        = (W₀.W t - W₀.W s) ∘ Function.eval i from rfl,
      ← MeasureTheory.Measure.map_map
        ((W₀.measurable_eval t).sub (W₀.measurable_eval s))
        (measurable_pi_apply i),
      h_eval]
    exact h_inc
  continuous_paths := by
    -- W₀.continuous_paths lifts via measure-preserving eval i.
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    exact mp.quasiMeasurePreserving.ae W₀.continuous_paths
  negative_zero := by
    -- W₀.negative_zero lifts via measure-preserving eval i.
    intro s hs
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    exact mp.quasiMeasurePreserving.ae (W₀.negative_zero s hs)
  joint_increment_independent := by
    -- W₀.joint_increment_independent + `indep_comap_of_measurePreserving`.
    intro s t hs hst
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    have h_inc_comap :
        MeasurableSpace.comap
          (fun (ω : Fin d → Ω₀) => W₀.W t (ω i) - W₀.W s (ω i)) inferInstance
        = (MeasurableSpace.comap (fun ω => W₀.W t ω - W₀.W s ω) inferInstance).comap
            (Function.eval i) := by
      rw [MeasurableSpace.comap_comp]
      rfl
    have h_past_comap :
        (⨆ j ∈ Set.Iic s, MeasurableSpace.comap
          (fun (ω : Fin d → Ω₀) => W₀.W j (ω i)) inferInstance)
        = (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W₀.W j) inferInstance).comap
            (Function.eval i) := by
      rw [MeasurableSpace.comap_iSup]
      refine iSup_congr (fun j => ?_)
      rw [MeasurableSpace.comap_iSup]
      refine iSup_congr (fun _ => ?_)
      rw [MeasurableSpace.comap_comp]
      rfl
    rw [h_past_comap, h_inc_comap]
    apply Probability.indep_comap_of_measurePreserving mp
    · -- past σ-algebra ≤ ambient
      refine iSup₂_le ?_
      intro j _ u hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact (W₀.measurable_eval j) hv
    · -- increment σ-algebra ≤ ambient
      intro u hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact ((W₀.measurable_eval t).sub (W₀.measurable_eval s)) hv
    · exact W₀.joint_increment_independent hs hst
end MeasurePreserving
end Multidim
end Brownian
end LevyStochCalc


