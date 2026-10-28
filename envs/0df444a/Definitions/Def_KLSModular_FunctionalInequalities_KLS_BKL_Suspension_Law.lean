-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Law
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Law
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:06:49.948347+00:00
-- url     : https://prove2.me/theorems/3aa21ca1-97e4-4f56-86c5-3a01d28b38f3
-- title:
--   Joint law for the finite-copy suspension
-- statement:
--   `JointSpace N n` is $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Option}(\mathrm{Fin}\,N\times\mathrm{Fin}\,n))$, with `none` representing the auxiliary scalar coordinate and `some (i,j)` representing a coordinate of copy $i$. `sigma β` is $\sqrt{1+2/\beta^2}$, `copyStat f N x` is $N^{-1/2}\sum_i f(x_i)$, and `embed` maps $(x,s)$ to the vector whose `none` coordinate is $(F_N(x)+s)/\sigma$ and whose pair coordinates are those of the copies. `jointLaw` is the pushforward of the product of the $N$-fold measure product of $\mu$ and `laplaceMeasure β`; the included theorems show it is a probability measure when $f$ is measurable and the factors are probability measures, in particular for $\beta>0$. `CumulantBound d b` names the universal isotropic log-concave cumulant inequality, while `coordinateEquiv` identifies the joint index space with `Fin (N*n+1)`.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.BKL.Suspension.Basic
--   import FunctionalInequalities.Probability.Line.Laplace
--   import Mathlib.MeasureTheory.Constructions.Pi
--   import Mathlib.Analysis.InnerProductSpace.PiL2
--   import FunctionalInequalities.KLS.Isotropic
--   import FunctionalInequalities.Probability.LogConcave
--   import FunctionalInequalities.KLS.LogConcave.Density.Tilted
--   import Mathlib.MeasureTheory.Measure.Tilted
--   import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
--   import FunctionalInequalities.KLS.LogConcave.Transport
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   abbrev JointSpace (N n : ℕ) : Type := EuclideanSpace ℝ (Option (Fin N × Fin n))
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/BKL/Suspension/Basic`](https://prove2.me/theorems/aaa7527c-3ccd-45dd-876d-0915bc183526), [`Probability/Line/Laplace`](https://prove2.me/theorems/cba52f6e-b244-4595-8333-a1bd8a9b0069), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`KLS/LogConcave/Transport`](https://prove2.me/theorems/e2b06803-5a96-41cf-bc8d-6b89b02cb255).
--
--   Theorems in source order:
--
--   - [`logConcave_jointLaw_of_eq_tilted`](https://prove2.me/theorems/91e4e9b1-0b51-481d-b310-130f8697a3a8)
--   - [`cumulantBound_jointSpace`](https://prove2.me/theorems/88c575f1-15b2-4a92-828b-6fef20c27f09)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Law.lean) · `FunctionalInequalities.KLS.BKL.Suspension.Law` · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item P71. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Law.lean#L34-L250 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Law`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Law`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Line_Laplace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_LogConcave
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted
import Mathlib.MeasureTheory.Measure.Tilted
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Transport

noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability.Line
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace Suspension
/-- The joint space `ℝ^{Nn+1}`, indexed by `none` (the coordinate `S`) and pairs `(i, j)`. -/
abbrev JointSpace (N n : ℕ) : Type := EuclideanSpace ℝ (Option (Fin N × Fin n))
/-- The source's `σ_β = √(1 + 2/β²)`. -/
def sigma (β : ℝ) : ℝ := Real.sqrt (1 + 2 / β ^ 2)
/-- `F_N = N^{-1/2} Σ_i f(x_i)`. -/
def copyStat {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (N : ℕ)
    (x : Fin N → EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ i, f (x i)) / Real.sqrt N
/-- The map `(x₁, …, x_N, s) ↦ ((F_N(x) + s)/σ, x₁, …, x_N)` into the joint space. -/
def embed {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (σ : ℝ) (N : ℕ)
    (q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ) : JointSpace N n :=
  WithLp.toLp 2 fun o => Option.elim o ((copyStat f N q.1 + q.2) / σ) fun ij => q.1 ij.1 ij.2
/-- The joint law of `(S, X₁, …, X_N)`: the image of `μ^{⊗N} ⊗ η_β` under `embed`. -/
def jointLaw {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (β σ : ℝ) (N : ℕ) : Measure (JointSpace N n) :=
  ((Measure.pi fun _ : Fin N => μ).prod (laplaceMeasure β)).map (embed f σ N)
/-- `jointLaw μ f β σ N` is a probability measure when `μ` and `laplaceMeasure β` are and `f` is
measurable. -/
theorem isProbabilityMeasure_jointLaw {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {β : ℝ}
    [IsProbabilityMeasure (laplaceMeasure β)] (σ : ℝ) (N : ℕ) :
    IsProbabilityMeasure (jointLaw μ f β σ N) := by
    have hg :
        Measurable
          (fun q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ =>
            fun o : Option (Fin N × Fin n) =>
              o.elim
                ((copyStat f N q.1 + q.2) / σ)
                (fun ij => (q.1 ij.1).ofLp ij.2)) := by
      rw [measurable_pi_iff]
      intro o
      cases o with
      | none =>
          unfold copyStat
          measurability
      | some ij =>
          measurability
    have h_embed : Measurable (embed f σ N) := by
      unfold embed
      exact (WithLp.measurable_toLp 2 _).comp hg
    refine ⟨?_⟩
    rw [jointLaw,
      Measure.map_apply_of_aemeasurable h_embed.aemeasurable MeasurableSet.univ]
    simp
/-- The joint law is a probability measure for every rate `β > 0` (the Laplace law's mass is
`isProbabilityMeasure_laplaceMeasure`). -/
theorem isProbabilityMeasure_jointLaw_of_pos {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f) {β : ℝ}
    (hβ : 0 < β) (σ : ℝ) (N : ℕ) : IsProbabilityMeasure (jointLaw μ f β σ N) :=
  haveI := isProbabilityMeasure_laplaceMeasure hβ
  isProbabilityMeasure_jointLaw μ hf σ N
open scoped RealInnerProductSpace in
/-- The hypothesis of BKL Proposition 7.1: `R^ν_{d+1} ≤ b Id` for every isotropic log-concave
probability measure `ν` in every dimension, i.e. `Σ_J κ^ν_{d+1}(u, e_{J 1}, …, e_{J d})² ≤ b |u|²`
in the standard basis of `ℝ^m`. This names the hypothesis; it asserts nothing. -/
def CumulantBound (d : ℕ) (b : ℝ) : Prop :=
  ∀ (m : ℕ) (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin m))),
    KLS.Isotropic ν → _root_.FunctionalInequalities.KLS.LogConcave ν →
      ∀ u : EuclideanSpace ℝ (Fin m),
      ∑ J : Fin d → Fin m, Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin m))) (d + 1)
        (Fin.cons u fun k => EuclideanSpace.basisFun (Fin m) ℝ (J k)) ^ 2 ≤ b * ‖u‖ ^ 2
/-- The index set of the joint space has `N n + 1` elements. -/
theorem card_option_prod (N n : ℕ) : Fintype.card (Option (Fin N × Fin n)) = N * n + 1 := by
  simp
/-- The coordinate reindexing of the joint space onto `ℝ^{Nn+1}`. -/
def coordinateEquiv (N n : ℕ) : JointSpace N n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (N * n + 1)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFinOfCardEq (card_option_prod N n))
end Suspension
end LogConcave
end KLS
end FunctionalInequalities


