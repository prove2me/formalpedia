-- Prove2me | Definitions.Def_ThinShellSampling_Supplement_restartLaw
-- name    : ThinShellSampling_Supplement_restartLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:36:20.37503+00:00
-- url     : https://prove2.me/theorems/7d041adc-aeb7-49ec-a293-84fd615e2b2f
-- title:
--   Restart-until-success algorithm on top of an attempt program: output law and expected total queries
-- statement:
--   An **attempt** is a randomized oracle program $p$ that either returns a value $a$ or declares failure. The **restart-until-success algorithm** built on $p$ runs independent copies of $p$, the $j$-th one on its own independent sequence $\omega_j$ of $\mathrm{Uniform}[0,1]$ random numbers, one after another, until the first attempt that does not declare failure; it outputs that attempt's value. Writing $J$ for the index of that attempt and $c(\omega_i)$ for the number of oracle queries of attempt $i$, the total cost is
--
--   $$
--   C_{\mathrm{restart}}=\sum_{i=0}^{J}c(\omega_i),
--   $$
--
--   and $C_{\mathrm{restart}}=\infty$ if every attempt fails. The **output law** is the push-forward of the product law of $(\omega_0,\omega_1,\dots)$ under the output map, and the **expected total cost** is $\mathbb E[C_{\mathrm{restart}}]\in[0,\infty]$. The run **halts** when some attempt does not declare failure and that attempt terminates. The **restart probability** of the algorithm is the probability that a single attempt declares failure.
--
--   This is the wrapper that Theorems 1.1, 1.5 and 1.6 put around $\mathsf{PS}_{\mathrm{unif}}$, Algorithm 5.5 and $\mathsf{PS}_{\exp}$: "restart from scratch with a new $x_0\sim\pi_0$".
--
--   **Formalization Note** Programs of the published oracle model `Prog` are well-founded trees, so an unbounded restart loop is not itself a program; the wrapper is defined on top of an attempt `p : Prog n (Option α)` (`none` = failure). The number of restarts is never capped. If the output map is not a.e.-measurable the law is the zero measure, whose Rényi divergence to any probability measure is $\infty$.
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1, p.2 (PDF p.4) ("restart from scratch with a new x₀ ∼ π₀"); §2.2.1, p.18 (PDF p.20) ("Restart-until-success"); Algorithm 5.5, p.32 (PDF p.34); proof of Theorem 1.5, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_ThinShellSampling_Prog

set_option autoImplicit false

namespace ThinShellSampling.Supplement

open MeasureTheory
open scoped ENNReal

/-- The uniform stream law `streamMeasure` is a probability measure (structural lemma). -/
instance isProbabilityMeasure_streamMeasure :
    IsProbabilityMeasure (ThinShellSampling.streamMeasure) := by
  unfold ThinShellSampling.streamMeasure
  infer_instance

/-- **The law of the random input of a restart run**: a sequence `ws = (ws 0, ws 1, …)` of independent
uniform streams, attempt `j` reading the stream `ws j`. -/
noncomputable def restartMeasure : Measure (ℕ → ℕ → unitInterval) :=
  Measure.infinitePi (fun _ : ℕ => ThinShellSampling.streamMeasure)

/-- An attempt `p` **halts and declares failure** on the stream `ω`: its run terminates with the
value `none`. -/
def Failed {n : ℕ} {α : Type} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (p : Prog n (Option α))
    (ω : ℕ → unitInterval) : Prop :=
  ∃ c : ℕ, ThinShellSampling.result V p ω = some (none, c)

open Classical in
/-- The index of the **first attempt that does not halt with failure**; `none` if every attempt
halts with failure. -/
noncomputable def firstNonFail {n : ℕ} {α : Type} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
    (p : Prog n (Option α)) (ws : ℕ → ℕ → unitInterval) : Option ℕ :=
  if h : ∃ j, ¬ Failed V p (ws j) then some (Nat.find h) else none

/-- The **restart run halts**: some attempt does not halt with failure, and the first such attempt
halts (so it returns `some a`). Attempts are run one after another; a non-halting attempt blocks
every later one. -/
def RestartHalts {n : ℕ} {α : Type} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
    (p : Prog n (Option α)) (ws : ℕ → ℕ → unitInterval) : Prop :=
  match firstNonFail V p ws with
  | some j => ThinShellSampling.Halts V p (ws j)
  | none => False

/-- The **output of the restart run**: the value `a` returned by the first successful attempt; the
default `d` if the run does not halt. -/
noncomputable def restartOutput {n : ℕ} {α : Type} (d : α)
    (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) (p : Prog n (Option α))
    (ws : ℕ → ℕ → unitInterval) : α :=
  match firstNonFail V p ws with
  | some j => (ThinShellSampling.output none V p (ws j)).getD d
  | none => d

/-- The **total number of oracle queries of the restart run**: the sum of the query counts of the
attempts `0, …, J` with `J` the first attempt that does not fail; `⊤` if every attempt fails (or
attempt `J` does not halt). -/
noncomputable def restartQueries {n : ℕ} {α : Type} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
    (p : Prog n (Option α)) (ws : ℕ → ℕ → unitInterval) : ℕ∞ :=
  match firstNonFail V p ws with
  | some j => ∑ i ∈ Finset.range (j + 1), ThinShellSampling.queryCount V p (ws i)
  | none => ⊤

/-- **The output law of the restart-until-success algorithm** built on the attempt `p`
(push-forward of `restartMeasure` under the output map, default `0`).

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with
Sesteric Complexity from a Cold Start*, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1,
p.2 (PDF p.4): "If this rejection loop exceeds τ trials, restart from scratch with a new
`x₀ ∼ π₀^X`"; §2.2.1, p.18 (PDF p.20): "A practical restart-until-success strategy repeats
independent attempts until `S` occurs"; Algorithm 5.5, p.32 (PDF p.34): "If a cap is hit, return to
Step 1 and start an independent annealing attempt".

**Formalization Note.** A `Prog` is a well-founded tree (every run path is finite), so an unbounded
restart loop is not a `Prog`. The restart algorithm is therefore defined on top of an attempt
`p : Prog n (Option α)` (`none` = failure declared): attempt `j` runs on the `j`-th of a sequence of
independent uniform streams, the run stops at the first attempt that does not declare failure, its
output is that attempt's value, and its cost is the sum of the query counts of all attempts made.
The number of restarts is never capped. If the output map is not a.e.-measurable, `Measure.map`
gives the zero measure, whose Rényi divergence to a probability measure is `∞` (`renyi`). -/
noncomputable def restartLaw {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
    (p : Prog n (Option (EuclideanSpace ℝ (Fin n)))) : Measure (EuclideanSpace ℝ (Fin n)) :=
  restartMeasure.map (restartOutput 0 V p)

/-- **Expected total number of oracle queries** `E[#queries] ∈ [0, ∞]` of the restart run. -/
noncomputable def restartExpQueries {n : ℕ} {α : Type} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
    (p : Prog n (Option α)) : ℝ≥0∞ :=
  ∫⁻ ws, (restartQueries V p ws : ℝ≥0∞) ∂restartMeasure

end ThinShellSampling.Supplement


