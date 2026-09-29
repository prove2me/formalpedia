-- Prove2me | Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem
-- name    : auto_M04_6e37b463_SolvesMartingaleProblem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T18:48:36.933792+00:00
-- url     : https://prove2.me/theorems/b6dc563f-721a-492a-b3f5-152ba87812e8
-- title:
--   SolvesMartingaleProblem
-- statement:
--   A jointly measurable process with initial law μ satisfies all finite-history compensated moment identities for pairs (f,g) in A. The histories are finite, possibly empty, with times at most the increment start, and bounded Borel test functions. For the theorem, P is a probability measure and A consists of bounded Borel pairs.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986; Chapter 4, Section 4, Theorem 4.1, printed p.182 (PDF p.191); equation (3.4), printed p.174 (PDF p.183); equation (4.2), printed p.183 (PDF p.192).

import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

namespace EthierKurtz

variable {E Ω Ω' : Type*} [MeasurableSpace E]
  [MeasurableSpace Ω] [MeasurableSpace Ω']

def SolvesMartingaleProblem
    (A : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (μ : Measure E) (P : Measure Ω) (X : ℝ≥0 → Ω → E) : Prop :=
  Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2) ∧
  Measure.map (X 0) P = μ ∧
  ∀ (fg : UniformBoundedFunction E × UniformBoundedFunction E), fg ∈ A →
    ∀ (s t : ℝ≥0), s ≤ t → ∀ (n : ℕ) (r : Fin n → ℝ≥0),
      (∀ i, r i ≤ s) → ∀ h : Fin n → UniformBoundedFunction E,
      (∀ i, Measurable (h i)) →
      (∫ ω, (fg.1 (X t ω) - fg.1 (X s ω) -
        ∫ u in (s : ℝ)..(t : ℝ), fg.2 (X u.toNNReal ω)) *
        ∏ i, h i (X (r i) ω) ∂P) = 0

end EthierKurtz


