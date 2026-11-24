-- Prove2me | Definitions.Def_ReedGGN_Regulator_Supplement_PathLimits
-- name    : ReedGGN_Regulator_Supplement_PathLimits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:02:02.438973+00:00
-- url     : https://prove2.me/theorems/22eaf6c0-2a53-4cc4-afb0-d46b9e714c43
-- title:
--   §1.1 — Product J₁ convergence and full path laws
-- statement:
--   Let $D$ be the real càdlàg path space on $[0,\infty)$. This layer gives the product spaces $\mathbb R\times D^k$ and their convergence in law. Scalar J₁ convergence is reused from the published Kurtz–Protter time-change definition. For a product, each path coordinate has its own time changes, as required by Reed's maximum product metric.
--
--   $$X_N\Rightarrow X\quad\Longleftrightarrow\quad\text{there are copies of their full path laws converging almost surely in product J₁.}$$
--
--   The coupling is joint across all coordinates, and the cylinder sigma-field is the J₁ Borel sigma-field on càdlàg paths. Values at negative times are excluded from observations. This definition allows discontinuous limiting paths and supplies convergence for the fluid and diffusion results. It reuses the published path and time-change layers; it does not replace weak convergence by finite-dimensional convergence.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, §1.1, p.5; proof of Theorem 4.1, pp.13–14

import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_KurtzProtter91_Integrals_Skorohod

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

namespace ReedGGN.Regulator.Supplement

/-- Paths are restricted to nonnegative times when taking laws or limits. -/
abbrev RPath := ℝ≥0 → ℝ

/-- A real coordinate and k path coordinates. Their topology is the product of scalar J₁
 topologies, not vector J₁ (different coordinates may use different time changes). -/
abbrev State (k : ℕ) := ℝ × (Fin k → RPath)

/-- The càdlàg locus, with the trace of the cylinder sigma-field. -/
def Admissible {k : ℕ} (x : State k) : Prop :=
  ∀ i, KurtzProtter91.Integrals.IsCadlag (x.2 i)

/-- Maximum-product J₁ sequential convergence. The imported scalar convergence uses genuine
 continuous strictly increasing onto time changes with locally uniform time and value errors.
 This allows discontinuous limits and ignores all negative-time extensions. -/
def ProductJ1 {k : ℕ} (xs : ℕ → State k) (x : State k) : Prop :=
  Tendsto (fun n => (xs n).1) atTop (𝓝 x.1) ∧
  ∀ i, KurtzProtter91.Integrals.SkorohodTendsto (fun n => (xs n).2 i) (x.2 i)

/-- Weak convergence in ℝ × D^k with its maximum product J₁ topology, in Skorohod
 representation form. IdentDistrib includes a.e. measurability and equality of full path laws;
 this is not merely finite-dimensional convergence. A single coupling carries all coordinates. -/
def WeakJ1 {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {k : ℕ}
    (P : Measure Ω) (P' : Measure Ω') (X : ℕ → Ω → State k) (Y : Ω' → State k) : Prop :=
  (∀ n, ∀ᵐ ω ∂P, Admissible (X n ω)) ∧ (∀ᵐ ω ∂P', Admissible (Y ω)) ∧
  ∃ (S : Type) (_ : MeasurableSpace S) (R : Measure S)
      (U : ℕ → S → State k) (V : S → State k),
    IsProbabilityMeasure R ∧ (∀ n, IdentDistrib (U n) (X n) R P) ∧
    IdentDistrib V Y R P' ∧ ∀ᵐ ω ∂ R, ProductJ1 (fun n => U n ω) (V ω)

/-- Embed a scalar random variable, or one/two/three paths, without dummy random coordinates. -/
def scalar (q : ℝ) : State 0 := (q, Fin.elim0)
def one (x : RPath) : State 1 := (0, fun _ => x)
def two (x y : RPath) : State 2 := (0, ![x, y])
def three (q : ℝ) (x y z : RPath) : State 3 := (q, ![x, y, z])
def initialArrival (q : ℝ) (a : RPath) : State 1 := (q, fun _ => a)

/-- Nonnegative-time restriction of an existing published path. -/
def restrictPath (x : ℝ → ℝ) : RPath := fun t => x t

/-- Extend by the time-zero value. Negative values are never observed. -/
def extendPath (x : RPath) : ℝ → ℝ := fun t => x (Real.toNNReal t)

end ReedGGN.Regulator.Supplement


