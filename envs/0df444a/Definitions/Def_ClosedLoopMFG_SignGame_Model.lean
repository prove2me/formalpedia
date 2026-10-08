-- Prove2me | Definitions.Def_ClosedLoopMFG_SignGame_Model
-- name    : ClosedLoopMFG_SignGame_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T05:21:17.804699+00:00
-- url     : https://prove2.me/theorems/3cfd8687-f6f0-4a5f-9b17-f085f52036b9
-- title:
--   P(R^d), path and flow spaces, empirical measures and F-Brownian motion (Section 2)
-- statement:
--   This file fixes the spaces on which the closed-loop $n$-player games of Lacker's paper live.
--
--   Let $d\ge 0$ and a time horizon $T>0$. Write $\mathbb R^d$ for Euclidean space and
--
--   1. $\mathcal P(\mathbb R^d)$ for the Borel probability measures on $\mathbb R^d$, with the topology of weak convergence and the Borel $\sigma$-field of that topology;
--   2. $\mathcal C^d = C([0,T];\mathbb R^d)$ for the continuous paths, and $C([0,T];\mathcal P(\mathbb R^d))$ for the continuous measure flows, both with the topology of uniform convergence and its Borel $\sigma$-field;
--   3. $C([0,T];\mathbb R)$ for the real-valued paths, likewise.
--
--   For $n\ge1$ points $x_1,\dots,x_n\in\mathbb R^d$ the **empirical measure** is
--
--   $$
--   \frac1n\sum_{k=1}^n \delta_{x_k}\in\mathcal P(\mathbb R^d).
--   $$
--
--   A process $W=(W_t)_{t\ge0}$ on a filtered probability space $(\Omega,\mathcal F,\mathbb F,\mathbb P)$ is an **$\mathbb F$-Brownian motion** if it is a standard $d$-dimensional Brownian motion (continuous paths, independent standard real Brownian coordinates), $W_t$ is $\mathcal F_t$-measurable for every $t$, and the increments $(W_r-W_t)_{r\ge t}$ are independent of $\mathcal F_t$. A filtration is **complete** when $\mathcal F_0$ contains every $\mathbb P$-null set.
--
--   These objects are shared by all statements of the series.
--
--   **Formalization Note** $\mathcal P(\mathbb R^d)$, $\mathcal C^d$, the flow space and $C([0,T];\mathbb R)$ are type synonyms carrying the Borel $\sigma$-field (not Mathlib's Giry $\sigma$-field). On maps from the compact interval $[0,T]$ into a metrizable space, the compact-open topology is the topology of uniform convergence for every compatible metric, so it is the paper's sup-metric topology. The empirical measure is written as the push-forward of the uniform distribution on $\{1,\dots,n\}$ (in Lean, `Fin n`), which is $\frac1n\sum_k\delta_{x_k}$. Coefficients take real times; a path is read at a real time $s$ at the projection of $s$ onto $[0,T]$. Brownian motions are indexed by $[0,\infty)$; every statement of the series concerns laws on $[0,T]$, so nothing changes.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, pp. 5–7, Section 2 and Section 2.1

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_ClosedLoopMFG_Converse_Model
import Definitions.Def_ClosedLoopMFG_Limit_Model
import Definitions.Def_ClosedLoopMFG_MarkovNash_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.SignGame

/-- `P(ℝ^d)`: probability measures on `ℝ^d` with the topology of weak convergence and its
Borel σ-field (Lacker, arXiv:1808.02745v1, p. 5). A type synonym, so that the σ-field is
`borel` rather than Mathlib's Giry σ-field. -/
def PR (d : ℕ) : Type := ProbabilityMeasure (EthierKurtz.SDEState d)

instance instTopologicalSpacePR (d : ℕ) : TopologicalSpace (PR d) :=
  inferInstanceAs (TopologicalSpace (ProbabilityMeasure (EthierKurtz.SDEState d)))

instance instMeasurableSpacePR (d : ℕ) : MeasurableSpace (PR d) := borel _

instance instBorelSpacePR (d : ℕ) : BorelSpace (PR d) := ⟨rfl⟩

/-- The underlying measure of an element of `P(ℝ^d)`. -/
def PR.meas {d : ℕ} (m : PR d) : Measure (EthierKurtz.SDEState d) :=
  ProbabilityMeasure.toMeasure m

instance PR.isProbabilityMeasure_meas {d : ℕ} (m : PR d) : IsProbabilityMeasure m.meas :=
  ProbabilityMeasure.instIsProbabilityMeasureToMeasure (μ := m)

instance instTopologicalSpacePath (d : ℕ) (T : ℝ≥0) : TopologicalSpace (ClosedLoopMFG.Limit.Path d T) :=
  inferInstanceAs (TopologicalSpace C(Set.Icc (0 : ℝ) T, EthierKurtz.SDEState d))

instance instBorelSpacePath (d : ℕ) (T : ℝ≥0) : BorelSpace (ClosedLoopMFG.Limit.Path d T) := ⟨rfl⟩

instance instSecondCountableTopologyPath (d : ℕ) (T : ℝ≥0) :
    SecondCountableTopology (ClosedLoopMFG.Limit.Path d T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, EthierKurtz.SDEState d))

instance instFunLikePath (d : ℕ) (T : ℝ≥0) :
    FunLike (ClosedLoopMFG.Limit.Path d T) (Set.Icc (0 : ℝ) T) (EthierKurtz.SDEState d) :=
  inferInstanceAs (FunLike C(Set.Icc (0 : ℝ) T, EthierKurtz.SDEState d) _ _)

instance instBorelSpaceFlow (d : ℕ) (T : ℝ≥0) : BorelSpace (ClosedLoopMFG.Converse.Flow d T) := ⟨rfl⟩

instance instFunLikeFlow (d : ℕ) (T : ℝ≥0) :
    FunLike (ClosedLoopMFG.Converse.Flow d T) (Set.Icc (0 : ℝ) T) (PR d) :=
  inferInstanceAs (FunLike C(Set.Icc (0 : ℝ) T, PR d) _ _)

/-- Real-valued paths `C([0, T]; ℝ)` (uniform topology, Borel σ-field). -/
def RPath (T : ℝ≥0) : Type := C(Set.Icc (0 : ℝ) T, ℝ)

instance instTopologicalSpaceRPath (T : ℝ≥0) : TopologicalSpace (RPath T) :=
  inferInstanceAs (TopologicalSpace C(Set.Icc (0 : ℝ) T, ℝ))

instance instMeasurableSpaceRPath (T : ℝ≥0) : MeasurableSpace (RPath T) := borel _

instance instBorelSpaceRPath (T : ℝ≥0) : BorelSpace (RPath T) := ⟨rfl⟩

instance instSecondCountableTopologyRPath (T : ℝ≥0) : SecondCountableTopology (RPath T) :=
  inferInstanceAs (SecondCountableTopology C(Set.Icc (0 : ℝ) T, ℝ))

instance instFunLikeRPath (T : ℝ≥0) : FunLike (RPath T) (Set.Icc (0 : ℝ) T) ℝ :=
  inferInstanceAs (FunLike C(Set.Icc (0 : ℝ) T, ℝ) _ _)

/-- The initial time `0 ∈ [0, T]`. -/
def tzero (T : ℝ≥0) : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, T.2⟩

/-- The terminal time `T ∈ [0, T]`. -/
def tend (T : ℝ≥0) : Set.Icc (0 : ℝ) T := ⟨T, T.2, le_rfl⟩

/-- Read a path at a real time (clamped to `[0, T]`). -/
noncomputable def ev {T : ℝ≥0} {Y : Type*} [TopologicalSpace Y] (x : C(Set.Icc (0 : ℝ) T, Y)) (s : ℝ) : Y := x (ClosedLoopMFG.Limit.clampT T s)

/-- The empirical measure `(1/n) Σ_k δ_{x_k}` of `n ≥ 1` points, written as the push-forward
of the uniform distribution on `Fin n`. -/
noncomputable def empirical {d n : ℕ} [NeZero n] (x : Fin n → EthierKurtz.SDEState d) : PR d :=
  ProbabilityMeasure.map
    (⟨(PMF.uniformOfFintype (Fin n)).toMeasure, inferInstance⟩ : ProbabilityMeasure (Fin n))
    (measurable_of_finite x).aemeasurable

/-- A filtration is complete: every `P`-null set (and hence every subset of one, `P` being an
outer measure) belongs to `𝓕 0`. -/
def IsCompleteFilt {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) : Prop :=
  ∀ s : Set Ω, P s = 0 → MeasurableSet[𝓕 0] s

/-- `W` is an `𝔽`-Brownian motion: a standard `d`-dimensional Brownian motion, adapted to `𝔽`,
whose increments after `t` are independent of `𝓕 t`. -/
def IsFBrownian {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (W : ℝ≥0 → Ω → EthierKurtz.SDEState d) : Prop :=
  EthierKurtz.IsStandardBrownian P W ∧
  (∀ t, Measurable[𝓕 t] (W t)) ∧
  ∀ t, Indep (𝓕 t)
    (MeasurableSpace.comap (fun ω (r : Set.Ici t) => W r ω - W t ω) inferInstance) P

end ClosedLoopMFG.SignGame


