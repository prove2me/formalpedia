-- Prove2me | Definitions.Def_PeskirShiryaev_LocalTime_Calculus
-- name    : PeskirShiryaev_LocalTime_Calculus
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:23:54.643102+00:00
-- url     : https://prove2.me/theorems/f34f7209-26b0-43b3-9c43-24ae43e7b6b8
-- title:
--   Continuous semimartingales and stochastic integration
-- statement:
--   Work on a filtered probability space $(\Omega,\mathcal F,(\mathcal F_t),P)$, with time $t\ge0$. An increasing clock is a continuous increasing real path starting at zero; it carries its Lebesgue–Stieltjes measure. Write $\int_0^t H_s\,dQ_s$ for the corresponding pathwise integral. Local integrability on every finite interval is recorded explicitly.
--
--   A continuous local martingale $M$ starts at zero and becomes a martingale after stopping along an increasing sequence of stopping times tending almost surely to infinity. Its bracket $Q$ is the continuous increasing adapted process for which $M^2-Q$ is a local martingale. The integral relation explicitly checks that its integrator is a continuous local martingale and that its clock is its bracket. For a progressive integrand $H$, the martingale integral $J=\int H\,dM$ is characterized by
--   $$
--   J\in\mathcal M_{\mathrm{loc}}^c,\quad J_0=0,\quad
--   JM-\int H\,dQ\in\mathcal M_{\mathrm{loc}}^c,\quad
--   J^2-\int H^2\,dQ\in\mathcal M_{\mathrm{loc}}^c.
--   $$
--   The definition also requires local pathwise integrability of $H$ and $H^2$ against $Q$.
--
--   A continuous semimartingale is represented by $X=X_0+M+A^+-A^-$, where the two increasing processes are continuous and adapted. Its stochastic integral adds the two signed finite-variation integrals to the martingale integral. These definitions support nonsmooth test functions without defining an integral by the desired change-of-variable identity.
--
--   **Formalization Note** Clocks extend by zero to negative real times, and integrals use $(0,t]$. Continuous paths make the endpoint convention immaterial. The bracket and integral are independent compensated-product characterizations; their existence in the formulas is part of the theorem conclusions. The initial random variable need not be integrable. Input semimartingale paths are continuous at every sample point; local-martingale versions have almost surely continuous paths. Stopped martingales are explicitly integrable at each time.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 53–59, 63–66 (PDF 73–79, 83–86), Eqs. (3.1.7), (3.1.18), (3.3.6), (3.3.9)–(3.3.16)

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace PeskirShiryaev.LocalTime

/-- Continuous increasing paths, extended by zero before time zero, with their
actual Lebesgue–Stieltjes measures. No change-of-variable identity is built in. -/
structure IncreasingClock (Ω : Type*) where
  path : Ω → StieltjesFunction ℝ
  continuous : ∀ ω, Continuous (path ω)
  zero_nonpos : ∀ ω r, r ≤ 0 → path ω r = 0

def IncreasingClock.value {Ω : Type*} (Q : IncreasingClock Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Q.path ω t

noncomputable def clockIntegral {Ω : Type*} (Q : IncreasingClock Ω)
    (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Set.Ioc 0 (t : ℝ), H s.toNNReal ω ∂(Q.path ω).measure

def ClockIntegrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Q : IncreasingClock Ω) (H : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
    IntegrableOn (fun s : ℝ => H s.toNNReal ω) (Set.Ioc 0 (t : ℝ)) (Q.path ω).measure

def timeClock (Ω : Type*) : IncreasingClock Ω where
  path := fun _ => {
    toFun := fun r => max r 0
    mono' := fun _ _ h => max_le_max h le_rfl
    right_continuous' := fun _ => (continuous_id.max continuous_const).continuousWithinAt }
  continuous := fun _ => continuous_id.max continuous_const
  zero_nonpos := fun _ _ h => max_eq_right h

/-- Continuous local martingales starting at zero, using stopped martingales
and genuine stopping-time localizing sequences. -/
def ContinuousLocalMartingale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) : Prop :=
  Adapted ℱ M ∧ (∀ᵐ ω ∂P, Continuous (fun t => M t ω)) ∧
  (∀ᵐ ω ∂P, M 0 ω = 0) ∧
  ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence ℱ τ P ∧
    ∀ n, Martingale (stoppedProcess M (τ n)) ℱ P ∧
      ∀ t, Integrable (stoppedProcess M (τ n) t) P

/-- A quadratic variation is characterized by the compensated square, as in
(3.3.6), and an increasing continuous clock, not by a target formula. -/
def HasBracket {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) (Q : IncreasingClock Ω) : Prop :=
  ContinuousLocalMartingale P ℱ M ∧ Adapted ℱ Q.value ∧
  ContinuousLocalMartingale P ℱ (fun t ω => (M t ω)^2 - Q.value t ω)

/-- The martingale integral is pinned by its own bracket and its covariation
with M. These two compensated products characterize ∫ H dM independently of
any Itô or Tanaka identity. Integrability is part of the relation. -/
def HasMartingaleIntegral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) (Q : IncreasingClock Ω)
    (H J : ℝ≥0 → Ω → ℝ) : Prop :=
  HasBracket P ℱ M Q ∧ IsProgressive ℱ H ∧ ClockIntegrable P Q H ∧
  ClockIntegrable P Q (fun t ω => (H t ω)^2) ∧
  ContinuousLocalMartingale P ℱ J ∧
  ContinuousLocalMartingale P ℱ
    (fun t ω => J t ω * M t ω - clockIntegral Q H t ω) ∧
  ContinuousLocalMartingale P ℱ
    (fun t ω => (J t ω)^2 - clockIntegral Q (fun s w => (H s w)^2) t ω)

/-- A continuous semimartingale represented as X₀+M+A⁺−A⁻, with its
quadratic variation. The increasing parts encode local finite variation;
X₀ need not be integrable. -/
structure ContinuousSemimartingale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (X : ℝ≥0 → Ω → ℝ) where
  M : ℝ≥0 → Ω → ℝ
  pos : IncreasingClock Ω
  neg : IncreasingClock Ω
  bracket : IncreasingClock Ω
  martingale : ContinuousLocalMartingale P ℱ M
  pos_adapted : Adapted ℱ pos.value
  neg_adapted : Adapted ℱ neg.value
  quadratic : HasBracket P ℱ M bracket
  adapted : Adapted ℱ X
  continuous : ∀ ω, Continuous (fun t => X t ω)
  decomposition : ∀ᵐ ω ∂P, ∀ t, X t ω = X 0 ω + M t ω + pos.value t ω - neg.value t ω

def HasSemimartingaleIntegral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {X : ℝ≥0 → Ω → ℝ} (S : ContinuousSemimartingale P ℱ X)
    (H I : ℝ≥0 → Ω → ℝ) : Prop :=
  ClockIntegrable P S.pos H ∧ ClockIntegrable P S.neg H ∧
  ∃ J : ℝ≥0 → Ω → ℝ, HasMartingaleIntegral P ℱ S.M S.bracket H J ∧
    (∀ᵐ ω ∂P, ∀ t, I t ω = J t ω + clockIntegral S.pos H t ω - clockIntegral S.neg H t ω)

end PeskirShiryaev.LocalTime


