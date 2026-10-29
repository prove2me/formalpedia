-- Prove2me | Definitions.Def_PeskirShiryaev_LocalTime_Diffusion
-- name    : PeskirShiryaev_LocalTime_Diffusion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:25:25.120344+00:00
-- url     : https://prove2.me/theorems/1c6fa029-5c7d-4f38-8c54-99f1a2b1d2c3
-- title:
--   Diffusion equation and off-curve generator
-- statement:
--   Let $B$ be a continuous adapted process starting at zero, whose increment $B_t-B_s$ for $s\le t$ has centered Gaussian law of variance $t-s$ and is independent of $\mathcal F_s$. This is a standard Brownian motion relative to the given filtration. A coefficient is called locally bounded here when it is measurable and bounded on every bounded interval; these coefficient conditions are imposed by the goal theorem. A continuous adapted process $X$ solves the diffusion equation when
--   $$
--   X_t=X_0+\int_0^t b(X_s)\,ds+\int_0^t\sigma(X_s)\,dB_s.
--   $$
--   The stochastic integral is the independently characterized martingale integral, and the drift integral must be locally integrable. No uniqueness of the SDE is assumed.
--
--   For piecewise $C^{1,2}$ data along $c$, define
--   $$
--   G(t,x)=\bigl(F_t+bF_x+\tfrac12\sigma^2F_{xx}\bigr)(t,x)\mathbf1_{\{x\ne c(t)\}},\qquad
--   N(t,x)=F_x(t,x)\sigma(x)\mathbf1_{\{x\ne c(t)\}}.
--   $$
--   Both functions are zero on the curve and use the appropriate side derivatives elsewhere. They supply the two ordinary diffusion terms in the goal.
--
--   **Formalization Note** The Gaussian increment law and independence from past events are stated explicitly, so the Brownian driver uses the given filtration. Input processes have continuous paths at every sample point, as in the source; identities and local-martingale versions are understood almost surely. Nonnegativity of $\sigma$ is a separate hypothesis of the goal, as on the page; it is not built into the general SDE definition.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, p. 75 (PDF 95), Eqs. (3.5.7)–(3.5.9); Brownian conventions: pp. 93–94 (PDF 113–114), Section 4.4, Eqs. (4.4.1)–(4.4.2)

import Definitions.Def_PeskirShiryaev_LocalTime_Curve

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

/-
Imported Lean source for self-contained blind auditing. These are verbatim
source snapshots, not additional declarations in this module.

MODULE Definitions/Def_PeskirShiryaev_LocalTime_Calculus
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


MODULE Definitions/Def_PeskirShiryaev_LocalTime_Curve
import Definitions.Def_PeskirShiryaev_LocalTime_Calculus

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace PeskirShiryaev.LocalTime

def RegularCurve (c : ℝ≥0 → ℝ) : Prop :=
  Continuous c ∧ ∀ T, BoundedVariationOn c (Set.Icc 0 T)

/-- Partial derivatives on each open side, continuously extended to its
closure. The two spatial traces may differ on the curve. -/
structure SideDerivatives (c : ℝ≥0 → ℝ) (F : ℝ≥0 → ℝ → ℝ) where
  ftPlus : ℝ≥0 → ℝ → ℝ
  ftMinus : ℝ≥0 → ℝ → ℝ
  fxPlus : ℝ≥0 → ℝ → ℝ
  fxMinus : ℝ≥0 → ℝ → ℝ
  fxxPlus : ℝ≥0 → ℝ → ℝ
  fxxMinus : ℝ≥0 → ℝ → ℝ
  continuous_F : Continuous (fun z : ℝ≥0 × ℝ => F z.1 z.2)
  cont_tp : ContinuousOn (fun z : ℝ≥0 × ℝ => ftPlus z.1 z.2) {z | c z.1 ≤ z.2}
  cont_tm : ContinuousOn (fun z : ℝ≥0 × ℝ => ftMinus z.1 z.2) {z | z.2 ≤ c z.1}
  cont_xp : ContinuousOn (fun z : ℝ≥0 × ℝ => fxPlus z.1 z.2) {z | c z.1 ≤ z.2}
  cont_xm : ContinuousOn (fun z : ℝ≥0 × ℝ => fxMinus z.1 z.2) {z | z.2 ≤ c z.1}
  cont_xxp : ContinuousOn (fun z : ℝ≥0 × ℝ => fxxPlus z.1 z.2) {z | c z.1 ≤ z.2}
  cont_xxm : ContinuousOn (fun z : ℝ≥0 × ℝ => fxxMinus z.1 z.2) {z | z.2 ≤ c z.1}
  dtp : ∀ t x, c t < x → HasDerivWithinAt (fun r : ℝ => F r.toNNReal x)
    (ftPlus t x) (Set.Ici 0) (t : ℝ)
  dtm : ∀ t x, x < c t → HasDerivWithinAt (fun r : ℝ => F r.toNNReal x)
    (ftMinus t x) (Set.Ici 0) (t : ℝ)
  dxp : ∀ t x, c t < x → HasDerivAt (F t) (fxPlus t x) x
  dxm : ∀ t x, x < c t → HasDerivAt (F t) (fxMinus t x) x
  dxxp : ∀ t x, c t < x → HasDerivAt (fxPlus t) (fxxPlus t x) x
  dxxm : ∀ t x, x < c t → HasDerivAt (fxMinus t) (fxxMinus t x) x

noncomputable def SideDerivatives.timeAverage {c : ℝ≥0 → ℝ} {F : ℝ≥0 → ℝ → ℝ}
    (D : SideDerivatives c F) (t : ℝ≥0) (x : ℝ) : ℝ :=
  if c t < x then D.ftPlus t x else if x < c t then D.ftMinus t x
  else (D.ftPlus t x + D.ftMinus t x) / 2

noncomputable def SideDerivatives.spaceAverage {c : ℝ≥0 → ℝ} {F : ℝ≥0 → ℝ → ℝ}
    (D : SideDerivatives c F) (t : ℝ≥0) (x : ℝ) : ℝ :=
  if c t < x then D.fxPlus t x else if x < c t then D.fxMinus t x
  else (D.fxPlus t x + D.fxMinus t x) / 2

noncomputable def SideDerivatives.secondOff {c : ℝ≥0 → ℝ} {F : ℝ≥0 → ℝ → ℝ}
    (D : SideDerivatives c F) (t : ℝ≥0) (x : ℝ) : ℝ :=
  if c t < x then D.fxxPlus t x else if x < c t then D.fxxMinus t x else 0

noncomputable def SideDerivatives.jumpOn {c : ℝ≥0 → ℝ} {F : ℝ≥0 → ℝ → ℝ}
    (D : SideDerivatives c F) (t : ℝ≥0) (x : ℝ) : ℝ :=
  if x = c t then D.fxPlus t x - D.fxMinus t x else 0

/-- Symmetric curve local time, defined only by the quadratic-variation
occupation limit (3.5.6). The limit is in probability, ε tends to zero through
positive reals, and the occupation strip has strict endpoints. -/
def HasCurveLocalTime {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : ℝ≥0 → Ω → ℝ)
    (Q : IncreasingClock Ω) (c : ℝ≥0 → ℝ) (L : IncreasingClock Ω) : Prop :=
  Adapted ℱ L.value ∧ ∀ t : ℝ≥0,
    TendstoInMeasure P
      (fun ε : ℝ => fun ω => (2 * ε)⁻¹ * clockIntegral Q
        (fun s w => if c s - ε < X s w ∧ X s w < c s + ε then 1 else 0) t ω)
      (𝓝[>] (0 : ℝ)) (L.value t)

end PeskirShiryaev.LocalTime

-/

namespace PeskirShiryaev.LocalTime

/-- Standard Brownian motion relative to the filtration: continuous paths,
zero initial value, centered Gaussian increments with variance t-s, independent
of every event in the information available at time s. -/
def FilteredBrownian {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ ω, Continuous (fun t => B t ω)) ∧ Adapted ℱ B ∧
  (∀ᵐ ω ∂P, B 0 ω = 0) ∧
  ∀ s t : ℝ≥0, s ≤ t →
    HasLaw (fun ω => B t ω - B s ω) (gaussianReal 0 (t - s)) P ∧
    ∀ A : Set Ω, MeasurableSet[ℱ s] A →
      ∀ C : Set ℝ, MeasurableSet C →
        P (A ∩ {ω | B t ω - B s ω ∈ C}) = P A * (gaussianReal 0 (t - s)) C

def LocallyBoundedCoefficient (g : ℝ → ℝ) : Prop :=
  Measurable g ∧ ∀ R : ℝ, 0 ≤ R → ∃ K : ℝ, ∀ x, |x| ≤ R → |g x| ≤ K

/-- The SDE as an integral equation with independently characterized Itô
integral, not as any change-of-variable formula. -/
def SolvesSDE {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X B : ℝ≥0 → Ω → ℝ)
    (b σ : ℝ → ℝ) : Prop :=
  FilteredBrownian P ℱ B ∧ Adapted ℱ X ∧
  (∀ ω, Continuous (fun t => X t ω)) ∧
  ClockIntegrable P (timeClock Ω) (fun t ω => b (X t ω)) ∧
  ∃ M : ℝ≥0 → Ω → ℝ,
    HasMartingaleIntegral P ℱ B (timeClock Ω) (fun t ω => σ (X t ω)) M ∧
    (∀ᵐ ω ∂P, ∀ t, X t ω = X 0 ω +
      clockIntegral (timeClock Ω) (fun s w => b (X s w)) t ω + M t ω)

noncomputable def SideDerivatives.generatorOff {c : ℝ≥0 → ℝ} {F : ℝ≥0 → ℝ → ℝ}
    (D : SideDerivatives c F) (b σ : ℝ → ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  if x = c t then 0 else D.timeAverage t x + b x * D.spaceAverage t x +
    (σ x)^2 / 2 * D.secondOff t x

noncomputable def SideDerivatives.noiseOff {c : ℝ≥0 → ℝ} {F : ℝ≥0 → ℝ → ℝ}
    (D : SideDerivatives c F) (σ : ℝ → ℝ) (t : ℝ≥0) (x : ℝ) : ℝ :=
  if x = c t then 0 else D.spaceAverage t x * σ x

end PeskirShiryaev.LocalTime


