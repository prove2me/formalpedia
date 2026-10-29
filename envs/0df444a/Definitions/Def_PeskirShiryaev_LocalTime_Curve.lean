-- Prove2me | Definitions.Def_PeskirShiryaev_LocalTime_Curve
-- name    : PeskirShiryaev_LocalTime_Curve
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:24:41.031285+00:00
-- url     : https://prove2.me/theorems/f6439e60-69f7-47ad-a2e9-48ea1ae40f66
-- title:
--   Piecewise smooth functions and occupation local time
-- statement:
--   Let $c:[0,\infty)\to\mathbb R$ be continuous and of bounded variation on each finite interval. Let $F:[0,\infty)\times\mathbb R\to\mathbb R$ be continuous, and put $C_+=\{(t,x):x>c(t)\}$ and $C_-=\{(t,x):x<c(t)\}$. The side-derivative data consist of $F_t,F_x,F_{xx}$ on each open side, continuously extended to that side's closure. The spatial derivatives may have distinct boundary traces.
--
--   Write $\bar F_t$ and $\bar F_x$ for the ordinary derivatives off the curve and the arithmetic averages of the two traces on the curve. Write $F_{xx}^{\circ}=F_{xx}\mathbf1_{x\ne c(t)}$ and $\Delta F_x^{c}=(F_x^+-F_x^-)\mathbf1_{x=c(t)}$.
--
--   For a process $X$ with quadratic-variation clock $Q$, its symmetric local time at the curve is a continuous increasing adapted clock $\ell^c$, characterized at every fixed time by
--   $$
--   \ell_t^c=\mathop{P\!\operatorname{-lim}}_{\varepsilon\downarrow0}\frac1{2\varepsilon}
--   \int_0^t\mathbf1_{\{c(s)-\varepsilon<X_s<c(s)+\varepsilon\}}\,dQ_s.
--   $$
--   This normalization retains the one-half coefficient in the local time-space formula.
--
--   **Formalization Note** The time derivative at zero is a right derivative. Derivatives are imposed in the open sides and extend continuously to their closures. Values of a side extension on the opposite side are unused. The local-time limit is in probability through strictly positive real $\varepsilon$.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 74–75 (PDF 94–95), Eqs. (3.5.1)–(3.5.6)

import Definitions.Def_PeskirShiryaev_LocalTime_Calculus

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

-/

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


