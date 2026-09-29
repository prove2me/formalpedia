-- Prove2me | Definitions.Def_AvramDividend_Classical_DividendStrategy
-- name    : AvramDividend_Classical_DividendStrategy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:56:08.904232+00:00
-- url     : https://prove2.me/theorems/561c1e83-0505-4d9d-9f28-33943f44b28a
-- title:
--   Dividend strategies, ruin, admissibility, value $v_\pi$, value function $v_*$ and the barrier strategy $\pi_a$
-- statement:
--   Let $X$ be a spectrally negative Lévy process on $(\Omega,\mathcal F,\mathbb F,P)$, let $x\in\mathbb R$ be the initial capital and $q$ a discount rate.
--
--   1. A **dividend strategy** is a process $L=(L_t)_{t\ge0}$ with $L_0=0$ whose paths are nondecreasing and left-continuous, and which is $\mathbb F$-adapted. $L_t$ is the cumulative dividend paid up to time $t$.
--   2. The **controlled risk process** is $U_t=x+X_t-L_t$, and the **ruin time** is $\sigma^L=\inf\{t\ge0:U_t<0\}\in[0,\infty]$ ($\inf\emptyset=\infty$).
--   3. $L$ is **admissible**, written $L\in\Pi$, if it is a dividend strategy and no lump sum exceeds the reserves: $L_{t+}-L_t\le U_t$ for every $t<\sigma^L$ and for $t=0$, where $L_{t+}=\inf_{s>t}L_s$.
--   4. For $C\in[0,\infty]$, $\Pi_{\le C}$ is the set of $L\in\Pi$ with $U_t\le C$ for all $t>0$ (no constraint if $C=\infty$).
--   5. The **value** of $L$ is
--   $$v_L(x)=\mathbf E\Bigl[\int_0^{\sigma^L}e^{-qt}\,dL_t\Bigr]\in[0,\infty],$$
--   the Stieltjes integral being over $[0,\sigma^L)\cup\{0\}$ against the measure $dL$ that gives mass $L_{t+}-L_t$ to each jump time $t$, including the lump sum $L_{0+}$ at time $0$.
--   6. The **value function** of the classical dividend problem (2.2) is $v_*(x)=\sup_{L\in\Pi}v_L(x)$, and $\sup_{L\in\Pi_{\le C}}v_L(x)$ is its restriction to $\Pi_{\le C}$.
--   7. The **constant barrier strategy** $\pi_a$ at level $a$ is $L^a_0=0$ and, for $t>0$,
--   $$L^a_t=\Bigl(x-a+\sup_{0\le s\le t}X_s\Bigr)\vee0 .$$
--   For $x\le a$ this is $\sup_{s\le t}(x+X_s-a)\vee0$, the reflection of $x+X$ at the level $a$; for $x>a$ it pays the lump sum $x-a$ at time $0$ and then reflects at $a$.
--
--   The optimal dividend problem asks for $v_*$ and a strategy attaining it; the barrier strategies are the candidates.
--
--   **Formalization Note.** The paper writes the admissibility condition with a strict inequality, $L_{t+}-L_t<U_t$ for $t<\sigma^\pi$. The strict form excludes the paper's own strategy "take out all dividends immediately", whose value $v_0(x)=x+W(0)/W'(0+)$ the paper uses (p. 13); the non-strict form is used here, which does not change the supremum. The constraint at $t=0$ and the counting of the time-$0$ lump sum when $\sigma^L=0$ are made explicit: for a process of unbounded variation the barrier at $0$ has $\sigma^L=0$ almost surely while the paper assigns it the value $x$ (p. 8 and p. 13), so the lump sum paid at time $0$ must count, and it must be bounded by $x$. The integral excludes a jump at the ruin instant $\sigma^L>0$, which the admissibility condition does not constrain. The Stieltjes measure is Mathlib's measure of the right-continuous version of the path extended by $0$ to $(-\infty,0)$. The value is an extended nonnegative real and the value function a supremum in $[0,\infty]$, so finiteness is part of any identity with a real formula. The initial capital is added to $X$ (which starts at $0$) instead of changing the measure; $P_x$ is the law of $x+X$. The barrier strategy is defined for all $t$, not only up to ruin; this does not affect its value.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 3 (Section 2, eqs. (2.1), (2.2)), p. 4 (class Π≤C), p. 7 (Section 3.3, barrier strategy π_a)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

/-!
Dividend strategies, the controlled risk process, ruin, admissibility, the classes `Π` and
`Π_{≤C}`, the discounted dividend value `v_π`, the value function `v_*` of problem (2.2), and the
constant barrier strategy `π_a` of Avram, Palmowski, Pistorius, arXiv:math/0702893v1,
§2 (pp. 3–4) and §3.3 (p. 7).

Throughout, `X` is the spectrally negative Lévy process (started at `0`), `x` is the initial
capital, and `D : ℝ≥0 → Ω → ℝ` is the cumulative dividend process (the paper's `L^π`).
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- A dividend strategy (p. 3): a nondecreasing, left-continuous, `𝓕`-adapted process with
`D_0 = 0`. -/
def IsDividendStrategy (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ ω, D 0 ω = 0) ∧ (∀ ω, Monotone fun t => D t ω) ∧
    (∀ ω t, ContinuousWithinAt (fun s => D s ω) (Iic t) t) ∧ Adapted 𝓕 D

/-- The controlled risk process (2.1) with initial capital `x`: `U_t = x + X_t - D_t`. -/
def riskProcess (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    ℝ :=
  x + X.X t ω - D t ω

/-- The ruin time `σ^π = inf {t ≥ 0 : U_t < 0}` in `[0, ∞]` (`inf ∅ = ∞`). -/
noncomputable def ruinTime (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : riskProcess X x D t ω < 0), (t : ℝ≥0∞)

/-- The right limit `D_{t+} = inf_{s > t} D_s` (for nondecreasing `D`). -/
noncomputable def rightLimit (D : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ⨅ s : Ioi t, D s ω

/-- Admissibility (p. 3): `D` is a dividend strategy and a lump sum paid at time `t` never
exceeds the reserves, `D_{t+} - D_t ≤ U_t`, at every time `t < σ^π` and at `t = 0`.
(The paper writes a strict `<` and only `t < σ^π`; see the Formalization Note of the item.) -/
def IsAdmissible (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) : Prop :=
  IsDividendStrategy 𝓕 D ∧
    ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ riskProcess X x D t ω

/-- The class `Π_{≤C}` (p. 4), `C ∈ [0, ∞]`: admissible strategies with `U_t ≤ C` for all
`t > 0` (no constraint when `C = ∞`). -/
def IsAdmissibleLe (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) :
    Prop :=
  IsAdmissible X x D ∧ ∀ ω (t : ℝ≥0), 0 < t → ENNReal.ofReal (riskProcess X x D t ω) ≤ C

open scoped _root_.Classical in
/-- The Lebesgue–Stieltjes measure `dD` of a path on `ℝ`: the path is extended by `0` to
`(-∞, 0)`, and the measure of the right-continuous version is taken, so that
`dD({0}) = D_{0+}`, `dD([0, s)) = D_s` for `s > 0`, and `dD({t}) = D_{t+} - D_t`. -/
noncomputable def dividendMeasure (D : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℝ :=
  if h : Monotone (fun t : ℝ => D t.toNNReal ω) then h.stieltjesFunction.measure else 0

/-- The times at which dividends count towards the value: `[0, σ) ∪ {0}`. -/
def paymentTimes (σ : ℝ≥0∞) : Set ℝ :=
  {t | 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ)}

/-- The value of a strategy (p. 3): `v_π(x) = E_x[∫_0^{σ^π} e^{-qt} dL^π_t]`, in `[0, ∞]`,
the dividends paid on `[0, σ^π) ∪ {0}`. -/
noncomputable def dividendValue (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
    ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P

/-- The value function (2.2): `v_*(x) = sup_{π ∈ Π} v_π(x)`, in `[0, ∞]`. -/
noncomputable def valueFunction (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) : ℝ≥0∞ :=
  ⨆ (D : ℝ≥0 → Ω → ℝ) (_ : IsAdmissible X x D), dividendValue X q x D

/-- `sup_{π ∈ Π_{≤C}} v_π(x)`, in `[0, ∞]`. -/
noncomputable def valueFunctionLe (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (C : ℝ≥0∞) (x : ℝ) :
    ℝ≥0∞ :=
  ⨆ (D : ℝ≥0 → Ω → ℝ) (_ : IsAdmissibleLe X x C D), dividendValue X q x D

/-- The constant barrier strategy `π_a` with initial capital `x` (p. 7):
`L^a_0 = 0` and, for `t > 0`, `L^a_t = (x - a + sup_{0 ≤ s ≤ t} X_s) ∨ 0`
(for `x ≤ a` this is `sup_{s ≤ t}(x + X_s - a) ∨ 0`; for `x > a` it is
`(x - a) + sup_{s ≤ t} X_s`, a lump sum `x - a` at time `0` followed by reflection at `a`). -/
noncomputable def barrierStrategy (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) :
    ℝ≥0 → Ω → ℝ :=
  fun t ω => if t = 0 then 0 else max 0 (x - a + ⨆ s : Icc (0 : ℝ≥0) t, X.X s ω)

end AvramDividend.Classical


