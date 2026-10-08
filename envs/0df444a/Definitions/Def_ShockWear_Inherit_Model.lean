-- Prove2me | Definitions.Def_ShockWear_Inherit_Model
-- name    : ShockWear_Inherit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:32.538924+00:00
-- url     : https://prove2.me/theorems/4d4694af-6fdc-48f8-8635-cdc709636b81
-- title:
--   Poisson shock survival, failure probabilities, density, and PF₂/IHR conditions
-- statement:
--   Fix a shock arrival rate $\lambda>0$ and a sequence $\bar P_k$ of probabilities of surviving the first $k$ shocks. The probability weight for $k$ Poisson arrivals by time $t\geq0$ is
--
--   $$w_k(t)=e^{-\lambda t}(\lambda t)^k/k!.$$
--
--   The model defines $\bar H(t)=\sum_{k\geq0}\bar P_k w_k(t)$ for $t\geq0$ and $\bar H(t)=1$ for $t<0$. Its failure probabilities are $p_0=1-\bar P_0$ and $p_{k+1}=\bar P_k-\bar P_{k+1}$, and its positive-time density is $h(t)=\lambda\sum_{k\geq0}p_{k+1}w_k(t)$.
--
--   The module also defines the paper's weakly decreasing successive-ratio condition for a PF₂ sequence, the PF₂ density condition, increasing hazard rate through survival ratios at nonnegative ages, and the negative–positive–negative sign-change condition used in the proof of Theorem 3.1. These shared definitions fix the mathematical objects for all statements in this mission.
--
--   For a survival function $\bar F$ of a life distribution, it further defines the ageing classes of pp. 631–632 used by the remaining statements:
--   1. **DHR** (ii′): $\bar F(x+t)/\bar F(t)$ is increasing in $t\geq0$ whenever $x>0$;
--   2. the residual integral $\int_0^\infty\bar F(x+t)\,dx\in[0,\infty]$;
--   3. **DMRL** (iii): $\int_0^\infty\bar F(x+t)\,dx/\bar F(t)$ is decreasing in $t\geq0$ wherever $\bar F(t)>0$;
--   4. **NBUE** (vi): $\int_0^\infty\bar F(x)\,dx\geq\int_0^\infty\bar F(t+x)\,dx/\bar F(t)$ for all $t\geq0$ with $\bar F(t)>0$;
--   5. **logarithmically convex density** (i′) on $(0,\infty)$: $f(x+t)/f(t)$ is increasing in $t>0$ whenever $x>0$.
--
--   **Formalization Note** Ratios are cross-multiplied to include zero survival probabilities without Lean's division-by-zero value, except in DMRL and NBUE, where the integrals may be infinite: there the ratio is computed in $[0,\infty]$ and only where $\bar F(t)>0$. IHR, DHR and DMRL compare ages $t\geq0$, the domain of a life distribution that may have an atom at the origin. The survival function is extended to negative time as in (2.1); the density is its positive-time formula, not a constructed random lifetime.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), pp. 628–631, (2.1)–(2.3), Definition 2.3, ageing classes (i)–(iii), (vi) on p. 631 and (i′), (ii′) on p. 632; https://doi.org/10.1214/aop/1176996891

import Mathlib
import Definitions.Def_ShockWear_CumDamage_Model

namespace ShockWear.Inherit

open scoped ENNReal

/-- The chance of failure at shock `k`, including failure at time zero. -/
def failProb (P : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1 - P 0
  | k + 1 => P k - P (k + 1)

/-- The positive-time density in (2.3), with its sum reindexed from zero. -/
noncomputable def shockDens (lam : ℝ) (P : ℕ → ℝ) (t : ℝ) : ℝ :=
  lam * ∑' k, failProb P (k + 1) * ShockWear.CumDamage.poisW lam t k

/-- The weakly decreasing successive-ratio condition for a PF₂ sequence,
expressed without division at zero. -/
def IsPF2SeqFrom (m : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ j k, m ≤ j → j ≤ k → a (k + 1) * a j ≤ a (j + 1) * a k

/-- The positive-time PF₂ density condition of p. 631. -/
def IsPF2Dens (f : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → ∀ s t, 0 < s → s ≤ t → f (x + t) * f s ≤ f (x + s) * f t

/-- Increasing hazard rate, stated through decreasing survival ratios on the
life-distribution domain `t ≥ 0`. -/
def IsIHR (Fb : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → ∀ s t, 0 ≤ s → s ≤ t → Fb (x + t) * Fb s ≤ Fb (x + s) * Fb t

/-- On a set, a sign pattern cannot return to positive after passing from
positive to negative. This expresses at most two sign changes in the order
negative, positive, negative. -/
def SignMPM (g : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, r < s → s < t → ¬ (0 < g r ∧ g s < 0 ∧ 0 < g t)

/-- Decreasing hazard rate (ii′), p. 632, stated through increasing survival ratios
on the life-distribution domain `t ≥ 0`. -/
def IsDHR (Fb : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → ∀ s t, 0 ≤ s → s ≤ t → Fb (x + s) * Fb t ≤ Fb (x + t) * Fb s

/-- `∫₀^∞ F̄(x + t) dx`, valued in `[0, ∞]`. -/
noncomputable def resInt (Fb : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (Fb (x + t))

/-- (iii) Decreasing mean residual life: `∫₀^∞ F̄(x + t) dx / F̄(t)` is decreasing
for `t ≥ 0` wherever `F̄(t) > 0`, computed in `[0, ∞]`. -/
def IsDMRL (Fb : ℝ → ℝ) : Prop :=
  AntitoneOn (fun t => resInt Fb t / ENNReal.ofReal (Fb t)) {t | 0 ≤ t ∧ 0 < Fb t}

/-- (vi) New better than used in expectation:
`∫₀^∞ F̄ ≥ ∫₀^∞ F̄(t + x) dx / F̄(t)` for all `t ≥ 0` with `F̄(t) > 0`, in `[0, ∞]`. -/
def IsNBUE (Fb : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → 0 < Fb t → resInt Fb t / ENNReal.ofReal (Fb t) ≤ resInt Fb 0

/-- (i′) Logarithmically convex density on `(0, ∞)`: `f(x + t)/f(t)` is increasing
in `t > 0` whenever `x > 0` (cross-multiplied). -/
def IsLogConvexDens (f : ℝ → ℝ) : Prop :=
  ∀ x, 0 < x → ∀ s t, 0 < s → s ≤ t → f (x + s) * f t ≤ f (x + t) * f s

end ShockWear.Inherit


