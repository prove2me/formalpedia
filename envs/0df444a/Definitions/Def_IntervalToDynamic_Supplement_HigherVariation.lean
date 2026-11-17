-- Prove2me | Definitions.Def_IntervalToDynamic_Supplement_HigherVariation
-- name    : IntervalToDynamic_Supplement_HigherVariation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:36:15.354414+00:00
-- url     : https://prove2.me/theorems/b715df07-7800-4d84-bdf7-9cf65f0f3ffb
-- title:
--   Higher differences, normalized $k$-th variation, and polynomial interval regret
-- statement:
--   For a sequence $u_1,\ldots,u_T$, define $D^0u_t=u_t$ and $D^ku_t=D^{k-1}u_t-D^{k-1}u_{t-1}$. Its unnormalized and normalized $k$-th difference variations are
--   $$
--   V_{T,k}=\sum_{t=k+1}^T\|D^ku_t\|_2,
--   \qquad P_{T,k}=T^{k-1}V_{T,k}.
--   $$
--   On an interval $I$, $\mathcal P_{k-1}(I;\mathcal Y)$ consists of the functions $q:I\to\mathcal Y$ whose $k$-th difference is zero whenever the entire stencil $[t-k,t]$ lies in $I$. Polynomial interval regret is
--   $$
--   \operatorname{I-Reg}^{\rm poly}_I(q)=\sum_{t\in I}\bigl(h_t(y_t)-h_t(q(t))\bigr).
--   $$
--   A polynomial interval-regret guarantee holds simultaneously on every interval and against every such $\mathcal Y$-valued comparator.
--
--   **Formalization Note** Round zero is unused. The difference function is total, but every variation sum and polynomial constraint begins only where the complete backward stencil exists. For $k=1$, the normalized variation is definitionally the published path length.
-- source:
--   Wang–Zhao–Zhou, On the Relation Between Interval Regret and Dynamic Regret, arXiv:2609.34423, Eq. (16) and preceding definitions, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_IntervalToDynamic_Supplement_Geometry
import Definitions.Def_IntervalToDynamic_OnlineAlgorithm
import Definitions.Def_IntervalToDynamic_decisions

namespace IntervalToDynamic.Supplement

/-- The backward `k`-th difference `D^k u_t`, p.11. Round zero and earlier junk values are never
read: every use below starts at `t = k + 1`. -/
def kthDifference {E : Type*} [AddGroup E] : ℕ → (ℕ → E) → ℕ → E
  | 0, u, t => u t
  | k + 1, u, t => kthDifference k u t - kthDifference k u (t - 1)

/-- The unnormalized variation `V_{T,k} = Σ_{t=k+1}^T ‖D^k u_t‖₂`. -/
noncomputable def higherVariation {E : Type*} [NormedAddGroup E]
    (u : ℕ → E) (T k : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc (k + 1) T, ‖kthDifference k u t‖

/-- The normalized variation `P_{T,k} = T^{k-1} V_{T,k}`, p.11. -/
noncomputable def normalizedVariation {E : Type*} [NormedAddGroup E]
    (u : ℕ → E) (T k : ℕ) : ℝ :=
  (T : ℝ) ^ (k - 1) * higherVariation u T k

/-- `q ∈ P_{k-1}(I;Y)`: `q` is `Y`-valued on `I` and its `k`-th difference vanishes
whenever the complete stencil `[t-k,t]` lies in `I`, Eq. (16), p.11. -/
def IsPolynomialComparator {E : Type*} [AddGroup E] {T : ℕ}
    (k : ℕ) (I : RoundInterval T) (Y : Set E) (q : ℕ → E) : Prop :=
  (∀ t ∈ I.rounds, q t ∈ Y) ∧
  ∀ t ∈ Finset.Icc (I.start + k) I.stop, kthDifference k q t = 0

/-- Polynomial interval regret, Eq. (16), p.11. -/
def polynomialIntervalRegret {E : Type*} {T : ℕ} (h : ℕ → E → ℝ)
    (y q : ℕ → E) (I : RoundInterval T) : ℝ :=
  ∑ t ∈ I.rounds, (h t (y t) - h t (q t))

/-- A simultaneous polynomial interval-regret guarantee against every `Y`-valued polynomial
comparator on every interval. -/
def HasPolynomialIntervalRegret {E : Type*} [AddGroup E] (A : IntervalToDynamic.OnlineAlgorithm E)
    (Y : Set E) (C : (E → ℝ) → Prop) (T k : ℕ) (rate : ℕ → ℝ) : Prop :=
  ∀ h : ℕ → E → ℝ, (∀ t ∈ Finset.Icc 1 T, C (h t)) →
    ∀ I : RoundInterval T, ∀ q : ℕ → E, IsPolynomialComparator k I Y q →
      polynomialIntervalRegret h (IntervalToDynamic.decisions A h) q I ≤ rate I.rounds.card

end IntervalToDynamic.Supplement


