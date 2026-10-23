-- Prove2me | Definitions.Def_ExplodingOffer_Mrl_Model
-- name    : ExplodingOffer_Mrl_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:59.534565+00:00
-- url     : https://prove2.me/theorems/f5379bb0-9939-415e-8518-07ada857e54b
-- title:
--   §3–§4, pp. 5–12 — Poisson search with a deadline offer: ℒ, 𝒯, 𝒯⁻¹, value-to-go (2)/(18), Π, problem (7), ŝ (10)
-- statement:
--   The model of Hu and Tang. A **proposer** makes an offer of size $s$ that expires at a deadline $t_D \in [0, T]$ to a **responder**, who meanwhile searches for alternative offers over the horizon $[0, T]$. Alternative offers arrive by a Poisson process of rate $\lambda > 0$, each exploding (it must be accepted on arrival), and their sizes are i.i.d. copies of a random variable $X$ with law $\mu$.
--
--   1. **Offer law** `OfferDist μ a b`: $X$ is nonnegative and continuous (no atoms), with support $[a, b]$, $0 \le a \le b$, $b \neq 0$, where $b$ may be $+\infty$, and with finite mean $\bar x = \mathbb E[X]$. "Support $[a,b]$" means: $\mu$ puts no mass below $a$ or above $b$, and positive mass on every open subinterval of $[a, b]$.
--   2. **Conditional mean** $\mathbb E[X \mid X \ge s] = \mathbb E[X;\, X \ge s] / \mathbb P(X \ge s)$.
--   3. **Stop-loss transform and value-to-time operator** (3):
--   $$\mathcal L(v) = \mathbb E[(X - v)^+], \qquad \mathcal T(V) = \int_0^V \frac{dv}{\mathcal L(v)}.$$
--   $\mathcal T^{-1}(y)$ is the supremum of the $V \in [0, b)$ with $\mathcal T(V) \le y$; for $y \ge 0$ it inverts $\mathcal T : [0,b) \to [0, \infty)$.
--   4. **Value-to-go** (2): for $t \le t_D$, $V(t; s, t_D) = \mathcal T^{-1}(\mathcal T(s) + \lambda (t_D - t))$ if $s < b$ and $V(t;s,t_D) = s$ if $s \ge b$; for $t > t_D$, $V(t; s, t_D) = \mathcal T^{-1}(\lambda(T - t))$. The minimum acceptable size is $v(t_D) = \mathcal T^{-1}(\lambda(T - t_D))$.
--   5. **HJB system** (18): $V$ is continuous on $[0, t_D]$ and on $(t_D, T]$, satisfies $V'(t) = -\lambda \mathcal L(V(t))$ on $[0, t_D) \cup (t_D, T)$ (one-sided at $0$), $V(t_D) = s$, and $V(T) = 0$ when $t_D < T$.
--   6. **Proposer's surplus** (6): with the no-acceptance probability
--   $$\mathbb P(N(0,t_D) = 0) = \exp\Big[-\lambda \int_0^{t_D} \mathbb P\big(X \ge V(t; s, t_D)\big)\, dt\Big],$$
--   the surplus is $\Pi(s, t_D) = (u - s)\, \mathbb P(N(0,t_D) = 0)$, where $u$ is the proposer's utility from the responder.
--   7. **Problem (7)**: maximize $\Pi(s, t_D)$ subject to $v(t_D) \le s \le u$, $0 \le t_D \le T$; an **optimal offer package** is a feasible $(s, t_D)$ whose surplus is at least that of every feasible package.
--   8. **Deadline (4)**: $t_D^*(s) = (T - \mathcal T(s)/\lambda)^+$, which is $0$ for $s \ge b$ (where $\mathcal T(s) = +\infty$).
--   9. **The size $\hat s$** (10): $\hat s = b$ if $u \ge b$; $\hat s$ is the solution $s \in [a, b)$ of $\mathbb E[X \mid X \ge s] = u$ if $\bar x \le u < b$; $\hat s = 0$ if $u < \bar x$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The upper end $b$ is an extended real (`EReal`) and is only compared with real numbers. Finite mean is assumed explicitly. "Continuous" is the absence of atoms (`NullSingletonClass`). The HJB terminal condition $V(T) = 0$ is imposed only for $t_D < T$: at $t_D = T$ the printed system demands both $V(T) = s$ and $V(T) = 0$. In (10) the boundary case $u = b$ (finite) is put in the first case, where both cases give $\hat s = b$. $\mathcal T$ is meaningful only below $b$ (in Lean $1/0 = 0$ above $b$); every statement evaluates it only there or through $t_D^*$, which tests $s < b$ first.
-- source:
--   Hu & Tang, Size Matters, So Does Duration: The Interplay between Offer Size and Offer Deadline, SSRN preprint 3143414 (version of 2020-05-16), pp. 5–12 and 33, §3.1, §3.2, §4, §4.1, eqs. (2)–(4), (6), (7), (10), (18)

import Mathlib

namespace ExplodingOffer.Mrl

open MeasureTheory

/-- §3.1, p. 6: the law `μ` of an alternative offer `X`. `X` is a nonnegative continuous random
variable with support `[a, b]`, `0 ≤ a ≤ b`, `b ≠ 0`, where `b` may be `+∞`. "Continuous" is
`NullSingletonClass` (no atoms); "support `[a, b]`" is: no mass below `a`, no mass above `b`,
and positive mass on every open subinterval of `[a, b]`. The finite mean `x̄` is assumed explicitly (the page names `x̄`). -/
structure OfferDist (μ : Measure ℝ) (a : ℝ) (b : EReal) : Prop where
  isProb : IsProbabilityMeasure μ
  noAtoms : NullSingletonClass μ
  a_nonneg : 0 ≤ a
  a_le_b : (a : EReal) ≤ b
  b_ne_zero : b ≠ 0
  below : μ (Set.Iio a) = 0
  above : μ {x : ℝ | b < (x : EReal)} = 0
  noGap : ∀ x y : ℝ, a ≤ x → x < y → (y : EReal) ≤ b → 0 < μ (Set.Ioo x y)
  integrable : Integrable (fun x : ℝ => x) μ

/-- The mean `x̄ = E[X]`. -/
noncomputable def mean (μ : Measure ℝ) : ℝ := ∫ x, x ∂μ

/-- The conditional mean `E[X | X ≥ s]` (§4.1, p. 11). -/
noncomputable def condMean (μ : Measure ℝ) (s : ℝ) : ℝ :=
  (∫ x in Set.Ici s, x ∂μ) / (μ (Set.Ici s)).toReal

/-- (3), p. 7: `ℒ(v) = E[(X − v)⁺]`. -/
noncomputable def Lfun (μ : Measure ℝ) (v : ℝ) : ℝ := ∫ x, max (x - v) 0 ∂μ

/-- (3), p. 7: the value-to-time operator `𝒯(V) = ∫₀^V dv / ℒ(v)`. Meaningful for `0 ≤ V < b`,
where `ℒ > 0`. -/
noncomputable def Tval (μ : Measure ℝ) (V : ℝ) : ℝ := ∫ v in (0 : ℝ)..V, 1 / Lfun μ v

/-- `𝒯⁻¹(y)`: the supremum of the values `V ∈ [0, b)` with `𝒯(V) ≤ y`. For `y ≥ 0` this is the
inverse of `𝒯 : [0, b) → [0, ∞)` (milestone `tval_bijection`). -/
noncomputable def Tinv (μ : Measure ℝ) (b : EReal) (y : ℝ) : ℝ :=
  sSup {V : ℝ | 0 ≤ V ∧ (V : EReal) < b ∧ Tval μ V ≤ y}

/-- (2) and the `s ≥ b` display of Lemma 1, pp. 7–8: the responder's value-to-go `V(t; s, t_D)`:
`𝒯⁻¹(𝒯(s) + λ(t_D − t))` (if `s < b`) or `s` (if `s ≥ b`) for `t ≤ t_D`, and `𝒯⁻¹(λ(T − t))`
for `t > t_D`. -/
noncomputable def valueToGo (μ : Measure ℝ) (b : EReal) (lam T s tD t : ℝ) : ℝ :=
  if t ≤ tD then (if (s : EReal) < b then Tinv μ b (Tval μ s + lam * (tD - t)) else s)
  else Tinv μ b (lam * (T - t))

/-- Lemma 1, p. 8: the responder's minimum acceptable size `v(t_D) = 𝒯⁻¹(λ(T − t_D))`. -/
noncomputable def minAccept (μ : Measure ℝ) (b : EReal) (lam T tD : ℝ) : ℝ :=
  Tinv μ b (lam * (T - tD))

/-- (18), p. 33: `V` solves the HJB equations of the package `(s, t_D)`:
`V'(t) = −λ ℒ(V(t))` on `[0, t_D) ∪ (t_D, T)`, `V(t_D) = s`, `V(T) = 0`. `V` is continuous on
`[0, t_D]` and on `(t_D, T]`; at `t = 0` the derivative is one-sided. The terminal condition
`V(T) = 0` is imposed when `t_D < T`; at `t_D = T` the deadline condition `V(t_D) = s` is the
terminal one. -/
def IsHJB (μ : Measure ℝ) (lam T s tD : ℝ) (V : ℝ → ℝ) : Prop :=
  V tD = s ∧ (tD < T → V T = 0) ∧
  ContinuousOn V (Set.Icc 0 tD) ∧ ContinuousOn V (Set.Ioc tD T) ∧
  (∀ t ∈ Set.Ico 0 tD, HasDerivWithinAt V (-(lam * Lfun μ (V t))) (Set.Icc 0 tD) t) ∧
  (∀ t ∈ Set.Ioo tD T, HasDerivAt V (-(lam * Lfun μ (V t))) t)

/-- p. 9: the probability that the responder accepts no alternative offer during `[0, t_D]`,
`P(N(0, t_D) = 0) = exp[−λ ∫₀^{t_D} P(X ≥ V(t)) dt]`. -/
noncomputable def noAcceptProb (μ : Measure ℝ) (b : EReal) (lam T s tD : ℝ) : ℝ :=
  Real.exp (-(lam * ∫ t in (0 : ℝ)..tD, (μ (Set.Ici (valueToGo μ b lam T s tD t))).toReal))

/-- (6), first equality, p. 9: the proposer's expected surplus `Π(s, t_D) = (u − s) P(N(0, t_D) = 0)`. -/
noncomputable def surplus (μ : Measure ℝ) (b : EReal) (lam T u s tD : ℝ) : ℝ :=
  (u - s) * noAcceptProb μ b lam T s tD

/-- The constraints of problem (7), p. 9: `v(t_D) ≤ s ≤ u`, `0 ≤ t_D ≤ T`. -/
def Feasible (μ : Measure ℝ) (b : EReal) (lam T u s tD : ℝ) : Prop :=
  minAccept μ b lam T tD ≤ s ∧ s ≤ u ∧ 0 ≤ tD ∧ tD ≤ T

/-- `(s, t_D)` is an optimal offer package: an optimal solution of problem (7), p. 9. -/
def IsOptimalPackage (μ : Measure ℝ) (b : EReal) (lam T u s tD : ℝ) : Prop :=
  Feasible μ b lam T u s tD ∧
  ∀ s' tD' : ℝ, Feasible μ b lam T u s' tD' →
    surplus μ b lam T u s' tD' ≤ surplus μ b lam T u s tD

/-- (4), p. 8, and Proposition 1, p. 10: `t*_D(s) = (T − 𝒯(s)/λ)⁺`, where `𝒯(s) = +∞` (so
`t*_D(s) = 0`) for `s ≥ b`. -/
noncomputable def optDeadline (μ : Measure ℝ) (b : EReal) (lam T s : ℝ) : ℝ :=
  if (s : EReal) < b then max (T - Tval μ s / lam) 0 else 0

/-- (10), p. 11: `sh` is `ŝ`. `ŝ = b` if `u > b`; `ŝ` solves `E[X | X ≥ s] = u`, `s ∈ [a, b]`, if
`x̄ ≤ u ≤ b`; `ŝ = 0` if `u < x̄`. The case `u = b` (finite) is merged into the first case: there
the solution of the middle case is `s = b`. -/
def IsSHat (μ : Measure ℝ) (a : ℝ) (b : EReal) (u sh : ℝ) : Prop :=
  (b ≤ (u : EReal) ∧ sh = b.toReal) ∨
  (mean μ ≤ u ∧ (u : EReal) < b ∧ a ≤ sh ∧ (sh : EReal) < b ∧ condMean μ sh = u) ∨
  (u < mean μ ∧ sh = 0)

end ExplodingOffer.Mrl


