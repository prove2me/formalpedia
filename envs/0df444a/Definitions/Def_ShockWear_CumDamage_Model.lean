-- Prove2me | Definitions.Def_ShockWear_CumDamage_Model
-- name    : ShockWear_CumDamage_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:30:03.405151+00:00
-- url     : https://prove2.me/theorems/0f8d39c4-367e-4395-bd97-59fc2dac3dfa
-- title:
--   Poisson shock survival function (2.1), convolution powers $F^{(k)}$ (4.1), the IHRA class (p. 631) and sign changes
-- statement:
--   This file fixes the objects of the cumulative damage shock model of Esary, Marshall and Proschan (1973).
--
--   1. **Poisson weights.** For $\lambda>0$, $t\geq0$ and $k \in \mathbb N$, $K_\lambda(k,t) = e^{-\lambda t}(\lambda t)^k/k!$, the probability that a Poisson process of rate $\lambda$ has exactly $k$ points in $[0,t]$.
--   2. **Shock survival function (2.1).** Given $\lambda$ and a sequence $\bar P_0, \bar P_1, \dots$ ($\bar P_k$ = probability of surviving $k$ shocks),
--   $$\bar H(t) = \sum_{k=0}^\infty \bar P_k\, e^{-\lambda t}\frac{(\lambda t)^k}{k!} \quad (t \ge 0), \qquad \bar H(t) = 1 \quad (t < 0).$$
--   3. **Convolution powers (4.1).** For a law $F$ on $\mathbb R$, $F^{(0)}$ is the point mass at $0$ and $F^{(k+1)} = F^{(k)} * F$; $F^{(k)}(x)$ is the mass $F^{(k)}$ gives to $(-\infty, x]$, i.e. $P\{X_1+\dots+X_k \le x\}$ for i.i.d. $X_i \sim F$. For a sequence of laws $F_1, F_2, \dots$, $F_1 * \dots * F_k$ is defined the same way, the empty convolution being the point mass at $0$.
--   4. **IHRA (p. 631, (iv)).** A survival function $\bar F$ has increasing hazard rate average if $[\bar F(t)]^{1/t}$ is decreasing (non-increasing) in $t > 0$.
--   5. **Sign changes.** A function $g$ on a set $D \subseteq \mathbb R$ (or a sequence $a_k$) *has at most one sign change, from $+$ to $-$ if one occurs*, if there are no $s < t$ in $D$ with $g(s) < 0 < g(t)$.
--   6. **Renewal count.** For random variables $X_1, X_2, \dots$, $N(x) = \#\{k \ge 1 : X_1 + \dots + X_k \le x\} \in \{0,1,\dots,\infty\}$, the number of renewals in $[0,x]$ not counting the origin.
--
--   These are the objects of §2, §4 and the ageing class (iv) of the paper; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note** A law is a measure on $\mathbb R$ (`Measure ℝ`); $F^{(k)}$ uses Mathlib's additive convolution of measures, and $F^{(k)}(x)$ is the real number `(convPow μ k (Set.Iic x)).toReal`. The paper's $F_i$ is Lean's `μ (i - 1)` and its $X_i$ is Lean's `X (i - 1)`. $[\bar F(t)]^{1/t}$ is the real power `Real.rpow`. "Decreasing" is the paper's weak sense (p. 628). The series is Lean's `tsum`; it converges whenever $\bar P$ is bounded, which every theorem of the mission assumes. $N(x)$ is an extended natural number (`Set.encard`).
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), pp. 628, 631, 633, 636–637, 641: (2.1), definition (iv), the kernel K(k, t) of p. 633, (4.1), Lemma 4.1a, Corollary 4.11

import Mathlib

namespace ShockWear.CumDamage

open MeasureTheory ProbabilityTheory

/-- The Poisson weight $e^{-\lambda t}(\lambda t)^k/k!$. -/
noncomputable def poisW (lam t : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(lam * t)) * (lam * t) ^ k / (k.factorial : ℝ)

/-- (2.1): $\bar H(t) = \sum_k \bar P_k e^{-\lambda t}(\lambda t)^k/k!$ for $t \ge 0$,
and $\bar H(t) = 1$ for $t < 0$. -/
noncomputable def shockSurv (lam : ℝ) (P : ℕ → ℝ) (t : ℝ) : ℝ :=
  if t < 0 then 1 else ∑' k, P k * poisW lam t k

/-- The k-fold convolution $F^{(k)}$ of a law on ℝ; $F^{(0)}$ is degenerate at 0 (p. 636). -/
noncomputable def convPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | k + 1 => Measure.conv (convPow μ k) μ

/-- $F^{(k)}(x) = $ the mass of $(-\infty, x]$ under the k-fold convolution. -/
noncomputable def cdfPow (μ : Measure ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (convPow μ k (Set.Iic x)).toReal

/-- $F_1 * \cdots * F_k$ for a sequence of laws, with the paper's $F_i$ = `μ (i - 1)`;
the empty convolution (k = 0) is degenerate at 0. -/
noncomputable def convProdPow (μ : ℕ → Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | k + 1 => Measure.conv (convProdPow μ k) (μ k)

/-- (iv) IHRA: $[\bar F(t)]^{1/t}$ is decreasing (non-increasing) in $t > 0$ (real power). -/
def IsIHRA (Fb : ℝ → ℝ) : Prop :=
  AntitoneOn (fun t => Fb t ^ (1 / t)) (Set.Ioi 0)

/-- `g` has at most one sign change on `D`, from + to − if one occurs. -/
def SignPM (g : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ s ∈ D, ∀ t ∈ D, s < t → ¬ (g s < 0 ∧ 0 < g t)

/-- A sequence has at most one sign change, from + to − if one occurs. -/
def SignPMSeq (a : ℕ → ℝ) : Prop :=
  ∀ j k, j < k → ¬ (a j < 0 ∧ 0 < a k)

/-- The number $N(x)$ of renewals in $[0, x]$, not counting the origin:
the number of $k \ge 1$ with $X_1 + \cdots + X_k \le x$ (paper's $X_i$ = Lean `X (i - 1)`),
as an extended natural number. -/
noncomputable def renewalCount {Ω : Type*} (X : ℕ → Ω → ℝ) (x : ℝ) (ω : Ω) : ℕ∞ :=
  {k : ℕ | 1 ≤ k ∧ ∑ i ∈ Finset.range k, X i ω ≤ x}.encard

end ShockWear.CumDamage


