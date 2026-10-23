-- Prove2me | Definitions.Def_EquilibriumExperiment_Gradient_Model
-- name    : EquilibriumExperiment_Gradient_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:38:53.507579+00:00
-- url     : https://prove2.me/theorems/bd0b9085-03a3-4a76-9d49-f15479fd853b
-- title:
--   §3–§4.1, pp. 12–21 — stochastic market given A = a: demand, regular allocation ω, matching Ω, choice functions, equilibrium (A.2), q (3.12), μ_a, u_a (3.15), Δ (3.17)/(3.19), estimators (4.1)–(4.3)
-- statement:
--   This file sets up the stochastic market of Wager and Xu, *Experimenting in Equilibrium*, §3 and §4.1, conditional on one fixed global state $A = a$; the state index $a$ is dropped throughout.
--
--   **Primitives.** A market consists of a number $d > 0$ (the scaled demand $d_a$); for every market size $n \in \mathbb N$, a law $F^{(n)}$ of the demand $D$; a law $\beta$ of the private supplier feature $B$ on a measurable space $\mathcal B$; choice functions $f_b : \mathbb R_+ \to [0,1]$ with first and second derivatives $f_b'$, $f_b''$; a regular allocation function $\omega$; the allocation function $\Omega(d,t)$ of (3.3) with its error term $l(d,t)$; and the limiting revenue function $r$.
--
--   **Regular allocation function (Definition 5).** $\omega : \mathbb R_+ \to [0,1]$ is smooth on $(0,\infty)$, concave and non-decreasing on $\mathbb R_+$, with $\lim_{x\to 0}\omega(x) = 0$, $\lim_{x\to\infty}\omega(x) \le 1$ and $\lim_{x\to 0}\omega'(x) \le 1$.
--
--   **Standing assumptions.** The predicate $\mathrm{Standing}$ collects:
--   1. $d > 0$; each $F^{(n)}$ is a probability measure on $[0,\infty)$ with $\mathbb E[D/n] = d$ for $n \ge 1$;
--   2. (3.1) $\lim_{n\to\infty}\mathbb E[(D/n - d)^2] = 0$ and (3.2) $n\,\mathbb P(D/n \notin [d/2, 2d]) \to 0$;
--   3. $\beta$ is a probability measure and $\omega$ is a regular allocation function;
--   4. Assumption 1: $\Omega(d,t)$ is non-decreasing in $d$ and non-increasing in $t$ on $\mathbb R_+^2$, and $\Omega(d,t) = \omega(d/t) + l(d,t)$ for all $d,t \ge 0$, where $0 \le l \le K$ and $|l(d,t)| = o(1/\sqrt t + 1/\sqrt d)$, read jointly: for every $\varepsilon > 0$ there is $K$ with $|l(d,t)| \le \varepsilon(1/\sqrt t + 1/\sqrt d)$ whenever $d, t \ge K$;
--   5. Assumption 2: each $f_b$ takes values in $[0,1]$ on $\mathbb R_+$, is non-decreasing, and is twice differentiable on $\mathbb R_+$ with $|f_b''| \le K$ uniformly in $b$;
--   6. the part of Assumption 3 about $r$: $r \ge 0$ on $\mathbb R_+$, $r$ is smooth on $(0,\infty)$ and every derivative of order $k \ge 1$ is bounded;
--   7. measurability of $d \mapsto \Omega(d,t)$, $(b,x) \mapsto f_b(x)$ and $(b,x) \mapsto f_b'(x)$.
--
--   **Equilibrium objects.** With $X \sim \mathrm{Binomial}(n,\mu)$ independent of $D$,
--   $$q^{(n)}(\mu) = \mathbb E[\Omega(D,X)] = \sum_{k=0}^n \binom nk \mu^k(1-\mu)^{n-k}\,\mathbb E[\Omega(D,k)] \quad (3.12),$$
--   $\psi^{(n)}(\mu,\pi) = \mathbb E[f_{B}(P\,q^{(n)}(\mu))]$ with $B \sim \beta$, $P \sim \pi$ (A.1), and $\mu^{(n)}(\pi)$ is the solution in $[0,1]$ of the balance equation $\psi^{(n)}(\mu,\pi) = \mu$ (A.2). The symmetric perturbation law $\pi_{p,\zeta}$ puts mass $1/2$ on each of $p \pm \zeta$ (3.11); $\mu^{(n)}(p) = \mu^{(n)}(\delta_p)$. The mean-field supply $\mu(p)$ is the solution in $(0,1]$ of $\mu = \mathbb E[f_B(p\,\omega(d/\mu))]$, and
--   $$u(p) = \bigl(r(d/\mu(p)) - p\,\omega(d/\mu(p))\bigr)\mu(p) \quad (3.15).$$
--   The marginal response functions are $\Delta^{(n)}(p) = q^{(n)}(\mu^{(n)}(p))\,\mathbb E[f_B'(p\,q^{(n)}(\mu^{(n)}(p)))]$ (3.17) and $\Delta(p) = \omega(d/\mu(p))\,\mathbb E[f_B'(p\,\omega(d/\mu(p)))]$ (3.19), and $\mu'(p)$ denotes the right-hand side of (3.20), $\Delta(p) / \bigl(1 + p\,d\,\Delta(p)\,\omega'(d/\mu(p)) / (\mu(p)^2\omega(d/\mu(p)))\bigr)$.
--
--   **The experiment.** In the $n$-th system the outcome is the demand $D \sim F^{(n)}$ and, independently for each supplier $i \le n$, a feature $B_i \sim \beta$, a payment $P_i \sim \pi$ and a uniform $U_i \in [0,1]$. Supplier $i$ is active, $Z_i = 1$, iff $U_i \le f_{B_i}(P_i\,q^{(n)}(\mu^{(n)}(\pi)))$. Under $\pi = \pi_{p,\zeta}$ the perturbation signs are $\varepsilon_i = (P_i - p)/\zeta$, with mean $\bar\varepsilon$; $\bar D = D/n$, $\bar Z = \frac1n\sum_i Z_i$, and
--   $$\hat\Delta = \zeta^{-1}\frac{\sum_i (Z_i - \bar Z)(\varepsilon_i - \bar\varepsilon)}{\sum_i(\varepsilon_i - \bar\varepsilon)^2}\ (4.1),\qquad \hat\Upsilon = \hat\Delta \Big/ \Bigl(1 + \frac{p\bar D\hat\Delta\,\omega'(\bar D/\bar Z)}{\bar Z^2\omega(\bar D/\bar Z)}\Bigr)\ (4.2),$$
--   $$\hat\Gamma = \hat\Upsilon\bigl[r(\bar D/\bar Z) - p\,\omega(\bar D/\bar Z) - (r'(\bar D/\bar Z) - p\,\omega'(\bar D/\bar Z))\,\bar D/\bar Z\bigr] - \omega(\bar D/\bar Z)\,\bar Z\ (4.3).$$
--
--   These objects are shared by every statement of the mission: the goal (Theorem 6) asserts that $\hat\Gamma$ consistently estimates $u'(p)$.
--
--   **Formalization Note** Everything is conditional on one global state $a$; since the state space is finite and its law does not depend on $n$, the paper's unconditional probability in (4.4) is a finite mixture of the conditional ones. Functions defined on $\mathbb R_+$ are Lean functions on $\mathbb R$ whose hypotheses are stated on $[0,\infty)$ only. With Lean's convention $d/0 = 0$, Assumption 1's decomposition at $t = 0$ reads $\Omega(d,0) = \omega(0) + l(d,0) = l(d,0)$. The supplier decision is realized by a uniform $U_i$: given $B_i, P_i$, $\mathbb P(Z_i = 1) = f_{B_i}(P_i\,q^{(n)}(\mu^{(n)}(\pi)))$, which is the choice model (3.6) at the equilibrium of Lemma 1, independently across suppliers. $\mu^{(n)}(\pi)$ and $\mu(p)$ are defined by choice among the solutions and take the value $0$ if there is none; Lemma 1 and Lemma 2 show the solutions exist and are unique. $\omega'$ and $r'$ are Lean's `deriv`; $f_b'$ and $f_b''$ are carried as data and pinned by one-sided derivative hypotheses on $[0,\infty)$. $\bar\omega = \sup_{x\ge 0}\omega(x)$ is `omegaSup`. The demand second moment in (3.1) is a lower Lebesgue integral, so it is never a junk value. The disclosed additions are $d > 0$ and the measurability conditions. The pre-limit revenue $R$, the service amounts $S_i$ and the pre-limit utility $u^{(n)}$ enter no statement of this mission and are not modelled.
-- source:
--   Wager & Xu, Experimenting in Equilibrium, arXiv:1903.02124v5, pp. 12–21, §3, §4.1, Definitions 5 and 9, Assumptions 1–3, eqs. (3.1)–(3.4), (3.6), (3.11)–(3.12), (3.15), (3.17)–(3.20), (4.1)–(4.3); Appendix A.1, (A.1)–(A.2), p. 36

import Mathlib

namespace EquilibriumExperiment.Gradient

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical

/-- Primitives of the `n`-indexed stochastic market of §3 (Wager & Xu, pp. 12–16), conditional on
one fixed global state `A = a` (the state index is dropped). -/
structure Market (B : Type) [MeasurableSpace B] where
  /-- `d_a`, the limiting scaled demand. -/
  d : ℝ
  /-- `F_a^{(n)}`: law of the demand `D` in the `n`-th system, given `A = a`. -/
  F : ℕ → Measure ℝ
  /-- Law of the private feature `B_i`, given `A = a`. -/
  β : Measure B
  /-- Choice functions `f_b`. -/
  f : B → ℝ → ℝ
  /-- `f_b′`, carried as data and pinned by `HasDerivWithinAt` in `Market.Standing`. -/
  f' : B → ℝ → ℝ
  /-- `f_b″`, carried as data and pinned by `HasDerivWithinAt` in `Market.Standing`. -/
  f'' : B → ℝ → ℝ
  /-- The regular allocation function `ω` (Definition 5). -/
  ω : ℝ → ℝ
  /-- The allocation function `Ω(d, t)` of (3.3). -/
  Ω : ℝ → ℝ → ℝ
  /-- The error function `l` of Assumption 1. -/
  l : ℝ → ℝ → ℝ
  /-- The limiting revenue function `r` of Assumption 3. -/
  r : ℝ → ℝ

variable {B : Type} [MeasurableSpace B]

/-- Definition 5 (regular allocation function), with `ℝ₊ = [0, ∞)`: `ω` maps `ℝ₊` into `[0, 1]`,
is smooth on `(0, ∞)`, concave and non-decreasing on `ℝ₊`, `lim_{x→0} ω(x) = 0`,
`lim_{x→∞} ω(x) ≤ 1` and `lim_{x→0} ω′(x) ≤ 1`. -/
def IsRegularAllocation (ω : ℝ → ℝ) : Prop :=
  (∀ x, 0 ≤ x → ω x ∈ Set.Icc (0 : ℝ) 1) ∧
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω (Set.Ioi 0) ∧
  ConcaveOn ℝ (Set.Ici 0) ω ∧ MonotoneOn ω (Set.Ici 0) ∧
  Tendsto ω (𝓝[>] 0) (𝓝 0) ∧
  (∃ L ≤ (1 : ℝ), Tendsto ω atTop (𝓝 L)) ∧
  (∃ L ≤ (1 : ℝ), Tendsto (deriv ω) (𝓝[>] 0) (𝓝 L))

/-- The standing assumptions of §3 for one state `a`: the demand conditions (3.1)–(3.2),
Definition 5 for `ω`, Assumption 1 for `Ω` and `l`, Assumption 2 for the choice functions, and
the part of Assumption 3 that concerns `r`; plus the disclosed choices `d_a > 0` and joint
measurability of the primitives. -/
def Market.Standing (M : Market B) : Prop :=
  -- `{d_a} ⊂ ℝ₊`, read as `d_a > 0`
  0 < M.d ∧
  -- demand: probability laws on `[0, ∞)` with `𝔼[D/n] = d_a` (for `n ≥ 1`)
  (∀ n, IsProbabilityMeasure (M.F n) ∧ M.F n (Set.Iio 0) = 0) ∧
  (∀ n : ℕ, 1 ≤ n → Integrable (fun D : ℝ => D) (M.F n) ∧ ∫ D, D / n ∂(M.F n) = M.d) ∧
  -- (3.1): `𝔼[(D/n − d_a)²] → 0`
  Tendsto (fun n : ℕ => ∫⁻ D, ENNReal.ofReal ((D / n - M.d) ^ 2) ∂(M.F n)) atTop (𝓝 0) ∧
  -- (3.2): `ℙ(D/n ∉ [d_a/2, 2 d_a]) = o(1/n)`
  Tendsto (fun n : ℕ => (n : ENNReal) * M.F n {D | D / n ∉ Set.Icc (M.d / 2) (2 * M.d)})
    atTop (𝓝 0) ∧
  -- the private features
  IsProbabilityMeasure M.β ∧
  -- Definition 5
  IsRegularAllocation M.ω ∧
  -- Assumption 1 (on `ℝ₊ × ℝ₊`)
  (∀ d d' t, 0 ≤ d → d ≤ d' → 0 ≤ t → M.Ω d t ≤ M.Ω d' t) ∧
  (∀ d t t', 0 ≤ d → 0 ≤ t → t ≤ t' → M.Ω d t' ≤ M.Ω d t) ∧
  (∃ K : ℝ, ∀ d t, 0 ≤ d → 0 ≤ t → 0 ≤ M.l d t ∧ M.l d t ≤ K) ∧
  (∀ ε > 0, ∃ K : ℝ, ∀ d t, K ≤ d → K ≤ t →
      |M.l d t| ≤ ε * (1 / Real.sqrt t + 1 / Real.sqrt d)) ∧
  (∀ d t, 0 ≤ d → 0 ≤ t → M.Ω d t = M.ω (d / t) + M.l d t) ∧
  (∀ t, Measurable (fun d => M.Ω d t)) ∧
  -- Assumption 2 (on `ℝ₊`)
  (∀ b x, 0 ≤ x → M.f b x ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ b, MonotoneOn (M.f b) (Set.Ici 0)) ∧
  (∀ b x, 0 ≤ x → HasDerivWithinAt (M.f b) (M.f' b x) (Set.Ici 0) x ∧
      HasDerivWithinAt (M.f' b) (M.f'' b x) (Set.Ici 0) x) ∧
  (∃ K : ℝ, ∀ b x, 0 ≤ x → |M.f'' b x| ≤ K) ∧
  Measurable (Function.uncurry M.f) ∧ Measurable (Function.uncurry M.f') ∧
  -- Assumption 3, the part on `r`
  (∀ x, 0 ≤ x → 0 ≤ M.r x) ∧
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M.r (Set.Ioi 0) ∧
  (∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ x, 0 < x → |iteratedDerivWithin k M.r (Set.Ioi 0) x| ≤ C)

/-- (3.12): `q_a^{(n)}(μ) = 𝔼[Ω(D, X)]`, `X ∼ Binomial(n, μ)` independent of `D ∼ F_a^{(n)}`,
written as the binomial sum. -/
noncomputable def Market.q (M : Market B) (n : ℕ) (μ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℝ) * μ ^ k * (1 - μ) ^ (n - k) * ∫ D, M.Ω D k ∂(M.F n)

/-- (A.1): `ψ_a^{(n)}(μ, π) = 𝔼[f_{B_1}(P_1 q_a^{(n)}(μ))]`, `B_1 ∼ β`, `P_1 ∼ π` independent. -/
noncomputable def Market.psi (M : Market B) (n : ℕ) (π : Measure ℝ) (μ : ℝ) : ℝ :=
  ∫ b, ∫ P, M.f b (P * M.q n μ) ∂π ∂M.β

/-- `π_{p,ζ}`: payments `p + ζ ε` with `ε = ±1` with probability `1/2` each, (3.11). -/
noncomputable def perturbLaw (p ζ : ℝ) : Measure ℝ :=
  (1 / 2 : ENNReal) • (Measure.dirac (p + ζ) + Measure.dirac (p - ζ))

/-- `μ_a^{(n)}(π)`: the solution in `[0, 1]` of the balance equation (A.2), `ψ_a^{(n)}(μ, π) = μ`
(it exists and is unique by Lemma 1; the value `0` is used only if there is none). -/
noncomputable def Market.muN (M : Market B) (n : ℕ) (π : Measure ℝ) : ℝ :=
  if h : ∃ μ ∈ Set.Icc (0 : ℝ) 1, M.psi n π μ = μ then h.choose else 0

/-- `ω̄ = sup_{x ≥ 0} ω(x)` (`= lim_{x→∞} ω(x)` for a regular allocation function). -/
noncomputable def Market.omegaSup (M : Market B) : ℝ := sSup (M.ω '' Set.Ici 0)

/-- `μ_a(p)`: the solution in `(0, 1]` of `μ = 𝔼[f_{B_1}(p ω(d_a/μ))]` (Lemma 2; unique when it
exists; the value `0` is used only if there is none). -/
noncomputable def Market.muLim (M : Market B) (p : ℝ) : ℝ :=
  if h : ∃ μ ∈ Set.Ioc (0 : ℝ) 1, μ = ∫ b, M.f b (p * M.ω (M.d / μ)) ∂M.β then h.choose else 0

/-- `u_a(p) = (r(d_a/μ_a(p)) − p ω(d_a/μ_a(p))) μ_a(p)`, the right-hand side of (3.15). -/
noncomputable def Market.u (M : Market B) (p : ℝ) : ℝ :=
  (M.r (M.d / M.muLim p) - p * M.ω (M.d / M.muLim p)) * M.muLim p

/-- (3.17): `Δ_a^{(n)}(p) = q_a^{(n)}(μ_a^{(n)}(p)) 𝔼[f′_{B_1}(p q_a^{(n)}(μ_a^{(n)}(p)))]`. -/
noncomputable def Market.DeltaN (M : Market B) (n : ℕ) (p : ℝ) : ℝ :=
  M.q n (M.muN n (Measure.dirac p)) *
    ∫ b, M.f' b (p * M.q n (M.muN n (Measure.dirac p))) ∂M.β

/-- (3.19): `Δ_a(p) = ω(d_a/μ_a(p)) 𝔼[f′_{B_1}(p ω(d_a/μ_a(p)))]`. -/
noncomputable def Market.DeltaLim (M : Market B) (p : ℝ) : ℝ :=
  M.ω (M.d / M.muLim p) * ∫ b, M.f' b (p * M.ω (M.d / M.muLim p)) ∂M.β

/-- (3.20): `μ′_a(p) = Δ_a(p) / (1 + p d_a Δ_a(p) ω′(d_a/μ_a(p)) / (μ_a(p)² ω(d_a/μ_a(p))))`. -/
noncomputable def Market.muLimDeriv (M : Market B) (p : ℝ) : ℝ :=
  M.DeltaLim p / (1 + p * M.d * M.DeltaLim p * deriv M.ω (M.d / M.muLim p) /
    (M.muLim p ^ 2 * M.ω (M.d / M.muLim p)))

/-- An outcome of the `n`-th one-period experiment: the demand `D` and, per supplier `i`,
`(B_i, P_i, U_i)`. -/
abbrev Outcome (B : Type) (n : ℕ) := ℝ × (Fin n → B × ℝ × ℝ)

/-- The law of the `n`-th experiment under payment law `π`: `D ∼ F_a^{(n)}` and, independently for
each supplier, `B_i ∼ β`, `P_i ∼ π`, `U_i ∼ Uniform[0, 1]`, all independent. -/
noncomputable def Market.sample (M : Market B) (n : ℕ) (π : Measure ℝ) : Measure (Outcome B n) :=
  (M.F n).prod (Measure.pi fun _ : Fin n =>
    M.β.prod (π.prod (volume.restrict (Set.Icc (0 : ℝ) 1))))

/-- `Z_i`: supplier `i` is active (`1`) iff `U_i ≤ f_{B_i}(P_i q_a^{(n)}(μ_a^{(n)}(π)))`, which
realizes the choice model (3.6) at the equilibrium of Lemma 1. -/
noncomputable def Market.Z (M : Market B) (n : ℕ) (π : Measure ℝ) (x : Outcome B n) (i : Fin n) :
    ℝ :=
  if (x.2 i).2.2 ≤ M.f (x.2 i).1 ((x.2 i).2.1 * M.q n (M.muN n π)) then 1 else 0

/-- `D̄ = D/n`. -/
noncomputable def Dbar (n : ℕ) (x : Outcome B n) : ℝ := x.1 / n

/-- `ε_i = (P_i − p)/ζ`, the sign of the perturbation of supplier `i` under `π_{p,ζ}`. -/
noncomputable def eps (n : ℕ) (p ζ : ℝ) (x : Outcome B n) (i : Fin n) : ℝ := ((x.2 i).2.1 - p) / ζ

/-- `ε̄ = (1/n) Σ_i ε_i`. -/
noncomputable def epsBar (n : ℕ) (p ζ : ℝ) (x : Outcome B n) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, eps n p ζ x i

/-- `Z̄ = (1/n) Σ_i Z_i` in the experiment with `ζ`-perturbed payments. -/
noncomputable def Market.Zbar (M : Market B) (n : ℕ) (p ζ : ℝ) (x : Outcome B n) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, M.Z n (perturbLaw p ζ) x i

/-- (4.1): `Δ̂ = ζ^{-1} Σ_i (Z_i − Z̄)(ε_i − ε̄) / Σ_i (ε_i − ε̄)²`. -/
noncomputable def Market.DeltaHat (M : Market B) (n : ℕ) (p ζ : ℝ) (x : Outcome B n) : ℝ :=
  ζ⁻¹ * (∑ i, (M.Z n (perturbLaw p ζ) x i - M.Zbar n p ζ x) * (eps n p ζ x i - epsBar n p ζ x)) /
    ∑ i, (eps n p ζ x i - epsBar n p ζ x) ^ 2

/-- (4.2): `Υ̂ = Δ̂ / (1 + p D̄ Δ̂ ω′(D̄/Z̄) / (Z̄² ω(D̄/Z̄)))`. -/
noncomputable def Market.UpsHat (M : Market B) (n : ℕ) (p ζ : ℝ) (x : Outcome B n) : ℝ :=
  M.DeltaHat n p ζ x / (1 + p * Dbar n x * M.DeltaHat n p ζ x *
    deriv M.ω (Dbar n x / M.Zbar n p ζ x) /
    (M.Zbar n p ζ x ^ 2 * M.ω (Dbar n x / M.Zbar n p ζ x)))

/-- (4.3): `Γ̂ = Υ̂ [r(D̄/Z̄) − p ω(D̄/Z̄) − (r′(D̄/Z̄) − p ω′(D̄/Z̄)) D̄/Z̄] − ω(D̄/Z̄) Z̄`. -/
noncomputable def Market.GammaHat (M : Market B) (n : ℕ) (p ζ : ℝ) (x : Outcome B n) : ℝ :=
  M.UpsHat n p ζ x *
      (M.r (Dbar n x / M.Zbar n p ζ x) - p * M.ω (Dbar n x / M.Zbar n p ζ x) -
        (deriv M.r (Dbar n x / M.Zbar n p ζ x) - p * deriv M.ω (Dbar n x / M.Zbar n p ζ x)) *
          (Dbar n x / M.Zbar n p ζ x)) -
    M.ω (Dbar n x / M.Zbar n p ζ x) * M.Zbar n p ζ x

end EquilibriumExperiment.Gradient


