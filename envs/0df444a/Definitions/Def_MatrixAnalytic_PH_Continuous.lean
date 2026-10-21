-- Prove2me | Definitions.Def_MatrixAnalytic_PH_Continuous
-- name    : MatrixAnalytic_PH_Continuous
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:39:50.249972+00:00
-- url     : https://prove2.me/theorems/9c56a788-388a-4ec8-99ed-b46a343b1240
-- title:
--   Continuous PH representations $(\tau, T)$, the absorbing generator (2.3), its transition function $\exp(Qx)$, absorption and expected sojourn times
-- statement:
--   Fix a finite set of **phases** (in the book $\{1, \dots, n\}$) and adjoin an absorbing state $0$. Let $T$ be a real matrix indexed by the phases and $\boldsymbol\tau$ a real row vector indexed by the phases. Write $\mathbf 1$ for the all-ones column vector and set
--   $$\boldsymbol t = -T\mathbf 1, \qquad \tau_0 = 1 - \boldsymbol\tau\mathbf 1,$$
--   so that (2.5) $T\mathbf 1 + \boldsymbol t = \mathbf 0$ and (2.6) $\tau_0 + \boldsymbol\tau\mathbf 1 = 1$ hold by construction (the book notes that $\boldsymbol t$ and $\tau_0$ are implicitly given by $T$ and $\boldsymbol\tau$). The file defines, following pp. 39–44 of Latouche and Ramaswami:
--
--   1. $T$ is a **PH rate matrix** if it satisfies (2.4): $T_{ii} < 0$ for every phase $i$, $T_{ij} \ge 0$ for $i \ne j$, and $t_i \ge 0$ for every $i$.
--   2. $(\boldsymbol\tau, T)$ is a **PH representation** if moreover $\boldsymbol\tau \ge 0$ and $\tau_0 \ge 0$, so that $(\tau_0, \boldsymbol\tau)$ is a probability vector on $\{0\} \cup \{\text{phases}\}$.
--   3. The **generator** (2.3) of the absorbing Markov process on $\{0\} \cup \{\text{phases}\}$:
--   $$Q = \begin{bmatrix} 0 & \mathbf 0 \\ \boldsymbol t & T \end{bmatrix}.$$
--   4. The **transition function** $P(x) = \exp(Qx)$, with $\exp(A) = \sum_{n \ge 0} A^n / n!$; $P_{ab}(x) = \mathrm P[J(x) = b \mid J(0) = a]$ for the process $J$ with generator $Q$.
--   5. The **distribution function** of the time $X$ until absorption into $0$ when $J(0)$ has distribution $(\tau_0, \boldsymbol\tau)$: since $0$ is absorbing, $X \le x$ exactly when $J(x) = 0$, so
--   $$F(x) = \mathrm P[J(x) = 0] = \tau_0 P_{00}(x) + \sum_i \tau_i P_{i0}(x).$$
--   6. **Absorption with probability 1 from phase $i$**: $P_{i0}(x) \to 1$ as $x \to \infty$.
--   7. $\mathrm{PH}(\boldsymbol\tau, T)$ is **nondefective** if $F(x) \to 1$ as $x \to \infty$ ($F(\infty) = 1$, p. 42).
--   8. The **expected total time in phase $j$** before absorption, starting from phase $i$:
--   $$E_{ij} = \int_0^\infty P_{ij}(x)\,dx \in [0, \infty],$$
--   the expectation of $\int_0^\infty \mathbf 1\{J(x) = j\}\,dx$ given $J(0) = i$.
--
--   These are the objects of Theorems 2.4.1–2.4.3 and of Eq. (2.11).
--
--   **Formalization Note** The phase set is an arbitrary finite type `ι` with decidable equality (the book's $\{1, \dots, n\}$ up to relabelling); the absorbing state $0$ is `none` in `Option ι` and phase $i$ is `some i`. On this finite state space the law of the process is its transition function, which is defined as Mathlib's matrix exponential `NormedSpace.exp (x • Q)`; no path space is built. The expected time $E_{ij}$ is a lower Lebesgue integral in $[0, \infty]$ (`ENNReal`) of `ENNReal.ofReal` of the transition probability, so an infinite expected time is $\infty$ and never a junk real $0$; the entries of $\exp(Qx)$ are nonnegative for a generator, so `ofReal` changes nothing. $F$ is given by the same formula for $x < 0$, where it has no probabilistic meaning; every statement uses it only for $x \ge 0$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 39, Eqs. (2.3)–(2.6) and Definition 2.3.1; pp. 41–42 (transition function, proof of Theorem 2.4.1; nondefectiveness); p. 43 (expected sojourn times, Theorem 2.4.3)

import Mathlib

open Matrix MeasureTheory Filter Topology

namespace MatrixAnalytic.PH

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exit-rate column vector `t = −T𝟙` of a rate matrix `T`, i.e. the vector determined by
(2.5) `T𝟙 + t = 0` (Latouche–Ramaswami, p. 39). -/
def exitRates (T : Matrix ι ι ℝ) : ι → ℝ :=
  -(T *ᵥ fun _ => (1 : ℝ))

/-- `T` is the transient block of a generator of the form (2.3) on `{0} ∪ phases`: conditions
(2.4) `T_ii < 0`, `t_i ≥ 0`, `T_ij ≥ 0` for `i ≠ j`, with `t = −T𝟙` from (2.5) (p. 39). -/
structure IsPHGenerator (T : Matrix ι ι ℝ) : Prop where
  diag_neg : ∀ i, T i i < 0
  offDiag_nonneg : ∀ i j, i ≠ j → 0 ≤ T i j
  exitRates_nonneg : ∀ i, 0 ≤ exitRates T i

/-- The mass `τ₀ = 1 − τ𝟙` that the initial vector `(τ₀, τ)` puts on the absorbing state 0,
determined by (2.6) `τ₀ + τ𝟙 = 1`. -/
def initAtom (τ : ι → ℝ) : ℝ :=
  1 - ∑ i, τ i

/-- `(τ, T)` is a (continuous) PH representation (Definition 2.3.1, p. 39): `T` satisfies (2.4),
(2.5), and `(τ₀, τ)` is a probability vector on `{0} ∪ phases`, i.e. `τ ≥ 0` and
`τ₀ = 1 − τ𝟙 ≥ 0` (2.6). -/
structure IsPHRep (τ : ι → ℝ) (T : Matrix ι ι ℝ) : Prop where
  generator : IsPHGenerator T
  init_nonneg : ∀ i, 0 ≤ τ i
  initAtom_nonneg : 0 ≤ initAtom τ

/-- The infinitesimal generator (2.3) `Q = [[0, 0], [t, T]]` of the absorbing Markov process on
`{0} ∪ phases`; the absorbing state 0 is `none`, phase `i` is `some i`. -/
def generator (T : Matrix ι ι ℝ) : Matrix (Option ι) (Option ι) ℝ :=
  Matrix.of fun a b =>
    match a, b with
    | none, _ => 0
    | some i, none => exitRates T i
    | some i, some j => T i j

/-- The transition function `P(x) = exp(Qx)` of the (finite-state, regular) Markov process with
generator `Q` of (2.3): `P(x)_{ab} = P[J(x) = b | J(0) = a]` (p. 41). -/
noncomputable def transFun (T : Matrix ι ι ℝ) (x : ℝ) : Matrix (Option ι) (Option ι) ℝ :=
  NormedSpace.exp (x • generator T)

/-- The initial probability vector `(τ₀, τ)` on `{0} ∪ phases`. -/
def initDist (τ : ι → ℝ) : Option ι → ℝ
  | none => initAtom τ
  | some i => τ i

/-- The distribution function `F(x) = P[X ≤ x]` of the time `X` until absorption into 0 when the
process starts with distribution `(τ₀, τ)`. Since 0 is absorbing, `X ≤ x` iff `J(x) = 0`, so
`F(x) = P[J(x) = 0] = Σ_a (τ₀, τ)_a P(x)_{a0}` (proof of Theorem 2.4.1, p. 42). Meaningful for
`x ≥ 0`. -/
noncomputable def cdf (τ : ι → ℝ) (T : Matrix ι ι ℝ) (x : ℝ) : ℝ :=
  ∑ a, initDist τ a * transFun T x a none

/-- Starting from phase `i`, absorption into state 0 occurs with probability 1: the probability
`P[J(x) = 0 | J(0) = i]` of having been absorbed by time `x` tends to 1 as `x → ∞`. -/
def AbsorbedAS (T : Matrix ι ι ℝ) (i : ι) : Prop :=
  Tendsto (fun x => transFun T x (some i) none) atTop (𝓝 1)

/-- The PH distribution `PH(τ, T)` is nondefective: `F(∞) = 1`, i.e. absorption occurs in a
finite time almost surely (p. 42). -/
def Nondefective (τ : ι → ℝ) (T : Matrix ι ι ℝ) : Prop :=
  Tendsto (cdf τ T) atTop (𝓝 1)

/-- The expected total time spent in phase `j` before absorption, starting from phase `i`:
`E_ij = E[∫₀^∞ 1{J(x) = j} dx | J(0) = i] = ∫₀^∞ P(x)_{ij} dx`, an extended nonnegative real
(`⊤` when the expected time is infinite). -/
noncomputable def expectedTime (T : Matrix ι ι ℝ) (i j : ι) : ENNReal :=
  ∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (transFun T x (some i) (some j))

end MatrixAnalytic.PH


