-- Prove2me | Definitions.Def_LinParamBandits_PEGE_Model
-- name    : LinParamBandits_PEGE_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:20:34.728984+00:00
-- url     : https://prove2.me/theorems/2add40df-eca9-4afd-b98a-a9989a31e3a0
-- title:
--   Sec. 1.1, Assumption 1, PEGE and SBAR(J) — linear bandit model, the PEGE policy, regret and risk
-- statement:
--   This file fixes the model and the policy of Section 3 of Rusmevichientong and Tsitsiklis, *Linearly Parameterized Bandits*.
--
--   **Arms and rewards.** Let $r \ge 2$. The set of arms is a compact set $\mathcal U_r \subset \mathbb R^r$, with the Euclidean norm. Playing arm $u$ in period $t$ gives the reward
--   $$X^u_t = u'Z + W^u_t,$$
--   where $Z \in \mathbb R^r$ is an unknown parameter and the errors $W^u_t$ are independent of each other and of $Z$; for each arm $u$ they are identically distributed in $t$, with law $\nu_u$ and mean zero.
--
--   **Assumption 1.** For constants $\sigma_0, \bar u, \lambda_0 > 0$:
--   1. (a) for every arm $u$ and every $x \in \mathbb R$, $\mathbb E[e^{xW^u_t}] \le e^{x^2\sigma_0^2/2}$;
--   2. (b) $\|u\| \le \bar u$ for every arm $u$, and $\mathcal U_r$ contains linearly independent arms $b_1, \dots, b_r$ with $\lambda_{\min}\big(\sum_{k=1}^r b_k b_k'\big) \ge \lambda_0$.
--
--   **SBAR($J$).** The arm set satisfies the smooth best arm response condition with parameter $J$ if every $z \ne 0$ has a unique best arm $u^*(z) \in \mathcal U_r$, i.e. a unique maximizer of $v \mapsto v'z$ over $\mathcal U_r$, and $\|u^*(z) - u^*(y)\| \le J\|z - y\|$ for all unit vectors $z, y$.
--
--   **The PEGE policy.** The policy runs in cycles $c = 1, 2, \dots$; cycle $c$ lasts $r + c$ periods. In its first $r$ periods (exploration) it plays $b_1, \dots, b_r$ and observes $X^{b_k}(c) = b_k'Z + W^{b_k}(c)$. It then forms the ordinary least squares estimate
--   $$\widehat Z(c) = \frac1c \Big(\sum_{k=1}^r b_k b_k'\Big)^{-1} \sum_{s=1}^c \sum_{k=1}^r b_k X^{b_k}(s),$$
--   and in the remaining $c$ periods (exploitation) it plays a greedy arm $G(c) \in \arg\max_{v \in \mathcal U_r} v'\widehat Z(c)$, ties broken by an arbitrary measurable rule.
--
--   **Regret and risk.** For a parameter value $z$ and a horizon $T$,
--   $$\mathrm{Regret}(z, T, \mathrm{PEGE}) = \sum_{t=1}^T \mathbb E\Big[\max_{v \in \mathcal U_r} v'z - U_t'z \,\Big|\, Z = z\Big], \qquad \mathrm{Risk}(T, \mathrm{PEGE}) = \mathbb E\big[\mathrm{Regret}(Z, T, \mathrm{PEGE})\big],$$
--   where $U_t$ is the arm played in period $t$ and $Z$ is drawn from a prior $\mu$. The file also fixes the normalization $w/\|w\|$ with $0/\|0\|$ a fixed unit vector, the multivariate normal law $N(0, I_r/r)$, and the standard normal error law.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^r$ is `EuclideanSpace ℝ (Fin r)`, and $\lambda_0$ is written `lam₀` (`λ` is reserved in Lean). The condition $\lambda_{\min}(\sum_k b_kb_k') \ge \lambda_0$ is written as the equivalent quadratic-form inequality $\lambda_0\|x\|^2 \le \sum_k (b_k'x)^2$ for all $x$. The noise conditions are required for the arms of $\mathcal U_r$ only; the existence of $\mathbb E[e^{xW}]$ is stated explicitly, so that a non-integrable error cannot satisfy the bound through a default value. PEGE observes only the exploration errors $W^{b_k}(s)$, so the expectation is taken over a table of independent errors $W^{b_k}(s)$ with law $\nu_{b_k}$; this is the paper's model restricted to what the policy sees. "Given $Z = z$" is literal: the errors are integrated with the parameter fixed to $z$. The exploration arms $b_k$ are an argument of the policy, and the greedy rule is any measurable selection of a maximizer, quantified universally in the theorems; measurability is implicit in the paper's expectations. Regret and risk are lower Lebesgue integrals of nonnegative quantities, with values in $[0, \infty]$, so an upper bound on them is never satisfied by a default value. The periods are 0-indexed in Lean.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Sec. 1.1, pp. 3–4 (model, eq. (1), Regret, Risk); Assumption 1, p. 13; PEGE and eq. (2), p. 14; SBAR(J), p. 14; Lemma 3.5, p. 17 (0/‖0‖ convention); Lemma 3.2(b) and Corollary 3.3, p. 16 (N(0, I_r/r), standard normal errors)

import Mathlib
import Definitions.Def_LinParamBandits_LowerBound_Model
import Definitions.Def_LinParamBandits_UEGeneral_Model

namespace LinParamBandits.PEGE

open MeasureTheory ProbabilityTheory

variable {r : ℕ}

/-- `u` is a best arm of `𝒰` for the parameter `z`: `u ∈ 𝒰` and `u′z = max_{v ∈ 𝒰} v′z`. -/
def IsBestArm (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (z u : LinParamBandits.LowerBound.Vec r) : Prop :=
  u ∈ 𝒰 ∧ ∀ v ∈ 𝒰, inner ℝ v z ≤ inner ℝ u z

/-- Assumption 1(a) (p. 13), together with the standing assumption of Sec. 1.1 (p. 3) that every
error has mean zero: for every arm `u ∈ 𝒰` the error law `ν u` (the common law of `W^u_t`, `t ≥ 1`)
has mean zero, and its moment generating function exists and satisfies
`E[e^{x W}] ≤ e^{x² σ₀² / 2}` for every `x ∈ ℝ`. -/
structure NoiseAssumption (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (σ₀ : ℝ) :
    Prop where
  /-- The mean exists. -/
  integrable : ∀ u ∈ 𝒰, Integrable (fun x : ℝ => x) (ν u : Measure ℝ)
  /-- `E[W^u_t] = 0` (Sec. 1.1, p. 3). -/
  mean_zero : ∀ u ∈ 𝒰, ∫ x, x ∂(ν u : Measure ℝ) = 0
  /-- `E[e^{x W^u_t}]` is finite for every `x`. -/
  integrable_exp : ∀ u ∈ 𝒰, ∀ x : ℝ, Integrable (fun w : ℝ => Real.exp (x * w)) (ν u : Measure ℝ)
  /-- `E[e^{x W^u_t}] ≤ e^{x² σ₀² / 2}`. -/
  mgf_le : ∀ u ∈ 𝒰, ∀ x : ℝ,
    ∫ w, Real.exp (x * w) ∂(ν u : Measure ℝ) ≤ Real.exp (x ^ 2 * σ₀ ^ 2 / 2)

/-- The standing assumption of Sec. 1.1 (p. 3) that `𝒰` is compact, and Assumption 1(b) (p. 13):
every arm has norm at most `ū`, and `b_1, …, b_r ∈ 𝒰` are linearly independent with
`λ_min(∑_k b_k b_k′) ≥ λ₀`. The eigenvalue condition is written in its equivalent quadratic-form
version `λ₀ ‖x‖² ≤ x′(∑_k b_k b_k′)x = ∑_k (b_k′x)²` for all `x`. The arms `b_k` are the ones PEGE
explores. -/
structure ArmAssumption (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (b : Fin r → LinParamBandits.LowerBound.Vec r) (ū lam₀ : ℝ) : Prop where
  /-- `𝒰_r` is compact (Sec. 1.1). -/
  isCompact : IsCompact 𝒰
  /-- `max_{u ∈ 𝒰} ‖u‖ ≤ ū`. -/
  norm_le : ∀ u ∈ 𝒰, ‖u‖ ≤ ū
  /-- `b_k ∈ 𝒰`. -/
  mem : ∀ k, b k ∈ 𝒰
  /-- `b_1, …, b_r` are linearly independent. -/
  linearIndependent : LinearIndependent ℝ b
  /-- `λ_min(∑_k b_k b_k′) ≥ λ₀`. -/
  lambdaMin : ∀ x : LinParamBandits.LowerBound.Vec r, lam₀ * ‖x‖ ^ 2 ≤ ∑ k, (inner ℝ (b k) x) ^ 2

/-- Assumption 1 (p. 13) for one dimension `r`, with the constants `σ₀, ū, λ₀`, the noise laws `ν`
and the exploration arms `b`. The theorems quantify the constants before `r`, so the same
constants serve every `r ≥ 2`, as on the page. -/
structure Assumption1 (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r)
    (σ₀ ū lam₀ : ℝ) : Prop where
  noise : NoiseAssumption 𝒰 ν σ₀
  arms : ArmAssumption 𝒰 b ū lam₀

/-- The smooth best arm response condition SBAR(`J`) (p. 14): for every `z ≠ 0` there is a unique
best arm `u*(z) ∈ 𝒰`, and for any two unit vectors `z, y`, `‖u*(z) − u*(y)‖ ≤ J ‖z − y‖`. The
second clause is stated for the best arms `u` of `z` and `v` of `y`, which by the first clause are
`u*(z)` and `u*(y)`. -/
def SBAR (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (J : ℝ) : Prop :=
  (∀ z : LinParamBandits.LowerBound.Vec r, z ≠ 0 → ∃! u, IsBestArm 𝒰 z u) ∧
  (∀ z y u v : LinParamBandits.LowerBound.Vec r, ‖z‖ = 1 → ‖y‖ = 1 → IsBestArm 𝒰 z u → IsBestArm 𝒰 y v →
    ‖u - v‖ ≤ J * ‖z - y‖)

/-- A greedy selection rule (eq. (2), p. 14), ties broken arbitrarily: `g c w` is an arm of `𝒰`
maximizing `v′w` over `v ∈ 𝒰`, chosen in cycle `c` for the estimate `w`. Each map `g c` is
measurable, which the paper's expectations use implicitly. -/
structure GreedySelector (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r) : Prop where
  isBestArm : ∀ c w, IsBestArm 𝒰 w (g c w)
  measurable : ∀ c, Measurable (g c)

/-- A table of exploration errors: `w (s, k)` is `W^{b_k}(s + 1)`, the error of the play of `b_k`
in the exploration phase of cycle `s + 1`. -/
abbrev NoiseTable (r : ℕ) : Type := ℕ × Fin r → ℝ

/-- The law of the exploration errors: independent, `W^{b_k}(s)` with law `ν (b_k)` for every
cycle `s` (Sec. 1.1, p. 3: errors independent, identically distributed in time for each arm). -/
noncomputable def noiseLaw (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r) :
    Measure (NoiseTable r) :=
  Measure.infinitePi (fun p : ℕ × Fin r => (ν (b p.2) : Measure ℝ))

/-- The matrix `∑_{k=1}^r b_k b_k′`. -/
noncomputable def gram (b : Fin r → LinParamBandits.LowerBound.Vec r) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun i j => ∑ k, b k i * b k j

/-- The OLS estimate after the exploration phase of cycle `c ≥ 1` (p. 14):
`Ẑ(c) = (1/c) (∑_k b_k b_k′)⁻¹ ∑_{s=1}^c ∑_k b_k X^{b_k}(s)`, with the observed rewards
`X^{b_k}(s) = b_k′z + W^{b_k}(s)` (eq. (1)) for the parameter value `z`. -/
noncomputable def Zhat (b : Fin r → LinParamBandits.LowerBound.Vec r) (z : LinParamBandits.LowerBound.Vec r) (w : NoiseTable r) (c : ℕ) : LinParamBandits.LowerBound.Vec r :=
  ((c : ℝ)⁻¹) • Matrix.toEuclideanLin (gram b)⁻¹
    (∑ s ∈ Finset.range c, ∑ k, (inner ℝ (b k) z + w (s, k)) • b k)

/-- Locates a period in the cycle schedule. Cycle `c ≥ 1` occupies `r + c` periods. `locate r k t`
returns `(c, j)`: the period with 0-based offset `t` from the start of cycle `k + 1` is slot `j`
(0-based) of cycle `c`. -/
def locate (r : ℕ) (k t : ℕ) : ℕ × ℕ :=
  if t < r + (k + 1) then (k + 1, t) else locate r (k + 1) (t - (r + (k + 1)))
termination_by t
decreasing_by omega

/-- The arm PEGE plays in period `t + 1` (0-based index `t`), for the parameter value `z` and the
exploration errors `w` (p. 14). In slot `j < r` of cycle `c` it plays `b_{j+1}` (exploration); in the
remaining `c` slots it plays the greedy arm `G(c) = g c (Ẑ(c))` (exploitation). -/
noncomputable def armAt (b : Fin r → LinParamBandits.LowerBound.Vec r) (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r) (z : LinParamBandits.LowerBound.Vec r)
    (w : NoiseTable r) (t : ℕ) : LinParamBandits.LowerBound.Vec r :=
  if h : (locate r 0 t).2 < r then b ⟨(locate r 0 t).2, h⟩
  else g (locate r 0 t).1 (Zhat b z w (locate r 0 t).1)

/-- `Regret(z, T, PEGE)` (p. 3): `∑_{t=1}^T E[max_{v ∈ 𝒰} v′z − U_t′z | Z = z]`, the expectation
taken over the errors with the parameter fixed to `z`. Each gap is nonnegative, so the regret is
the lower Lebesgue integral of the nonnegative total gap, a value in `[0, ∞]`. -/
noncomputable def regret (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ) (b : Fin r → LinParamBandits.LowerBound.Vec r)
    (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r) (z : LinParamBandits.LowerBound.Vec r) (T : ℕ) : ENNReal :=
  ∫⁻ w, ENNReal.ofReal (∑ t ∈ Finset.range T, (LinParamBandits.UEGeneral.bestValue 𝒰 z - inner ℝ (armAt b g z w t) z))
    ∂(noiseLaw ν b)

/-- `Risk(T, PEGE) = E[Regret(Z, T, PEGE)]` (p. 4), `Z` drawn from the prior `μ`, independent of
the errors. -/
noncomputable def risk (μ : Measure (LinParamBandits.LowerBound.Vec r)) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (ν : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (g : ℕ → LinParamBandits.LowerBound.Vec r → LinParamBandits.LowerBound.Vec r) (T : ℕ) : ENNReal :=
  ∫⁻ z, regret 𝒰 ν b g z T ∂μ

/-- The normalization `w / ‖w‖` of Lemma 3.5 (p. 17), with the convention that `0 / ‖0‖` is a fixed
unit vector `e`. -/
noncomputable def normalize (e w : LinParamBandits.LowerBound.Vec r) : LinParamBandits.LowerBound.Vec r :=
  if w = 0 then e else ‖w‖⁻¹ • w

/-- The multivariate normal law `N(0, I_r / r)` on `ℝ^r` (Lemma 3.2(b) and Corollary 3.3, p. 16),
written as the law of `Y / √r` with `Y` standard normal on `ℝ^r`. -/
noncomputable def gaussPrior (r : ℕ) : Measure (LinParamBandits.LowerBound.Vec r) :=
  (stdGaussian (LinParamBandits.LowerBound.Vec r)).map (fun y => (Real.sqrt r)⁻¹ • y)

/-- The standard normal error law of Corollary 3.3 (p. 16), the same for every arm. -/
noncomputable def stdNormalNoise : LinParamBandits.LowerBound.Vec r → ProbabilityMeasure ℝ :=
  fun _ => ⟨gaussianReal 0 1, inferInstance⟩

end LinParamBandits.PEGE


