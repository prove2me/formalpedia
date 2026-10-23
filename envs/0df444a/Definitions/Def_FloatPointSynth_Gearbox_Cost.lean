-- Prove2me | Definitions.Def_FloatPointSynth_Gearbox_Cost
-- name    : FloatPointSynth_Gearbox_Cost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:59:30.939142+00:00
-- url     : https://prove2.me/theorems/687a6a24-4c6c-46a2-9877-567f00a26aa2
-- title:
--   Repeat-until-success cost of C◦d(U): geometric trial counts, the law of x_d from (A1), n_d = 2x_d, and P_q of Theorem 2 (Appendix A)
-- statement:
--   This file defines the random number of applications of $U$ and $U^\dagger$ used by the composed gearbox circuit, following Appendix A.
--
--   1. **Trial counts.** For a success probability $p\in(0,1]$, $\mathrm{Geom}_{\ge1}(p)$ is the law on $\{1,2,\dots\}$ of the number of independent trials up to and including the first success, $\Pr(N=k)=(1-p)^{k-1}p$.
--   2. **Independent sums.** For a law $\mu$ on $\mathbb N$ and $k\in\mathbb N$, $\mu^{*k}$ is the law of the sum of $k$ independent draws from $\mu$.
--   3. **The law of $x_d$** (eq. (A1)). $x_d$ is the number of applications of $C^{\circ1}(U)$ before $C^{\circ d}(U)$ succeeds. $x_1=N_1\sim\mathrm{Geom}_{\ge1}(p_1(U))$, and for $d\ge2$
--   $$x_d=\sum_{i=1}^{N_d}(\eta_i+\chi_i),$$
--   where $N_d\sim\mathrm{Geom}_{\ge1}(p_d(U))$, the $\eta_i,\chi_i$ are distributed as $x_{d-1}$, and all are independent. So the law of $x_d$ is the mixture over $N_d$ of $(\text{law of }x_{d-1})^{*2N_d}$. Here $p_q(U)$ is the level success probability computed from the circuit.
--   4. **The law of $n_d$.** Each $C^{\circ1}(U)$ uses one $U$ and one $U^\dagger$, so $n_d=2x_d$.
--   5. **Moments.** For a law $\mu$ on $\mathbb N$, $\mathbb E(\mu)=\sum_n n\,\mu(n)\in[0,\infty]$ and $\mathbb V(\mu)=\sum_n\mu(n)\,(n-\mathbb E(\mu))^2\in[0,\infty]$.
--   6. **Theorem 2's closed forms.** For $q\ge1$,
--   $$\varphi_q:=\tan^{-1}\big(\tan^{2^{q-1}}(\theta_0)\big),\qquad P_q:=\sin^4(\varphi_q)+\cos^4(\varphi_q).$$
--
--   The law of $n_d$ is the random variable of Theorem 2, and $P_q$ is the closed form its moments are expressed in; the law itself never uses $P_q$.
--
--   **Formalization Note** Laws are Mathlib `PMF ℕ`; independence is built into the monadic `bind`. The geometric law is Mathlib's `geometricMeasure` (failures before the first success) shifted by one. For $p\notin(0,1]$ (never the case for unitary $U$) $\mathrm{Geom}_{\ge1}(p)$ is the point mass at $1$. Moments are `ℝ≥0∞`-valued sums, so a divergent mean or variance is $\infty$, never a junk $0$; inside the variance the mean enters through `toReal`, which is the true mean whenever the mean is finite (if it were $\infty$ it would be read as $0$). The law of $x_0$ is the point mass at $0$ and is never used. At $\theta_0=\pi/2$ Lean's `Real.tan` returns $0$, so $P_q=1$, which is also the true value $\sin^4(\pi/2)+\cos^4(\pi/2)$.
-- source:
--   Wiebe and Kliuchnikov, Floating Point Representations in Quantum Circuit Synthesis, arXiv:1305.5528v3, p. 6, Theorem 2 (P_q, φ_q, n_d); pp. 14–15, Appendix A, Eq. (A1), n_d = 2x_d

import Mathlib
import Definitions.Def_FloatPointSynth_Gearbox_Circuit

namespace FloatPointSynth.Gearbox

open scoped ENNReal

/-- The number of trials up to and including the first success, for success probability `p`:
the geometric law on `{1, 2, …}` with `P(N = k) = (1 - p)^{k-1} p`. Outside `0 < p ≤ 1` (never
reached for the circuit's level probabilities) the value is the point mass at `1`. It is the
shift by one of Mathlib's `geometricMeasure`, which counts the failures before the first
success (`P(n) = (1 - p)^n p` on `{0, 1, …}`). -/
noncomputable def geomPos (p : ℝ) : PMF ℕ :=
  if h : 0 < p ∧ p ≤ 1 then
    (ProbabilityTheory.geometricMeasure ⟨p, h.1.le, h.2⟩).toPMF.map Nat.succ
  else PMF.pure 1

/-- The law of the sum of `k` independent draws from `μ`. -/
noncomputable def iidSum (μ : PMF ℕ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | k + 1 => μ.bind fun a => (iidSum μ k).map (a + ·)

/-- The law of `x_d`, the number of applications of `C◦1(U)` before `C◦d(U)` succeeds
(Appendix A, (A1)), for `d ≥ 1`: `x_1 = N_1`, and
`x_d = ∑_{i=1}^{N_d} (η_i + χ_i)` with `N_d` geometric with the level-`d` success probability and
`η_i, χ_i` independent copies of `x_{d-1}`, all independent; i.e. `x_d` is a sum of `2 N_d`
independent copies of `x_{d-1}`. (`xLaw U 0` is the point mass at `0` and is never used.) -/
noncomputable def xLaw (U : Matrix (Fin 2) (Fin 2) ℂ) : ℕ → PMF ℕ
  | 0 => PMF.pure 0
  | 1 => geomPos (levelProb U 1)
  | q + 2 => (geomPos (levelProb U (q + 2))).bind fun N => iidSum (xLaw U (q + 1)) (2 * N)

/-- The law of `n_d = 2 x_d`, the number of applications of `U` or `U†` used to enact `C◦d(U)`
(each `C◦1(U)` uses one `U` and one `U†`). -/
noncomputable def nLaw (U : Matrix (Fin 2) (Fin 2) ℂ) (d : ℕ) : PMF ℕ :=
  (xLaw U d).map (2 * ·)

/-- The mean `∑ n μ(n)` of a law on `ℕ`, in `[0, ∞]`. -/
noncomputable def pmfMean (μ : PMF ℕ) : ℝ≥0∞ :=
  ∑' n, μ n * (n : ℝ≥0∞)

/-- The variance `∑ μ(n) (n - E)^2` of a law on `ℕ`, in `[0, ∞]`, with `E` the mean. (It is the
variance whenever the mean is finite; if the mean is `∞`, `E` is read as `0`.) -/
noncomputable def pmfVar (μ : PMF ℕ) : ℝ≥0∞ :=
  ∑' n, μ n * ENNReal.ofReal (((n : ℝ) - (pmfMean μ).toReal) ^ 2)

/-- `φ_q := tan⁻¹(tan^{2^{q-1}}(θ0))` of Theorem 2. -/
noncomputable def phi (θ0 : ℝ) (q : ℕ) : ℝ :=
  Real.arctan (Real.tan θ0 ^ (2 ^ (q - 1)))

/-- `P_q := sin⁴(φ_q) + cos⁴(φ_q)` of Theorem 2. -/
noncomputable def P (θ0 : ℝ) (q : ℕ) : ℝ :=
  Real.sin (phi θ0 q) ^ 4 + Real.cos (phi θ0 q) ^ 4

end FloatPointSynth.Gearbox


