-- Prove2me | Definitions.Def_KieferWolfowitz_Convergence_Model
-- name    : KieferWolfowitz_Convergence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:30:10.471624+00:00
-- url     : https://prove2.me/theorems/438ec57c-b6c4-4f18-a9d8-f209d7a2524c
-- title:
--   §2, (2.1)–(2.10): regression function of a kernel, Conditions 1–3, step sizes and the Kiefer–Wolfowitz process (2.7)
-- statement:
--   This file fixes the objects of Kiefer and Wolfowitz's stochastic approximation scheme for locating the maximum of a regression function.
--
--   **Observations and regression function.** For each level $x\in\mathbb R$ let $H(\cdot\mid x)$ be a probability distribution on $\mathbb R$, depending measurably on $x$ (a Markov kernel). An observation taken at level $x$ is a random number with law $H(\cdot\mid x)$. The **regression function** is its mean,
--   $$M(x)=\int_{-\infty}^{\infty} y\,dH(y\mid x). \tag{2.1}$$
--   The **variance bound** (2.2) asks that every $H(\cdot\mid x)$ have a finite second moment and
--   $$\int_{-\infty}^{\infty}(y-M(x))^2\,dH(y\mid x)\le S<\infty$$
--   for one constant $S$. **Unimodality** means that $M$ is strictly increasing on $\{x<\theta\}$ and strictly decreasing on $\{x>\theta\}$.
--
--   **Regularity conditions** on a function $M$ and a point $\theta$:
--
--   1. *Condition 1* with constants $\beta,B>0$: if $x'\neq x''$ and $|x'-\theta|+|x''-\theta|<\beta$, then $|M(x')-M(x'')|<B|x'-x''|$ (2.8).
--   2. *Condition 2* with constants $\rho,R>0$: if $|x'-x''|<\rho$, then $|M(x')-M(x'')|<R$ (2.9).
--   3. *Condition 3*: for every $\delta>0$ there is $\pi(\delta)>0$ such that $|z-\theta|>\delta$ implies $|M(z+\varepsilon)-M(z-\varepsilon)|/\varepsilon>\pi(\delta)$ for every $0<\varepsilon<\delta/2$ (2.10).
--
--   **Step sizes.** $\{a_n\}$ and $\{c_n\}$ are sequences of positive numbers with
--   $$c_n\to0,\qquad \sum a_n=\infty,\qquad \sum a_nc_n<\infty,\qquad \sum a_n^2c_n^{-2}<\infty \tag{2.3–2.6}$$
--   (for example $a_n=n^{-1}$, $c_n=n^{-1/3}$).
--
--   **The process (2.7).** On a probability space $(\Omega,\mathcal F,P)$ with a filtration $(\mathcal F_n)$, a Kiefer–Wolfowitz process started at the number $z_1$ consists of random variables $z_n$, $y_{2n-1}$, $y_{2n}$ such that $z_n$ is $\mathcal F_n$-measurable, $y_{2n-1},y_{2n}$ are $\mathcal F_{n+1}$-measurable,
--   $$z_{n+1}=z_n+a_n\,\frac{y_{2n}-y_{2n-1}}{c_n},$$
--   and, conditionally on $\mathcal F_n$, the observations $y_{2n-1}$ and $y_{2n}$ are independent with laws $H(\cdot\mid z_n-c_n)$ and $H(\cdot\mid z_n+c_n)$:
--   $$P\big(y_{2n-1}\in A,\ y_{2n}\in B\,\big|\,\mathcal F_n\big)=H(A\mid z_n-c_n)\,H(B\mid z_n+c_n)\quad\text{a.s.}$$
--   for all Borel sets $A,B$.
--
--   **Auxiliary quantities of the proof** (§3): $U_n(z)=(z-\theta)\big(M(z+c_n)-M(z-c_n)\big)$ (3.2), its positive and negative parts $U_n^+=\max(U_n,0)$, $U_n^-=\min(U_n,0)$ (3.3), and $K_n=\big|(M(z_n+c_n)-M(z_n-c_n))/c_n\big|$ (3.16).
--
--   These are the shared objects of every statement in the mission.
--
--   **Formalization Note** Indices are 0-based: Lean's `z 0` is the paper's $z_1$, `a n`, `c n` are $a_{n+1}$, $c_{n+1}$, and `yminus n`, `yplus n` are $y_{2n+1}$, $y_{2n+2}$. The family $H$ is a Markov kernel, so measurability in $x$ is assumed; the paper takes expectations of functions of $z_n$ and needs it implicitly. "$S<\infty$" is automatic for a real $S$; the integrability of $y^2$ under each $H(\cdot\mid x)$ is stated so that (2.1) and (2.2) are not Lean's default value $0$. As printed, (2.8) has no $x'\neq x''$, and then its strict inequality fails at $x'=x''$, so the printed condition is unsatisfiable; the hypothesis $x'\neq x''$ is the minimal repair (a Lipschitz condition, as the paper's remark (c) says). The paper writes Condition 3 with $\inf_{\frac12\delta>\varepsilon>0}$; because $\pi(\delta)$ is existential, the pointwise form here is equivalent. The paper's "independent chance variables with respective distributions $H(y\mid z_n\mp c_n)$" is read as the conditional law given the past $\mathcal F_n$, stated on measurable rectangles (which determine the joint conditional law); a general filtration rather than the natural one only widens the class of processes. $z_1$ is a deterministic number. $U_n$ is written through $M$; under the model it equals the paper's $(z-\theta)E\{y_{2n}-y_{2n-1}\mid z_n=z\}$. Conditions 1 and 2 are parametrised by their constants, so statements can name $\beta,B,\rho,R$.
-- source:
--   Kiefer & Wolfowitz, Stochastic estimation of the maximum of a regression function, Ann. Math. Statist. 23 (1952), pp. 462–463, (2.1)–(2.10), (3.2), (3.3); p. 465, (3.16)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace KieferWolfowitz.Convergence

/-- (2.1), Kiefer & Wolfowitz, Ann. Math. Statist. 23 (1952), p. 462: the regression function
`M(x) = ∫ y dH(y | x)` of the family of distributions `H(· | x)`, here a Markov kernel `H : ℝ → ℝ`. -/
noncomputable def regFun (H : Kernel ℝ ℝ) (x : ℝ) : ℝ :=
  ∫ y, y ∂(H x)

/-- (2.2), p. 462: every `H(· | x)` has a finite second moment, and its variance about `M(x)` is at
most `S`. The integrability clause makes `M(x)` and the integral in (2.2) genuine (not Lean's junk
value `0` for a non-integrable function). -/
def SecondMomentBound (H : Kernel ℝ ℝ) (S : ℝ) : Prop :=
  (∀ x, Integrable (fun y : ℝ => y ^ 2) (H x)) ∧
    ∀ x, ∫ y, (y - regFun H x) ^ 2 ∂(H x) ≤ S

/-- p. 462: `M(x)` is strictly increasing for `x < θ` and strictly decreasing for `x > θ`. -/
def Unimodal (M : ℝ → ℝ) (θ : ℝ) : Prop :=
  StrictMonoOn M (Set.Iio θ) ∧ StrictAntiOn M (Set.Ioi θ)

/-- Condition 1, (2.8), p. 463, with the constants `β, B` named:
`|x' − θ| + |x'' − θ| < β` implies `|M(x') − M(x'')| < B |x' − x''|`, for `x' ≠ x''`.
The page omits `x' ≠ x''`; with it omitted the strict inequality fails at `x' = x''`, so the printed
condition is unsatisfiable. The added `x' ≠ x''` is the minimal repair (a Lipschitz condition near `θ`). -/
def Cond1 (M : ℝ → ℝ) (θ β B : ℝ) : Prop :=
  ∀ x' x'' : ℝ, x' ≠ x'' → |x' - θ| + |x'' - θ| < β → |M x' - M x''| < B * |x' - x''|

/-- Condition 2, (2.9), p. 463, with the constants `ρ, R` named:
`|x' − x''| < ρ` implies `|M(x') − M(x'')| < R`. -/
def Cond2 (M : ℝ → ℝ) (ρ R : ℝ) : Prop :=
  ∀ x' x'' : ℝ, |x' - x''| < ρ → |M x' - M x''| < R

/-- Condition 3, (2.10), p. 463: for every `δ > 0` there is `π(δ) > 0` such that `|z − θ| > δ` implies
`|M(z + ε) − M(z − ε)| / ε > π(δ)` for every `0 < ε < δ/2`. The page writes the infimum over
`½δ > ε > 0`; since `π(δ)` is existential, the pointwise form (uniform in `z` and `ε`) is equivalent. -/
def Cond3 (M : ℝ → ℝ) (θ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ π : ℝ, 0 < π ∧
    ∀ z : ℝ, δ < |z - θ| → ∀ ε : ℝ, 0 < ε → ε < δ / 2 → π < |M (z + ε) - M (z - ε)| / ε

/-- p. 462: `{a_n}`, `{c_n}` are sequences of positive numbers with (2.3) `c_n → 0`, (2.4)
`Σ a_n = ∞`, (2.5) `Σ a_n c_n < ∞`, (2.6) `Σ a_n² c_n⁻² < ∞`. Lean index `n` is the paper's `n + 1`. -/
def StepSizes (a c : ℕ → ℝ) : Prop :=
  (∀ n, 0 < a n) ∧ (∀ n, 0 < c n) ∧ Tendsto c atTop (𝓝 0) ∧
    Tendsto (fun N => ∑ n ∈ Finset.range N, a n) atTop atTop ∧
    Summable (fun n => a n * c n) ∧ Summable (fun n => a n ^ 2 / c n ^ 2)

/-- The Kiefer–Wolfowitz process (2.7), p. 462, on a probability space `(Ω, P)` with a filtration `ℱ`
(`ℱ n` = the information available before the `n`-th pair of observations).
Indices are 0-based: `z 0` is the paper's `z₁`, `a n, c n` are `a_{n+1}, c_{n+1}`, and
`yminus n, yplus n` are `y_{2n+1}, y_{2n+2}`, observed at `z_n − c_n` and `z_n + c_n`.

* `init`: `z₁` is an arbitrary (deterministic) number;
* `step`: `z_{n+1} = z_n + a_n (y_{2n} − y_{2n−1}) / c_n`;
* `z n` is `ℱ n`-measurable, the observations of step `n` are `ℱ (n+1)`-measurable;
* `cond_law`: given `ℱ n`, the two observations are independent with laws `H(· | z_n − c_n)` and
  `H(· | z_n + c_n)` (stated on measurable rectangles, which determine the joint conditional law). -/
structure IsKWProcess {Ω : Type*} [mΩ : MeasurableSpace Ω] (H : Kernel ℝ ℝ) (a c : ℕ → ℝ)
    (z₁ : ℝ) (P : Measure Ω) (ℱ : Filtration ℕ mΩ) (z yminus yplus : ℕ → Ω → ℝ) : Prop where
  init : ∀ ω, z 0 ω = z₁
  step : ∀ n ω, z (n + 1) ω = z n ω + a n * (yplus n ω - yminus n ω) / c n
  adapted : ∀ n, Measurable[ℱ n] (z n)
  measurable_yminus : ∀ n, Measurable[ℱ (n + 1)] (yminus n)
  measurable_yplus : ∀ n, Measurable[ℱ (n + 1)] (yplus n)
  cond_law : ∀ (n : ℕ) (A B : Set ℝ), MeasurableSet A → MeasurableSet B →
    P⟦yminus n ⁻¹' A ∩ yplus n ⁻¹' B | ℱ n⟧ =ᵐ[P]
      fun ω => (H (z n ω - c n) A).toReal * (H (z n ω + c n) B).toReal

/-- (3.2), p. 463, written through `M`: `U_n(z) = (z − θ)(M(z + c_n) − M(z − c_n))`, which equals the
paper's `(z − θ) E{y_{2n} − y_{2n−1} | z_n = z}` under the model. Here `c` is the current `c_n`. -/
def U (M : ℝ → ℝ) (θ c z : ℝ) : ℝ :=
  (z - θ) * (M (z + c) - M (z - c))

/-- (3.3), p. 463: `U_n⁺(z) = ½(U_n(z) + |U_n(z)|) = max(U_n(z), 0)`. -/
def Uplus (M : ℝ → ℝ) (θ c z : ℝ) : ℝ :=
  max (U M θ c z) 0

/-- (3.3), p. 463: `U_n⁻(z) = ½(U_n(z) − |U_n(z)|) = min(U_n(z), 0)`. -/
def Uminus (M : ℝ → ℝ) (θ c z : ℝ) : ℝ :=
  min (U M θ c z) 0

/-- (3.16), p. 465: `K_n = |(M(z_n + c_n) − M(z_n − c_n)) / c_n|`, a random variable. -/
noncomputable def K {Ω : Type*} (M : ℝ → ℝ) (c : ℕ → ℝ) (z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  |(M (z n ω + c n) - M (z n ω - c n)) / c n|

end KieferWolfowitz.Convergence


