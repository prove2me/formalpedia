-- Prove2me | Definitions.Def_QueueingFundamentals_GG1_Lindley
-- name    : QueueingFundamentals_GG1_Lindley
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T19:34:17.631259+00:00
-- url     : https://prove2.me/theorems/7ba00e02-73af-4227-afb7-97a052b85dfb
-- title:
--   The G/G/1 queue on laws — Lindley's recursion, stationary delay, U = S − T and transforms
-- statement:
--   Consider a single-server first-come, first-served queue with general interarrival times and general service times (the G/G/1 queue). The interarrival times $T^{(n)}$ have distribution $A$ and the service times $S^{(n)}$ have distribution $B$; both are **lifetime laws**, that is, probability distributions on $\mathbb R$ with no mass on $(-\infty,0)$. For a distribution $\nu$ on $\mathbb R$ write $F_\nu(t)=\nu((-\infty,t])$ for its cumulative distribution function, $\mathrm E[T]=\int x\,dA(x)$, $\mathrm E[S]=\int x\,dB(x)$, and let the traffic intensity be
--
--   $$
--   \rho=\frac{\lambda}{\mu}=\frac{\mathrm E[S]}{\mathrm E[T]},\qquad \lambda=\frac1{\mathrm E[T]},\ \mu=\frac1{\mathrm E[S]}.
--   $$
--
--   The random variable $U=S-T$, with $S\sim B$ and $T\sim A$ independent, has the law $U$ given by the convolution of $S$ and $-T$. The line delays of successive customers satisfy Lindley's recursion
--
--   $$
--   W_q^{(n+1)}=\max\bigl(0,\;W_q^{(n)}+S^{(n)}-T^{(n)}\bigr),
--   $$
--
--   and since $W_q^{(n)}$ is independent of $(S^{(n)},T^{(n)})$, one step of the recursion maps the law $\nu$ of $W_q^{(n)}$ to the law of $\max(0,W+U)$ with $W\sim\nu$ and $U$ independent. A **stationary delay distribution** is a probability law $\nu$ that this step maps to itself; its CDF is the book's $W_q(t)$.
--
--   The file also fixes the transforms of §6.2: the two-sided Laplace transform $\bar f(s)=\int_{-\infty}^{\infty}e^{-st}f(t)\,dt$ of a function (used for $\overline{W}_q(s)$ and $\overline{W}_q^-(s)$), and the function
--
--   $$
--   W_q^-(t)=\begin{cases}\int_{-\infty}^{t}W_q(t-x)\,dU(x), & t<0,\\ 0, & t\ge 0.\end{cases}
--   $$
--
--   The (two-sided) Laplace–Stieltjes transform $F^*(s)=\int_{-\infty}^{\infty} e^{-sx}\,dF(x)$ of a law, which gives $A^*(s)$, $B^*(s)$ and the book's two-sided $U^*(s)$, is the one of the M/G/1 transforms file, imported here. These are the objects of every G/G/1 statement in §6.2 and of the G/E_k/1 characteristic equation of §6.1.
--
--   **Formalization Note** Laws are measures on `ℝ`; independence is encoded by product measures, so `lindleyStep U ν` is the image of `ν ⊗ U` under `(w, u) ↦ max 0 (w + u)` and `diffLaw A B` the image of `B ⊗ A` under `(s, t) ↦ s − t`. Stieltjes integrals over $(-\infty,t]$ are Lebesgue integrals over `Set.Iic t`, so the endpoint $x=t$ (where $W_q(0)=q_0$ may be positive) is included. `meanOf`, `twoSidedLaplace` and the imported `QueueingFundamentals.MG1.lst` are Bochner integrals and return `0` for non-integrable integrands; every theorem that uses them assumes or implies integrability.
-- source:
--   Gross, Shortle, Thompson & Harris, Fundamentals of Queueing Theory, 4th ed., Wiley 2008, DOI 10.1002/9781118625651, pp.284–285, §6.2, the recursion of p.284, Eqs. (6.8)–(6.10) and the transforms of p.285

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms

namespace QueueingFundamentals.GG1

open MeasureTheory

/-- A **lifetime law**: a probability measure on `ℝ` that puts no mass on `(-∞, 0)`. The
interarrival-time distribution `A` and the service-time distribution `B` of the G/G/1 queue are
lifetime laws (p.284). -/
def IsLifetimeLaw (A : Measure ℝ) : Prop :=
  IsProbabilityMeasure A ∧ A (Set.Iio 0) = 0

/-- The cumulative distribution function `F(t) = ν((-∞, t])` of a measure `ν` on `ℝ`. For the
stationary delay law `ν` this is the book's `W_q(t)`; for `B` it is `B(t)`. -/
noncomputable def cdfOf (ν : Measure ℝ) (t : ℝ) : ℝ :=
  ν.real (Set.Iic t)

/-- The mean `∫ x dA(x)` of a law on `ℝ` (a Bochner integral: `0` when the identity is not
integrable, so every theorem using it assumes integrability). `E[T] = meanOf A`, `E[S] = meanOf B`. -/
noncomputable def meanOf (A : Measure ℝ) : ℝ :=
  ∫ x, x ∂A

/-- The traffic intensity `ρ = λ/μ = E[S]/E[T]` of the G/G/1 queue, with `λ = 1/E[T]` and
`μ = 1/E[S]`, for interarrival law `A` and service law `B`. -/
noncomputable def trafficIntensity (A B : Measure ℝ) : ℝ :=
  meanOf B / meanOf A

/-- The law `U` of `U = S − T` for independent `S ~ B` and `T ~ A`, i.e. the convolution of `S`
and `−T` (Eq. (6.9), p.285). Independence is encoded by the product measure `B ⊗ A`. -/
noncomputable def diffLaw (A B : Measure ℝ) : Measure ℝ :=
  (B.prod A).map (fun p : ℝ × ℝ => p.1 - p.2)

/-- One step of Lindley's recursion `W_q^{(n+1)} = max(0, W_q^{(n)} + S^{(n)} − T^{(n)})` (p.284)
on laws: the law of `max(0, W + U)` when `W ~ ν` is independent of `U ~ Ulaw`. -/
noncomputable def lindleyStep (Ulaw ν : Measure ℝ) : Measure ℝ :=
  (ν.prod Ulaw).map (fun p : ℝ × ℝ => max 0 (p.1 + p.2))

/-- `ν` is a **stationary delay distribution** of the G/G/1 queue with interarrival law `A` and
service law `B`: a probability measure that Lindley's recursion maps to itself, i.e. if
`W_q^{(n)} ~ ν` is independent of `S^{(n)} ~ B` and `T^{(n)} ~ A` (themselves independent), then
`W_q^{(n+1)} ~ ν`. -/
def IsStationaryDelay (A B ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ lindleyStep (diffLaw A B) ν = ν

/-- The two-sided Laplace transform `f̄(s) = ∫_{−∞}^{∞} e^{−st} f(t) dt` of a real function
(Lebesgue measure; `0` where the integrand is not integrable). -/
noncomputable def twoSidedLaplace (f : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-s * (t : ℂ)) * (f t : ℂ)

/-- The function `W_q^−(t)` of Eq. (6.10) (p.285), built from a function `W` (the book's `W_q`)
and the law `U`: `W_q^−(t) = ∫_{−∞}^{t} W(t − x) dU(x)` for `t < 0` and `0` for `t ≥ 0`. The
Stieltjes integral over `(−∞, t]` is the Lebesgue integral over `Set.Iic t` against `U`. -/
noncomputable def negPart (Ulaw : Measure ℝ) (W : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t < 0 then ∫ x in Set.Iic t, W (t - x) ∂Ulaw else 0

end QueueingFundamentals.GG1


