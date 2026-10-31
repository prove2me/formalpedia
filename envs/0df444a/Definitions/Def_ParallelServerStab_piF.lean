-- Prove2me | Definitions.Def_ParallelServerStab_piF
-- name    : ParallelServerStab_piF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:24:21.89831+00:00
-- url     : https://prove2.me/theorems/1af3b492-7795-4896-b639-f5b198d89983
-- title:
--   The front-server birth–death process $Y^F$, its law $\pi^F$, and its uniformization
-- statement:
--   In the proof of Theorem 2 the system splits into one **front server** and $s-1$ back servers. The number of jobs at the front server, $Y^F$, is a birth–death process on $\mathbb Z_+=\{0,1,2,\dots\}$ with
--
--   $$
--   \lambda_0=\lambda,\quad \mu_0=0,\qquad \lambda_n=\lambda(1-p),\quad \mu_n=\mu\quad(n\ge1).
--   $$
--
--   Its candidate stationary law is
--
--   $$
--   \pi^F(0)=\frac{\mu-\lambda+\lambda p}{\mu+\lambda p},\qquad \pi^F(n)=\left(\frac{\lambda(1-p)}{\mu}\right)^{n-1}\frac{\lambda}{\mu}\,\pi^F(0)\quad(n\ge1).
--   $$
--
--   The module also provides:
--
--   1. the jump chain and exit rates of $Y^F$ (`frontJump`, `frontRate`);
--   2. $\pi^F$ as a measure on $\mathbb Z_+$;
--   3. the law of an $\mathbb Z_+$-valued random variable through its point masses;
--   4. the uniformized kernel of a birth–death process at a clock rate $\Lambda$: $K(n,n+1)=\lambda_n/\Lambda$, $K(n,n-1)=\mu_n/\Lambda$ ($n\ge1$), $K(n,n)=1-(\lambda_n+\mu_n)/\Lambda$, and the kernel of $Y^F$ at $\Lambda=\lambda+\mu$.
--
--   These objects state (15) and (16), the front-server facts on which the proof of Theorem 2 rests.
--
--   **Formalization Note** The paper prints the second formula of $\pi^F$ for $i\ge2$; it holds at $i=1$ (balance at $0$) and (15) needs it there, so it is defined for every $n\ge1$. `frontDeath μ 0 = μ` is never read: the death rate at $0$ is $0$ in `frontRate` and `frontJump`, and the balance equations never use $\mu_0$. The continuous-time process is realized by uniformization at rate $\lambda+\mu$, which bounds the exit rates $\lambda$ and $\lambda(1-p)+\mu$ for $p\in[0,1]$. The law of a variable is written through point masses $P(X=n)$, which equals the push-forward measure for measurable $X$.
-- source:
--   Moyal–Perry, Stability of Parallel Server Systems, arXiv:1904.10331v1, §5.3, proof of Theorem 2, p.14 (Y^F, its rates, the display of π^F)

import Mathlib
import Definitions.Def_ParallelServerStab_StableNI

namespace ParallelServerStab

open MeasureTheory
open scoped ENNReal

/-- Birth rates of the front-server process `Y^F` (Moyal–Perry, Stability of Parallel Server
Systems, arXiv:1904.10331v1, §5.3, p. 14: "`Y^F` is a Birth and Death (BD) process on `ℤ₊`
with respective birth and death rates `λ` and `0` at state `0`, and `λ(1 − p)` and `µ` at all
other states"): `λ` at `0`, `λ(1 − p)` at `n ≥ 1`. -/
noncomputable def frontBirth (lam p : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then lam else lam * (1 - p)

/-- Death rates of the front-server process `Y^F` (arXiv:1904.10331v1, §5.3, p. 14): `µ` at
every state `n ≥ 1`.

**Formalization Note.** The value at `n = 0` is `µ` as a function value but is never used:
the death rate at state `0` is `0` (`frontRate`, `frontJump`), and the balance equations of
`QueueingFundamentals.BirthDeath.IsSteadyState` never read `mu 0`. -/
noncomputable def frontDeath (μ : ℝ) (_n : ℕ) : ℝ := μ

/-- Exit rate of `Y^F` at state `n`: `λ` at `0` and `λ(1 − p) + µ` at `n ≥ 1`. -/
noncomputable def frontRate (lam μ p : ℝ) (n : ℕ) : ℝ :=
  frontBirth lam p n + if n = 0 then 0 else frontDeath μ n

/-- Jump chain of the birth–death process `Y^F` (arXiv:1904.10331v1, §5.3, p. 14): from `n`,
a birth (to `n + 1`) with probability proportional to the birth rate and a death (to `n − 1`,
only for `n ≥ 1`) with probability proportional to `µ`. -/
noncomputable def frontJump (lam μ p : ℝ) (n : ℕ) : PMF ℕ :=
  jumpOfRates (E := Bool) (fun b => if b then frontBirth lam p n else if n = 0 then 0 else frontDeath μ n)
    (fun b => if b then n + 1 else n - 1) n

/-- The stationary distribution `π^F` of the front-server process (Moyal–Perry, Stability of
Parallel Server Systems, arXiv:1904.10331v1, §5.3 display before (15), p. 14):
`π^F(0) = (µ − λ + λp)/(µ + λp)` and `π^F(n) = (λ(1 − p)/µ)^{n−1} (λ/µ) π^F(0)` for `n ≥ 1`.

**Formalization Note.** The paper prints the second formula for `i ≥ 2`; it holds at `i = 1`
as well (balance at `0`: `λ π^F(0) = µ π^F(1)`), and (15) needs it there, so it is stated for
every `n ≥ 1`. -/
noncomputable def piF (lam μ p : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then (μ - lam + lam * p) / (μ + lam * p)
  else (lam * (1 - p) / μ) ^ (n - 1) * (lam / μ) * ((μ - lam + lam * p) / (μ + lam * p))

/-- `π^F` as a measure on `ℕ`: the point masses `π^F(n)` (negative values read as `0`). -/
noncomputable def piFMeasure (lam μ p : ℝ) : Measure ℕ :=
  Measure.sum (fun n => ENNReal.ofReal (piF lam μ p n) • Measure.dirac n)

/-- The law of an `ℕ`-valued random variable `X` under `P`, as the measure with point masses
`P(X = n)`.

**Formalization Note.** For measurable `X` (every `X` here is a function of measurable
variables) this is `P.map X`; it is written through point masses so that no measurability
proof of the time-`t` state is needed to state (16). -/
noncomputable def lawNat {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℕ) :
    Measure ℕ :=
  Measure.sum (fun n => P {ω | X ω = n} • Measure.dirac n)

/-- The uniformized transition kernel, at clock rate `Λ`, of a birth–death process on `ℕ` with
birth rates `birth n` and death rates `death n` (`n ≥ 1`; there is no death at `0`):
`K(n, n+1) = birth n / Λ`, `K(n, n−1) = death n / Λ` for `n ≥ 1`, and
`K(n, n) = 1 − (birth n + death n·[n ≥ 1]) / Λ`. Running this chain at the epochs of an
independent Poisson clock of rate `Λ` (`StrictCompatLB.MeanField.IsUniformizedProcess`) gives
the continuous-time birth–death process whenever `Λ` bounds every exit rate. -/
noncomputable def bdUniformKernel (birth death : ℕ → ℝ) (Λ : ℝ) (n m : ℕ) : ℝ :=
  (if m = n + 1 then birth n / Λ else 0) +
    (if n ≠ 0 ∧ m + 1 = n then death n / Λ else 0) +
    (if m = n then 1 - (birth n + if n = 0 then 0 else death n) / Λ else 0)

/-- The uniformized kernel of the front-server process `Y^F` (arXiv:1904.10331v1, §5.3, p. 14)
at clock rate `λ + µ`, which bounds its exit rates `λ` and `λ(1 − p) + µ` for `p ∈ [0, 1]`.

**Formalization Note.** The paper's `Y^F` is a continuous-time BD process; its law at time `t`
is that of the uniformized chain, the standard construction of a bounded-rate CTMC. -/
noncomputable def frontKernel (lam μ p : ℝ) : ℕ → ℕ → ℝ :=
  bdUniformKernel (frontBirth lam p) (frontDeath μ) (lam + μ)

end ParallelServerStab


