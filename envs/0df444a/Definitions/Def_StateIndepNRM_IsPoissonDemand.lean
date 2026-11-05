-- Prove2me | Definitions.Def_StateIndepNRM_IsPoissonDemand
-- name    : StateIndepNRM_IsPoissonDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:36:13.722686+00:00
-- url     : https://prove2.me/theorems/08874028-62b8-4758-905a-983b9ecca2e8
-- title:
--   Non-homogeneous multivariate Poisson process on $[0,T]$ with respect to a filtration
-- statement:
--   Let $(\Omega,\mathcal F,P)$ carry a filtration $(\mathcal F_t)_{t\in[0,T]}$. A family $X=(X_1,\dots,X_N)$ of $\mathbb N$-valued processes is a **non-homogeneous multivariate Poisson process** with rate vector $\lambda_t$ on $[0,T]$ if
--
--   1. the rates are nonnegative and integrable on $[0,T]$;
--   2. each $X_n$ is adapted, and every path starts at $0$, is nondecreasing and is right-continuous;
--   3. for $0\le s\le t\le T$ the increment $X_n(t)-X_n(s)$ is independent of $\mathcal F_s$ and Poisson distributed with mean $\int_s^t\lambda_{n,v}\,dv$;
--   4. the processes $X_1,\dots,X_N$ are independent.
--
--   This is the demand process along which the make-to-stock policy is run. The module also defines **counting paths**: the path conditions of item 2.
--
--   **Formalization Note** The filtration is indexed by `Set.Icc 0 T`, so nothing is required after $T$. Every path, not only almost every path, is a counting path: this makes stock-out times stopping times without completing the filtration, and such a process exists on the canonical space of counting paths. Unit jumps are not listed because they follow almost surely from item 3. The published `WolffPASTA.Main.IsPoissonProcessWithIntensity` lives on $[0,\infty)$ without a filtration, so it is not this object.
-- source:
--   Manchiraju–Dawande–Janakiraman, A Note on State-Independent Policies in Network Revenue Management, SSRN 3831496, §3, p.7 (non-homogenous multivariate Poisson process with rate vector λ*_t)

import Mathlib

open MeasureTheory ProbabilityTheory Set

namespace StateIndepNRM

/-- The sample-path part of a sales or demand process on `[0, T]`: it starts at `0`, is
nondecreasing, and is right-continuous (Manchiraju–Dawande–Janakiraman, SSRN 3831496, §3, p.7).

**Formalization Note.** Only times in `[0, T]` are constrained; values of `x` outside `[0, T]`
are never read. Right-continuity is asked on `[0, T)`, where it has content. -/
structure IsCountingPath (T : ℝ) (x : ℝ → ℕ) : Prop where
  zero : x 0 = 0
  mono : MonotoneOn x (Icc 0 T)
  rightCont : ∀ t ∈ Ico 0 T, ContinuousWithinAt x (Ici t) t

/-- A non-homogeneous multivariate Poisson process on `[0, T]` with rate vector `rate t` at time
`t`, relative to the filtration `𝓕` (Manchiraju–Dawande–Janakiraman, SSRN 3831496, §3, p.7:
"for any n, {Xₙ(t) : 0 ≤ t ≤ T} is a non-homogenous Poisson process with rate λ*ₙ,ₜ at time t, and
these processes are independent across n").

For each coordinate `n` and `s ≤ t` in `[0, T]`, the increment `X n t - X n s` is independent of
`𝓕 s` and Poisson with mean `∫ₛᵗ rate v n dv`; the `N` coordinate processes are independent.

**Formalization Note.** The filtration is indexed by `Set.Icc 0 T`, so nothing is required after
`T`. Every path (not only almost every one) is a counting path: this makes stock-out times
stopping times without completing the filtration, and the process exists with this property on
the canonical space of counting paths. Unit jumps are not listed, since they follow almost surely
from the Poisson increments. The rate is nonnegative and integrable on `[0, T]`, so the means are
true integrals and `Real.toNNReal` loses nothing; `X n t - X n s` is truncated `ℕ` subtraction,
exact because paths are nondecreasing. -/
structure IsPoissonDemand {N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} (T : ℝ)
    (rate : ℝ → Fin N → ℝ) (𝓕 : Filtration (Icc (0 : ℝ) T) mΩ) (X : Fin N → ℝ → Ω → ℕ)
    (P : Measure Ω) : Prop where
  rate_nonneg : ∀ t ∈ Icc 0 T, ∀ n, 0 ≤ rate t n
  rate_integrable : ∀ n, IntervalIntegrable (fun t => rate t n) volume 0 T
  adapted : ∀ n, StronglyAdapted 𝓕 (fun (t : Icc (0 : ℝ) T) ω => X n t ω)
  path : ∀ n ω, IsCountingPath T (fun t => X n t ω)
  increment_indep : ∀ n, ∀ s t : Icc (0 : ℝ) T, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω => X n t ω - X n s ω) ⊤) (𝓕 s) P
  increment_law : ∀ n, ∀ s t : Icc (0 : ℝ) T, s ≤ t →
    P.map (fun ω => X n t ω - X n s ω) =
      poissonMeasure (Real.toNNReal (∫ v in (s : ℝ)..t, rate v n))
  indep_across : iIndepFun (fun n ω (t : Icc (0 : ℝ) T) => X n t ω) P

end StateIndepNRM


