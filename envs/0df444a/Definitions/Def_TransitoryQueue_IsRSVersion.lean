-- Prove2me | Definitions.Def_TransitoryQueue_IsRSVersion
-- name    : TransitoryQueue_IsRSVersion
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:01:34.88281+00:00
-- url     : https://prove2.me/theorems/a46dd678-9c75-4821-a2aa-d870c276fdb1
-- title:
--   A version of the RS$(G,p)/G/1$ model with its Gaussian processes
-- statement:
--   A **version** of the model on a probability space $(\Omega,\mathcal F,P)$ consists of triangular arrays $T_{n,i}$, $\zeta_{n,i}$, $V_{n,i}$ ($1\le i\le n$) and processes $B$, $\hat B$, $B^{\mathrm{br},n}$ such that $P$ is a probability measure and, for every $n\ge1$:
--
--   1. $T_{n,1},\dots,T_{n,n}$ are iid with distribution function $F_n$;
--   2. $\zeta_{n,1},\dots,\zeta_{n,n}$ are iid Bernoulli($p$);
--   3. $V_{n,1},\dots,V_{n,n}$ are iid with law $\nu$;
--   4. $B$ and $\hat B$ are standard Brownian motions (the same for all $n$) and $B^{\mathrm{br},n}$ is a Brownian bridge;
--   5. the blocks $(T_{n,\cdot},B^{\mathrm{br},n})$, $(\zeta_{n,\cdot},\hat B)$ and $(V_{n,\cdot},B)$ are mutually independent.
--
--   This is the "version" of §2.2: "Strong approximation results are usually stated in terms of versions of the random variables we wish to approximate … the same version suffices for each theorem below", on a space "rich enough to support the random variables as well as the approximating stochastic processes".
--
--   **Formalization Note** The dependence of the arrays across $n$ is free, as in Assumptions 2.1, 2.5 and 2.7. Brownian motion is Mathlib's `IsBrownianReal` with time in $[0,\infty)$. The block independence (5) is what the paper's construction provides.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Assumptions 2.1, 2.5, 2.7, pp.5–6; §2.2, p.6

import Mathlib
import Definitions.Def_TransitoryQueue_IsBrownianBridge
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TransitoryQueue

/-- A **version** of the RS(G, p)/G/1 model together with its approximating Gaussian processes,
on one probability space `P`. For every system size `n ≥ 1`:

1. the arrival epochs `T n 0, …, T n (n-1)` are iid with distribution function `F n`;
2. the turn-up indicators `ζ n 0, …, ζ n (n-1)` are iid Bernoulli(`p`);
3. the service requirements `V n 0, …, V n (n-1)` are iid with law `ν`;
4. `B` and `Bh` (the paper's `B` and `B̂`) are standard Brownian motions, the same for all `n`,
   and `Bbr n` (the paper's `B^{br,n}`) is a Brownian bridge;
5. the three blocks `(T n, Bbr n)`, `(ζ n, Bh)` and `(V n, B)` are mutually independent.

Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Assumptions 2.1, 2.5 and 2.7, pp.5–6, and §2.2, p.6 ("Strong approximation results are
usually stated in terms of versions of the random variables … the same version suffices for each
theorem below … the underlying probability space is rich enough to support the random variables
as well as the approximating stochastic processes"); Theorems 2.8, 2.10, 2.11, pp.6–8.

**Formalization Note** The arrays are triangular: `T n i`, `ζ n i`, `V n i` with `i : Fin n`; their
dependence across `n` is not constrained, as in the paper. The law of `T n i` is given by its
distribution function, the law of `ζ n i` (valued in `ℕ`) by `P(ζ = 1) = p`, `P(ζ = 0) = 1 - p`.
Brownian motions use Mathlib's `IsBrownianReal`, with time in `ℝ≥0`. The independence of the
three blocks is what the paper's construction provides; it is not printed in the theorem
statements. -/
structure IsRSVersion {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ℕ → ℝ → ℝ) (p : ℝ)
    (ν : Measure ℝ) (T : (n : ℕ) → Fin n → Ω → ℝ) (ζ : (n : ℕ) → Fin n → Ω → ℕ)
    (V : (n : ℕ) → Fin n → Ω → ℝ) (B Bh : ℝ≥0 → Ω → ℝ) (Bbr : ℕ → ℝ → Ω → ℝ) : Prop where
  prob : IsProbabilityMeasure P
  T_meas : ∀ n i, Measurable (T n i)
  T_cdf : ∀ n i (t : ℝ), P {ω | T n i ω ≤ t} = ENNReal.ofReal (F n t)
  T_indep : ∀ n, iIndepFun (T n) P
  ζ_meas : ∀ n i, Measurable (ζ n i)
  ζ_one : ∀ n i, P {ω | ζ n i ω = 1} = ENNReal.ofReal p
  ζ_zero : ∀ n i, P {ω | ζ n i ω = 0} = ENNReal.ofReal (1 - p)
  ζ_indep : ∀ n, iIndepFun (ζ n) P
  V_law : ∀ n i, HasLaw (V n i) ν P
  V_indep : ∀ n, iIndepFun (V n) P
  brownian : IsBrownianReal B P
  brownian_hat : IsBrownianReal Bh P
  bridge : ∀ n, 1 ≤ n → IsBrownianBridge (Bbr n) P
  blocks : ∀ n, 1 ≤ n → iIndep
    ![MeasurableSpace.comap (fun ω => ((fun i => T n i ω), (fun s => Bbr n s ω))) inferInstance,
      MeasurableSpace.comap (fun ω => ((fun i => ζ n i ω), (fun s => Bh s ω))) inferInstance,
      MeasurableSpace.comap (fun ω => ((fun i => V n i ω), (fun s => B s ω))) inferInstance] P

end TransitoryQueue


