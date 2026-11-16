-- Prove2me | Definitions.Def_FracTruthSched_Supplement_ebsExpectedMakespan
-- name    : FracTruthSched_Supplement_ebsExpectedMakespan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:16:38.554569+00:00
-- url     : https://prove2.me/theorems/9e126237-6201-4633-b355-d4f7f3de54d4
-- title:
--   Expected makespan $\mathbb E[\mathrm{Mech}_{\mathrm{EBS}}(t)]$ of Exp-Bounded-Square
-- statement:
--   For an instance $t$, let $R_i(t)$ be the random set of tasks Exp-Bounded-Square assigns to machine $i$, $\theta_i(t)=\sum_{j\in R_i(t)}t_{ij}$ its load, and
--   $$\mathrm{Mech}_{\mathrm{EBS}}(t)=\max_i\theta_i(t)$$
--   the makespan of the random allocation. The randomness consists of weights $E_{ij}\sim\mathrm{Exp}(1)$ for all $i,j$ and a uniform random permutation $\pi_j$ of the machines for every task $j$, all mutually independent. The **expected makespan** is
--   $$\mathbb E[\mathrm{Mech}_{\mathrm{EBS}}(t)]=\frac{1}{(n!)^m}\sum_{\pi_1,\dots,\pi_m}\ \int \max_i\sum_{j:\,\sigma_{E,\pi}(j)=i}t_{ij}\ d\mathbb P(E),$$
--   where $\sigma_{E,\pi}$ is the assignment of Algorithm 1 for the draws $(E,\pi)$ and $\mathbb P$ is the weight law.
--
--   This is the performance measure bounded in Theorem 4.
--
--   **Formalization Note.** The makespan is the published `FracTruthSched.schedMakespan` at the assignment `ebsAssign t E π`. Independent uniform permutations form the uniform law on the finite set of permutation tuples, independent of $E$, so the expectation is the normalized finite sum of the $E$-integrals. The integral is a Bochner integral; Theorem 4 states integrability explicitly.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §4.3, p.20 (θ_i(t), Mech_EBS(t)) and Theorem 4, p.21; Algorithm 1, p.19

import Mathlib
import Definitions.Def_FracTruthSched_schedMakespan
import Definitions.Def_FracTruthSched_Supplement_ebsAssign
import Definitions.Def_FracTruthSched_Supplement_expWeightLaw

set_option autoImplicit false

namespace FracTruthSched.Supplement

open MeasureTheory

/-- The **expected makespan** `E[Mech_EBS(t)]` of Exp-Bounded-Square (Anastasiadis et al.,
arXiv:2611.06642v1, §4.3, p.20: `Mech_EBS(t) := max_i θ_i(t)` with `θ_i(t) = Σ_{j ∈ R_i(t)} t_ij`,
and Theorem 4, p.21). The randomness is that of Algorithm 1 (p.19): weights `E_ij ∼ Exp(1)` for all
`i, j` and, independently, a uniform random permutation `π_j` of the machines for every task `j`,
all mutually independent. The value is the average over all `(π_j)_j` of the integral of the
makespan of `ebsAssign t E π` against `expWeightLaw`.

**Formalization Note.** `Mech_EBS(t)` is the published `FracTruthSched.schedMakespan t σ` at the
random assignment `σ = ebsAssign t E π`. Independent uniform permutations `π_1, …, π_m` form the
uniform distribution on the finite set `Fin m → Equiv.Perm (Fin n)`, independent of `E`, so the
expectation is the normalized finite sum of the `E`-integrals (Fubini for a product with a uniform
finite factor). The integrand is a Bochner integral; Theorem 4 states its integrability
explicitly, so the expectation is never a junk `0`. -/
noncomputable def ebsExpectedMakespan {n m : ℕ} [NeZero n] (t : Fin n → Fin m → ℝ) : ℝ :=
  (Fintype.card (Fin m → Equiv.Perm (Fin n)) : ℝ)⁻¹ *
    ∑ π : Fin m → Equiv.Perm (Fin n),
      ∫ E, FracTruthSched.schedMakespan t (ebsAssign t E π) ∂(expWeightLaw n m)

end FracTruthSched.Supplement


