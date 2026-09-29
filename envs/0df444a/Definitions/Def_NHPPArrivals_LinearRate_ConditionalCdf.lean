-- Prove2me | Definitions.Def_NHPPArrivals_LinearRate_ConditionalCdf
-- name    : NHPPArrivals_LinearRate_ConditionalCdf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:18:12.242976+00:00
-- url     : https://prove2.me/theorems/4795e29c-3bbb-4718-b360-792419453bf3
-- title:
--   Cumulative rate Λ, conditional cdf Λ(tT)/Λ(T), degree of nonhomogeneity, subinterval mixture Σ p_j F_j, linear rate a + bt, one-arrival law (§3.2 (4), (5), (9); §3.3 (12); §3.5 (17), (18))
-- statement:
--   This file fixes the objects of §3 of Kim and Whitt (2014) for an arrival rate function $\lambda$ on a finite interval $[0,T]$.
--
--   1. **Cumulative arrival rate** (4): $\Lambda(t) = \int_0^t \lambda(s)\,ds$.
--   2. **Conditional cdf** (5): the cdf on $[0,1]$ of one scaled arrival time,
--   $$F(t) = \frac{\Lambda(tT)}{\Lambda(T)}, \qquad 0 \le t \le 1.$$
--   3. **Degree of nonhomogeneity** (9): for a cdf $F$ on $[0,1]$,
--   $$D = \sup_{0 \le t \le 1} |F(t) - t|,$$
--   the distance of $F$ from the uniform cdf. It is $0$ exactly for a homogeneous Poisson process.
--   4. **Equal subintervals** (17): divide $[0,T]$ into $k$ subintervals of length $T/k$. For $1 \le j \le k$,
--   $$\Lambda_j(t) = \Lambda\big((j-1)T/k + t\big) - \Lambda\big((j-1)T/k\big), \qquad F_j(t) = \frac{\Lambda_j(tT/k)}{\Lambda_j(T/k)}, \qquad p_j = \frac{\Lambda(jT/k) - \Lambda((j-1)T/k)}{\Lambda(T)},$$
--   and the combined conditional cdf of LEMMA 1 is the mixture $F(t) = \sum_{j=1}^k p_j F_j(t)$.
--   5. **Linear arrival rate** (12): $\lambda(t) = a + bt$, and the relative slope of the $j$-th subinterval (18), $r_j = b/\lambda((j-1)T/k)$. The relative slope of the whole interval is $r = b/a$ and needs no separate definition.
--   6. **Law of one arrival**: the probability measure on $\mathbb R$ with density $\lambda(s)/\Lambda(T)$ on $[0,T]$ and zero elsewhere. By the paper's THEOREM 1, conditionally on $n$ arrivals in $[0,T]$ the arrival times are distributed as the order statistics of $n$ i.i.d. variables with this law.
--
--   These are the shared vocabulary of every statement in the mission: THEOREM 4 computes $F$ and $D$ for a linear rate, LEMMA 1 identifies the law of the combined data as the mixture, and THEOREM 5 computes its degree of nonhomogeneity.
--
--   **Formalization Note** Rates are real functions $\lambda : \mathbb R \to \mathbb R$ of which only the values on $[0,T]$ matter; $\Lambda$ is an interval integral. All quotients are Lean real divisions, which return $0$ when the denominator is $0$; every theorem of the mission carries hypotheses under which $\Lambda(T) > 0$ and $\Lambda_j(T/k) > 0$. The supremum $D$ is `sSup` of the image of $[0,1]$; every theorem that uses it also proves that the supremum is attained (`IsGreatest`), so no junk value of `sSup` enters. The indices $k, j$ are natural numbers cast to reals, with $(j-1)$ computed in $\mathbb R$. The one-arrival law is `withDensity` of $\mathrm{ofReal}(\lambda/\Lambda(T))$ over Lebesgue measure restricted to $[0,T]$; the Poisson process itself is not formalized.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, pp. 471–472, §3.2 (4), (5) (THEOREM 1), (9); §3.3 (12); §3.5 LEMMA 1 (17), (18)

import Mathlib

namespace NHPPArrivals.LinearRate

open MeasureTheory

/-- (4): the cumulative arrival rate `Λ(t) = ∫₀ᵗ λ(s) ds`. -/
noncomputable def cumRate (lam : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, lam s

/-- (5): the conditional cdf `F(t) = Λ(tT)/Λ(T)` of the scaled arrival times on `[0, T]`. -/
noncomputable def condCdf (lam : ℝ → ℝ) (T t : ℝ) : ℝ := cumRate lam (t * T) / cumRate lam T

/-- (9): the degree of nonhomogeneity `D = sup_{0 ≤ t ≤ 1} |F(t) − t|` of a cdf `F` on `[0, 1]`. -/
noncomputable def degree (F : ℝ → ℝ) : ℝ := sSup ((fun t => |F t - t|) '' Set.Icc (0:ℝ) 1)

/-- (17): `Λ_j(t) = Λ((j − 1)T/k + t) − Λ((j − 1)T/k)`, the cumulative rate of the `j`-th of `k`
equal subintervals of `[0, T]`. -/
noncomputable def subCum (lam : ℝ → ℝ) (T : ℝ) (k j : ℕ) (t : ℝ) : ℝ :=
  cumRate lam (((j:ℝ) - 1) * T / k + t) - cumRate lam (((j:ℝ) - 1) * T / k)

/-- (17): `F_j(t) = Λ_j(tT/k)/Λ_j(T/k)`, the conditional cdf of the `j`-th subinterval. -/
noncomputable def subCdf (lam : ℝ → ℝ) (T : ℝ) (k j : ℕ) (t : ℝ) : ℝ :=
  subCum lam T k j (t * T / k) / subCum lam T k j (T / k)

/-- (17): `p_j = (Λ(jT/k) − Λ((j − 1)T/k))/Λ(T)`, the share of the `j`-th subinterval. -/
noncomputable def weight (lam : ℝ → ℝ) (T : ℝ) (k j : ℕ) : ℝ :=
  (cumRate lam ((j:ℝ) * T / k) - cumRate lam (((j:ℝ) - 1) * T / k)) / cumRate lam T

/-- LEMMA 1: the conditional cdf `F(t) = ∑_{j=1}^k p_j F_j(t)` of the combined data of the `k`
equal subintervals. -/
noncomputable def mixCdf (lam : ℝ → ℝ) (T : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 k, weight lam T k j * subCdf lam T k j t

/-- (12): the linear arrival rate `λ(t) = a + bt`. -/
def linRate (a b : ℝ) : ℝ → ℝ := fun s => a + b * s

/-- (18): `r_j = b/λ((j − 1)T/k)`, the relative slope of the linear rate on the `j`-th
subinterval. -/
noncomputable def subSlope (a b T : ℝ) (k j : ℕ) : ℝ := b / linRate a b (((j:ℝ) - 1) * T / k)

/-- The law on `[0, T]` of one arrival time of the NHPP given the number of arrivals
(THEOREM 1 before scaling by `T`): density `λ(s)/Λ(T)` with respect to Lebesgue measure on
`[0, T]`. -/
noncomputable def arrivalLaw (lam : ℝ → ℝ) (T : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Icc (0:ℝ) T)).withDensity (fun s => ENNReal.ofReal (lam s / cumRate lam T))

end NHPPArrivals.LinearRate


