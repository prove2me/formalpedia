-- Prove2me | Definitions.Def_OptStochMatch_Tight_Laws
-- name    : OptStochMatch_Tight_Laws
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:53:34.652758+00:00
-- url     : https://prove2.me/theorems/0d4e4592-1a6b-4b9c-a8f8-c007a41d2e67
-- title:
--   Arrival laws (Poisson and i.i.d.), $\mathrm{Exp}(1)$ demands and Poisson type counts
-- statement:
--   - $Z_i\sim\mathrm{Exp}(1)$ independent (law `demandLaw m` on $\mathbb R^m$); $N_S\sim\mathrm{Pois}(\lambda_S)$ independent (law `countLaw`); the internal seed $U\sim\mathrm{Uniform}[0,1]$.
--   - Poisson arrivals on $[0,1]$: the expectation of a nonnegative functional of the arrival stream is written through the Janossy densities of the marked Poisson process — on the event of exactly $n$ arrivals at ordered times $0\le t_0<\dots<t_{n-1}\le 1$ with types $s_0,\dots,s_{n-1}$ the density is $e^{-\sum_S\lambda_S}\prod_k\lambda_{s_k}$. This is the superposition of independent type-wise Poisson processes of intensities $\lambda_S$ (including the empty type).
--   - i.i.d. arrivals: $n$ neighbourhoods drawn independently from $\mu$; optionally with independent uniform timestamps processed in increasing order (density $n!$ on the ordered simplex).
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), §2.1–§2.2, pp. 5–6 (PDF 6–7); §5, p. 18 (PDF 19)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic

/-!
Dütting, Feldman, Molina, *Optimal Online Stochastic Matching*, arXiv:2610.19866
(sha256 0458ce2e…), §2.1–§2.2 and §5, pp. 5–6, 18 (PDF 6–7, 19).

The probability laws of the two arrival models and of the service demands.

* `countLaw lam`: independent type counts `N_S ∼ Pois(λ_S)` (p. 5, PDF 6).
* `demandLaw m`: independent service demands `Z_i ∼ Exp(1)` (p. 6, PDF 7).
* `poissonExpect lam F`: the expectation of a nonnegative functional `F` of the realized
  arrival stream of the Poisson model on `[0,1]`: arrivals of type `S` form independent Poisson
  processes of intensity `λ_S`. It is written through the Janossy densities of the marked
  Poisson process: on the event of exactly `n` arrivals, at ordered times
  `0 ≤ t_0 < ⋯ < t_{n-1} ≤ 1` with types `s_0, …, s_{n-1}`, the density with respect to
  Lebesgue measure on the ordered simplex is `e^{−∑_S λ_S} ∏_k λ_{s_k}`.
  This is the law of the superposition of the independent type-wise Poisson processes (the
  total includes the empty type `S = ∅`).
* `iidExpect n mu F`: the expectation over `n` i.i.d. neighbourhoods with law `µ` (p. 18, PDF 19).
-/

namespace OptStochMatch.Tight

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

/-- The unit-rate exponential law `Exp(1)` on `ℝ`. -/
noncomputable def expOne : Measure ℝ := expMeasure 1

instance : IsProbabilityMeasure expOne :=
  isProbabilityMeasure_gammaMeasure one_pos one_pos

/-- Independent `Exp(1)` service demands `Z = (Z_i)_{i ∈ [m]}`. -/
noncomputable def demandLaw (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ : Fin m => expOne

/-- Independent type counts `N_S ∼ Pois(λ_S)`, `S ⊆ [m]`. -/
noncomputable def countLaw {m : ℕ} (lam : Ty m → ℝ≥0) : Measure (Ty m → ℕ) :=
  Measure.pi fun S : Ty m => poissonMeasure (lam S)

/-- The uniform law of the internal random seed `U ∼ Uniform[0,1]` of a randomized policy. -/
noncomputable def seedLaw : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The ordered simplex `{t : 0 ≤ t_0 < t_1 < ⋯ < t_{n-1} ≤ 1}` of arrival times. -/
def orderedTimes (n : ℕ) : Set (Fin n → ℝ) :=
  {t | StrictMono t ∧ ∀ k, t k ∈ Set.Icc (0 : ℝ) 1}

/-- Total arrival intensity `∑_{S ⊆ [m]} λ_S` (including the empty type). -/
noncomputable def totalRate {m : ℕ} (lam : Ty m → ℝ≥0) : ℝ := ∑ S : Ty m, (lam S : ℝ)

/-- Expectation, in the Poisson arrival model with intensities `lam` on the horizon `[0,1]`,
of a nonnegative functional `F n t s` of the realized arrival stream (`n` arrivals, ordered
times `t`, types `s`), through the Janossy densities of the marked Poisson process. -/
noncomputable def poissonExpect {m : ℕ} (lam : Ty m → ℝ≥0)
    (F : (n : ℕ) → (Fin n → ℝ) → (Fin n → Ty m) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (Real.exp (-totalRate lam)) *
    ∑ s : Fin n → Ty m, (∏ k, (lam (s k) : ℝ≥0∞)) * ∫⁻ t in orderedTimes n, F n t s

/-- Expectation over `n` i.i.d. arrivals with neighbourhood law `mu` of a nonnegative
functional of the realized neighbourhood sequence. -/
noncomputable def iidExpect {m : ℕ} (n : ℕ) (mu : Ty m → ℝ≥0)
    (F : (Fin n → Ty m) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ s : Fin n → Ty m, (∏ k, (mu (s k) : ℝ≥0∞)) * F s

/-- Expectation over `n` i.i.d. arrivals with neighbourhood law `mu`, each carrying an
independent `Uniform[0,1]` timestamp, processed in increasing timestamp order (§5.1, p. 18,
PDF 19): the ordered timestamps have density `n!` on the ordered simplex. -/
noncomputable def iidTimedExpect {m : ℕ} (n : ℕ) (mu : Ty m → ℝ≥0)
    (F : (Fin n → ℝ) → (Fin n → Ty m) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ s : Fin n → Ty m, (∏ k, (mu (s k) : ℝ≥0∞)) *
    ((n.factorial : ℝ≥0∞) * ∫⁻ t in orderedTimes n, F t s)

end OptStochMatch.Tight


