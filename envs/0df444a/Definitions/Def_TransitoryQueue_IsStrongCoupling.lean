-- Prove2me | Definitions.Def_TransitoryQueue_IsStrongCoupling
-- name    : TransitoryQueue_IsStrongCoupling
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:38.762982+00:00
-- url     : https://prove2.me/theorems/77fd274f-4ff1-46d0-849e-a61eefbf5628
-- title:
--   Strongly coupled version: (88), (89), (98) with one bridge
-- statement:
--   A version of the model (`IsRSVersion`) is **strongly coupled** if $B^{\mathrm{br},n}=B^{\mathrm{br},1}$ for all $n\ge1$, and there are constants $C,K,\lambda>0$ such that for all $n\ge1$ and $x>0$, each of the following events has probability less than $Ke^{-\lambda x\sqrt n}$:
--
--   1. (88) $\displaystyle\max_{0\le k\le n}\Bigl|\frac1{\sqrt n}\sum_{i=1}^{k}(\zeta_i-p)-\sqrt{p(1-p)}\,\hat B_{k/n}\Bigr|>C\frac{\log n}{\sqrt n}+x$;
--   2. (89) $\displaystyle\sup_{t\ge0}\Bigl|\sqrt n\bigl(G_n(t)-F_n(t)\bigr)-B^{\mathrm{br},n}_{F_n(t)}\Bigr|>C\frac{\log n}{\sqrt n}+x$, with $G_n(t)=\frac1n\#\{i:T_i\le t\}$;
--   3. (98) $\displaystyle\max_{0\le k\le n}\Bigl|\frac1{\sqrt n}\sum_{i=1}^{k}(V_i-\mu)-\sigma B_{k/n}\Bigr|>C\frac{\log n}{\sqrt n}+x$, where $\mu,\sigma$ are the mean and standard deviation of $\nu$.
--
--   These are the three Komlós–Major–Tusnády couplings the proofs of Theorems 2.8 and 2.11 rest on.
--
--   **Formalization Note** (88) and (98) are stated over every index $k\le n$ rather than at the random indices $nG_n(t)$ and $A_n(t)$, and are multiplied by $\sqrt{p(1-p)}$ and $\sigma$, so no division by zero occurs. (89) is centred at $F_n$ as in Corollary 5.4. A supremum exceeding a level is written as the existence of an index exceeding it.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, eqs. (88), (89), p.31; eq. (98), p.33; Corollary 5.4, p.26; Remark 8.3, p.46

import Mathlib
import Definitions.Def_TransitoryQueue_IsRSVersion
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TransitoryQueue

/-- A version of the model (`IsRSVersion`) whose Gaussian processes are **strongly coupled** to
the primitives, with one Brownian bridge for all `n` and constants `C, K, λ > 0` such that for all
`n ≥ 1` and `x > 0`:

* (88) `P(max_{0≤k≤n} |n^{-1/2} Σ_{i≤k} (ζ_i - p) - √(p(1-p)) B̂_{k/n}| > C log n/√n + x) < K e^{-λ x √n}`;
* (89) `P(sup_{t≥0} |√n (G_n(t) - F_n(t)) - B^{br}_{F_n(t)}| > C log n/√n + x) < K e^{-λ x √n}`, with
  `G_n(t) = n^{-1} #{i : T_i ≤ t}`;
* (98) `P(max_{0≤k≤n} |n^{-1/2} Σ_{i≤k} (V_i - μ) - σ B_{k/n}| > C log n/√n + x) < K e^{-λ x √n}`,
  with `μ`, `σ` the mean and standard deviation of `ν`.

Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, eqs. (88), (89), p.31, (98), p.33, Corollary 5.4, p.26, and Remark 8.3, p.46.

**Formalization Note** A predicate for the milestones, not the goal. (88) and (98) are stated for
every index `k ≤ n` instead of the random indices `n G_n(t)` and `A_n(t)`, which is stronger.
(88) is multiplied by `√(p(1-p))`, so it does not divide by `0` when `p ∈ {0, 1}`; (98) likewise
by `σ`. (89) is centred at `F_n` (Corollary 5.4); `F_n = G` gives (89) as printed. "sup > a" is
written "there is a time with value > a", which is equivalent and avoids real suprema. -/
def IsStrongCoupling {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ℕ → ℝ → ℝ) (p : ℝ)
    (ν : Measure ℝ) (T : (n : ℕ) → Fin n → Ω → ℝ) (ζ : (n : ℕ) → Fin n → Ω → ℕ)
    (V : (n : ℕ) → Fin n → Ω → ℝ) (B Bh : ℝ≥0 → Ω → ℝ) (Bbr : ℕ → ℝ → Ω → ℝ) : Prop :=
  IsRSVersion P F p ν T ζ V B Bh Bbr ∧ (∀ n : ℕ, 1 ≤ n → Bbr n = Bbr 1) ∧
  ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
    P.real {ω | ∃ k : ℕ, k ≤ n ∧ C * Real.log n / Real.sqrt n + x <
        |(∑ i : Fin n with i.val < k, ((ζ n i ω : ℝ) - p)) / Real.sqrt n
          - Real.sqrt (p * (1 - p)) * Bh ((k : ℝ≥0) / (n : ℝ≥0)) ω|}
      < K * Real.exp (-(lam * x * Real.sqrt n)) ∧
    P.real {ω | ∃ t : ℝ, 0 ≤ t ∧ C * Real.log n / Real.sqrt n + x <
        |Real.sqrt n * (((Finset.univ.filter (fun i : Fin n => T n i ω ≤ t)).card : ℝ) / n - F n t)
          - Bbr n (F n t) ω|}
      < K * Real.exp (-(lam * x * Real.sqrt n)) ∧
    P.real {ω | ∃ k : ℕ, k ≤ n ∧ C * Real.log n / Real.sqrt n + x <
        |(∑ i : Fin n with i.val < k, (V n i ω - ∫ y, y ∂ν)) / Real.sqrt n
          - Real.sqrt (variance id ν) * B ((k : ℝ≥0) / (n : ℝ≥0)) ω|}
      < K * Real.exp (-(lam * x * Real.sqrt n))

end TransitoryQueue


