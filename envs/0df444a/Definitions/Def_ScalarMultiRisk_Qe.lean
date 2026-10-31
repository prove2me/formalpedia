-- Prove2me | Definitions.Def_ScalarMultiRisk_Qe
-- name    : ScalarMultiRisk_Qe
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:18:33.611181+00:00
-- url     : https://prove2.me/theorems/2c8e7709-56e2-45fe-95f3-828597a7908f
-- title:
--   The set $\mathcal Q^e(S)$ of consistent equivalent martingale measures
-- statement:
--   For $S\in\mathcal S$, $\mathcal Q^e(S)$ is the set of probability measures $\mathbb Q\sim\mathbb P$ with
--
--   $$S_s=\mathbb E^{\mathbb Q}[S_T\mid\mathcal F_s]\ \text{ for all }s,\qquad\frac{d\mathbb Q}{d\mathbb P}S_T\in\mathbb K_T^+.$$
--
--   **Formalization Note** The other conditions of $\mathcal Q_0$ hold for $S\in\mathcal S$ by (4.3). For $\mathbb Q\sim\mathbb P$ the paper's $\mathbb P$-a.s. version of $\mathbb E^{\mathbb Q}[\cdot\mid\mathcal F_t]$ agrees a.s. with the usual conditional expectation.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 4.2, p.18, with p.11 and p.13

import Mathlib
import Definitions.Def_ScalarMultiRisk_dualKK

open MeasureTheory

namespace ScalarMultiRisk

/-- **The set `𝒬^e(S)`.** arXiv:1807.10694v5, Definition 4.2, p.18, with `𝒬_t` (p.11) and `𝒬^e_t`
(p.13): `𝒬^e(S) := {ℚ ∈ ℳ | (ℚ, S) ∈ 𝒬^e_0}`, i.e. the probability measures `ℚ ∼ ℙ` with
`S_s = 𝔼^ℚ[S_T | F_s]` for all `s` and `dℚ/dℙ S_T ∈ 𝕂_T⁺`.

**Formalization Note.** `𝒬_0` also requires `S_s ∈ L∞_s(ℝ^d)`, `S_{s,1} ≡ 1` and the bound
`‖S_{s,i}‖_∞ ≤ max{‖e_i‖_{𝕂_T,0}, 1}`; for `S ∈ 𝒮`, the only case the paper considers, they
hold by (4.3). The paper's `𝔼^ℚ[·|F_t]` is a `ℙ`-a.s. version (p.6); since `ℚ ∼ ℙ` it agrees
a.s. with Mathlib's `ℚ[·|F t]`, used coordinatewise. -/
def Qe {Ω : Type*} [MeasurableSpace Ω] {T d : ℕ} (A : Market Ω T d)
    (S : Fin (T + 1) → Ω → Fin d → ℝ) : Set (Measure Ω) :=
  {Q | IsProbabilityMeasure Q ∧ Q ≪ A.P ∧ A.P ≪ Q ∧
    (∀ s i, (fun ω => S s ω i) =ᵐ[A.P] Q[fun ω => S (Fin.last T) ω i | A.F s]) ∧
    (fun ω => (Q.rnDeriv A.P ω).toReal • S (Fin.last T) ω) ∈ dualKK A}

end ScalarMultiRisk


