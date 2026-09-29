-- Prove2me | Definitions.Def_RobustLP_Counterpart_AlmostReliable
-- name    : RobustLP_Counterpart_AlmostReliable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:26:13.742985+00:00
-- url     : https://prove2.me/theorems/c9998892-88b5-4d70-a495-398c67d487fc
-- title:
--   Random symmetric uncertainty model and almost reliable solutions (condition (ii′))
-- statement:
--   Let an uncertain linear program be given as in `UncertainLP`, with uncertain-entry sets $J_i$. Let $(S,\mathcal F,\mathbb P)$ be a probability space and $\xi_{ij}: S\to\mathbb{R}$ random variables, one for each row $i$ and column $j$.
--
--   **Random symmetric uncertainty.** The family $(\xi_{ij})$ follows the model if, for every row $i$:
--
--   1. each $\xi_{ij}$ is measurable and takes values in $[-1,1]$;
--   2. $\xi_{ij}=0$ for $j\notin J_i$;
--   3. each $\xi_{ij}$ is **symmetrically distributed**: $\xi_{ij}$ and $-\xi_{ij}$ have the same law;
--   4. the perturbations $\{\xi_{ij}\}_j$ of row $i$ are independent.
--
--   The true coefficients are then $\tilde a_{ij} = (1+\epsilon\xi_{ij})\,a_{ij}$, a multiplicative relative perturbation of size at most $\epsilon$.
--
--   **Almost reliable solutions.** Given $\epsilon$, $\delta$ and a reliability level $\kappa$, a vector $x$ is **almost reliable** if (i) it is feasible for the nominal problem and (ii′) for every $i$,
--   $$
--   \mathbb P\Big\{\sum_j \tilde a_{ij}x_j > b_i+\delta\max[1,|b_i|]\Big\} \le \kappa .
--   $$
--
--   This is the probabilistic relaxation of reliability used in Proposition 1.
--
--   **Formalization Note** The sample space is called $S$ (the paper's $\Omega$ is the safety parameter of (RC)). Symmetry is the equality of image measures `P.map (ξ i j) = P.map (fun ω => -ξ i j ω)`. Values in $[-1,1]$ are required at every outcome. Independence is `iIndepFun (ξ i) P` within each row, which is equivalent to independence of $\{\xi_{ij}\}_{j\in J_i}$ since the others are the constant $0$; nothing is assumed across rows and no identical distribution is assumed (§3.1 says only "independent"). The probability is `P.real`, the real-valued measure of the event.
-- source:
--   Ben-Tal and Nemirovski, Robust solutions of Linear Programming problems contaminated with uncertain data, Math. Program. Ser. A 88 (2000) 411–424, p. 418, §3.1, 'Random symmetric uncertainty' (ã_ij = (1 + ϵξ_ij)a_ij) and condition (ii′), 'almost reliable'

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP

namespace RobustLP.Counterpart

open MeasureTheory ProbabilityTheory

/-- The random symmetric uncertainty model (Ben-Tal–Nemirovski 2000, §3.1, p. 418) on a
probability space `(S, P)`: the perturbations `ξ i j : S → ℝ` are measurable, vanish for `j ∉ J i`,
take values in `[-1, 1]`, are symmetrically distributed (the law of `ξ i j` equals the law of
`-ξ i j`), and for each row `i` the family `(ξ i j)_j` is independent. The true coefficients are
`ã_{ij} = (1 + ε ξ_{ij}) a_{ij}`. Nothing is assumed across different rows. -/
structure IsSymmetricPerturbation {n m : ℕ} {S : Type*} [MeasurableSpace S] (P : Measure S)
    (J : Fin m → Finset (Fin n)) (ξ : Fin m → Fin n → S → ℝ) : Prop where
  measurable : ∀ i j, Measurable (ξ i j)
  zero_of_not_mem : ∀ i, ∀ j ∉ J i, ∀ ω, ξ i j ω = 0
  mem_Icc : ∀ i j ω, ξ i j ω ∈ Set.Icc (-1 : ℝ) 1
  symmetric : ∀ i j, P.map (ξ i j) = P.map (fun ω => -ξ i j ω)
  indep : ∀ i, iIndepFun (ξ i) P

namespace UncertainLP

variable {n p m : ℕ} {S : Type*} [MeasurableSpace S]

/-- The event that the `i`-th inequality, with the true coefficients
`ã_{ij} = (1 + ε ξ_{ij}(ω)) a_{ij}`, is violated beyond the tolerance:
`∑_j ã_{ij} x_j > b_i + δ max[1, |b_i|]` (condition (ii′), §3.1, p. 418). -/
def violationEvent (L : UncertainLP n p m) (ε δ : ℝ) (ξ : Fin m → Fin n → S → ℝ)
    (x : Fin n → ℝ) (i : Fin m) : Set S :=
  {ω | L.bPlus δ i < ∑ j, (1 + ε * ξ i j ω) * L.A i j * x j}

/-- `x` is an *almost reliable* solution with reliability level `κ` (§3.1, p. 418, conditions (i)
and (ii′)): `x` is feasible for the nominal problem, and for every row `i` the probability that
`∑_j ã_{ij} x_j > b_i + δ max[1, |b_i|]` is at most `κ`. -/
def AlmostReliable (L : UncertainLP n p m) (ε δ κ : ℝ) (P : Measure S)
    (ξ : Fin m → Fin n → S → ℝ) (x : Fin n → ℝ) : Prop :=
  L.NominalFeasible x ∧ ∀ i : Fin m, P.real (L.violationEvent ε δ ξ x i) ≤ κ

end UncertainLP

end RobustLP.Counterpart


