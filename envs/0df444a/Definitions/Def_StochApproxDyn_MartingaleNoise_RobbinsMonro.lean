-- Prove2me | Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro
-- name    : StochApproxDyn_MartingaleNoise_RobbinsMonro
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T16:11:06.677113+00:00
-- url     : https://prove2.me/theorems/4bea6432-d3b4-4390-9f91-bb553cd4f1b4
-- title:
--   Robbins–Monro algorithm (martingale difference noise condition, §4.2)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\{\mathcal F_n\}_{n\ge0}$ a nondecreasing sequence of sub-$\sigma$-algebras of $\mathcal F$. Let $F:\mathbb R^d\to\mathbb R^d$ be continuous and $\{\gamma_n\}_{n\ge1}$ a step sequence ($\gamma_n\ge0$, $\sum\gamma_n=\infty$, $\gamma_n\to0$). Random sequences $\{x_n\}_{n\ge0}$ and $\{U_n\}_{n\ge1}$ in $\mathbb R^d$ form a **Robbins–Monro algorithm** if, on every sample path,
--   $$x_{n+1}-x_n=\gamma_{n+1}\big(F(x_n)+U_{n+1}\big)\qquad(n\ge0), \tag{7}$$
--   and the Robbins–Monro (martingale difference noise) condition holds:
--
--   1. $\{\gamma_n\}$ is a deterministic sequence;
--   2. $\{U_n\}$ is adapted: $U_n$ is $\mathcal F_n$-measurable;
--   3. $E(U_{n+1}\mid\mathcal F_n)=0$.
--
--   This is the simplest probabilistic setting in which the noise hypothesis A1 can be verified by martingale techniques.
--
--   **Formalization Note** "Deterministic" is encoded by $\gamma$ being a fixed real sequence. Condition 3 is stated for integrable $U_{n+1}$, so that the conditional expectation is the genuine one (Lean's conditional expectation of a non-integrable function is $0$ by convention). The paper indexes $U$ from $1$; $U_0$ is unused. The space is $\mathbb R^d$ as `EuclideanSpace ℝ (Fin d)` (the paper writes $\mathbb R^m$). The filtration is a Mathlib `Filtration ℕ`, i.e. a nondecreasing sequence of sub-$\sigma$-algebras. The definition takes the measure $P$ as a parameter; that $P$ is a probability measure is stated as a hypothesis (`IsProbabilityMeasure P`) by every theorem that uses it.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 4.1, p. 11 (PDF p. 12), Eq. (7); Section 4.2, p. 14 (PDF p. 15), conditions (i)–(iii)

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation

namespace StochApproxDyn.MartingaleNoise

open MeasureTheory

/-- A Robbins–Monro algorithm (Benaïm 1999, §4.1 p. 11 and §4.2 p. 14).

On a probability space `(Ω, ℱ, P)` with a nondecreasing sequence `ℱ_n` of sub-σ-algebras, the
random sequence `x` is given by scheme (7), `x_{n+1} - x_n = γ_{n+1} (F(x_n) + U_{n+1})`, with
the standing assumptions of §4.1 (`F : ℝ^d → ℝ^d` continuous, `γ` a step sequence), and
satisfies the Robbins–Monro (martingale difference noise) condition:
(i) `γ` is deterministic (it is a fixed real sequence, not a random one);
(ii) `U_n` is `ℱ_n`-measurable;
(iii) `E(U_{n+1} | ℱ_n) = 0`, where `U_{n+1}` is integrable so that the conditional expectation
is the genuine one. The paper indexes `U` from `1`; `U 0` is not used. -/
def IsRobbinsMonro {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (γ : ℕ → ℝ) (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) : Prop :=
  Continuous F ∧ IsStepSequence γ ∧
  (∀ n ω, x (n + 1) ω - x n ω = γ (n + 1) • (F (x n ω) + U (n + 1) ω)) ∧
  (∀ n : ℕ, StronglyMeasurable[ℱ (n + 1)] (U (n + 1))) ∧
  (∀ n : ℕ, Integrable (U (n + 1)) P) ∧
  (∀ n : ℕ, P[U (n + 1) | ℱ n] =ᵐ[P] 0)

end StochApproxDyn.MartingaleNoise


