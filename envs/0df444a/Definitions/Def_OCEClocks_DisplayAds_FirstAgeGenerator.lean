-- Prove2me | Definitions.Def_OCEClocks_DisplayAds_FirstAgeGenerator
-- name    : OCEClocks_DisplayAds_FirstAgeGenerator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:21:24.617923+00:00
-- url     : https://prove2.me/theorems/36eb0da4-8d2d-4a57-a157-88393a7cc96e
-- title:
--   The First-Age Poisson generator (§3.2, eq. (3))
-- statement:
--   Fix an arrival rate $\lambda>0$. The **First-Age Poisson generator** lays the incoming allocations consecutively on the timeline $[0,\infty)$ of a stationary rate-$\lambda$ Poisson process. Its internal randomness is the process together with independent $V_j\sim\mathrm{Unif}[0,1]$, one per request. Upon receiving $x_j$:
--
--   1. if $x_j=0$, return $Y_j=\infty$;
--   2. take the next interval $I_j=\big[\sum_{j'<j}x_{j'},\ \sum_{j'\le j}x_{j'}\big)$ and compute its first age $\widehat A(I_j)$;
--   3. set
--   $$U_j=\begin{cases}e^{-\lambda x_j}V_j, & \widehat A(I_j)=0,\\ F_{x_j}\big(\widehat A(I_j)\big), & \widehat A(I_j)>0;\end{cases}\qquad(3)$$
--   4. return $Y_j=-\log U_j/x_j$.
--
--   This is the generator the paper uses in all its applications. Lemma 9 shows that it is an OCEC generator.
--
--   **Formalization Note** `generatorLaw λ n` is the product of the Poisson gap law (`gapLaw λ`) and $n$ i.i.d. uniforms (`unifLaw`, Lebesgue measure on $[0,1]$). `clockOf λ x b v` performs steps 1, 3 and 4 for mass `x`, first age `b` and uniform `v`, returning `ENNReal.ofReal (-log U / x)`; since first ages are nonnegative, the case `b ≠ 0` is the paper's case $\widehat A>0$. `requestInterval x j` is $I_j$. `firstAgeGenerator λ n x (G, V) j = clockOf λ (x j) (firstAge G I_j) (V j)`. One process and one uniform sequence serve the whole input, as in the paper.
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 8, §3.2, box 'First-Age Poisson Generator', eq. (3)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_PoissonProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OCEClocks.DisplayAds

/-!
# The First-Age Poisson generator (§3.2)

Huang, Patton, Yang, Zhao, *Online Correlated Exponential Clocks*, STOC 2027 submission
(manuscript of November 3, 2026), p. 8, §3.2 (box "First-Age Poisson Generator", eq. (3)).

Parameter: arrival rate `λ > 0`. Internal randomness: the gap sequence `G` of the stationary
Poisson process (`gapLaw λ`) and, independently, i.i.d. uniforms `V_j ∼ Unif[0, 1]`, one per
request. Upon receiving `x_j`:
1. if `x_j = 0`, return `Y_j = ∞`;
2. take the next interval `I_j = [Σ_{j' < j} x_{j'}, Σ_{j' ≤ j} x_{j'})` and compute `Â(I_j)`;
3. set `U_j = e^{-λ x_j} V_j` if `Â(I_j) = 0` and `U_j = F_{x_j}(Â(I_j))` if `Â(I_j) > 0` (3);
4. return `Y_j = -log U_j / x_j`.
-/

/-- The uniform law on `[0, 1]`. -/
noncomputable def unifLaw : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Steps 1, 3 and 4 of the generator for one request of mass `x`, given the first age `b` of its
interval and the uniform `v`: `∞` if `x = 0`, else `-log U / x` with `U = e^{-λx} v` if `b = 0`
and `U = F_x(b)` if `b ≠ 0` (first ages are nonnegative, so `b ≠ 0` is `b > 0`). -/
noncomputable def clockOf (lam x b v : ℝ) : ℝ≥0∞ :=
  if x = 0 then ⊤
  else ENNReal.ofReal
    (-Real.log (if b = 0 then Real.exp (-(lam * x)) * v else firstAgeCDF lam x b) / x)

/-- The interval `I_j = [Σ_{j' < j} x_{j'}, Σ_{j' ≤ j} x_{j'})` of request `j` on the timeline
`[0, ∞)` (step 2). -/
def requestInterval {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : Set ℝ :=
  Set.Ico (∑ j' ∈ Finset.univ.filter (fun j' => j' < j), x j')
    (∑ j' ∈ Finset.univ.filter (fun j' => j' ≤ j), x j')

/-- The internal randomness of one First-Age Poisson generator on `n` requests: the gap sequence
of the stationary rate-`λ` Poisson process and, independently, `n` i.i.d. `Unif[0, 1]`. -/
noncomputable def generatorLaw (lam : ℝ) (n : ℕ) : Measure ((ℤ → ℝ) × (Fin n → ℝ)) :=
  (gapLaw lam).prod (Measure.pi fun _ : Fin n => unifLaw)

/-- The First-Age Poisson generator with rate `λ` (p. 8): on input `x` and randomness
`ω = (G, V)`, the clock of request `j` is `clockOf λ x_j (Â(I_j)) V_j`. -/
noncomputable def firstAgeGenerator (lam : ℝ) (n : ℕ) :
    (Fin n → ℝ) → (ℤ → ℝ) × (Fin n → ℝ) → Fin n → ℝ≥0∞ :=
  fun x ω j => clockOf lam (x j) (firstAge ω.1 (requestInterval x j)) (ω.2 j)

end OCEClocks.DisplayAds


