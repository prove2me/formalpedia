-- Prove2me | Definitions.Def_CorreaThreshold_Nonadaptive_Bernoulli
-- name    : CorreaThreshold_Nonadaptive_Bernoulli
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T12:35:57.383001+00:00
-- url     : https://prove2.me/theorems/2e9e0ee9-8586-4930-9ada-9dcd9830b0fd
-- title:
--   §2, pp. 1455–1458 — Bernoulli selection objective, relaxation, f_M, φ_n and h_n
-- statement:
--   For independent Bernoulli indicators with success probabilities $q_i$, `bernExp` sums the product probability of each success set $T$ times the value of a function of $T$. For prizes $b_i$ and a chosen set $S$, the selected payoff is
--
--   $$r_b(S,T)=\frac{\sum_{i\in S\cap T}b_i}{|S\cap T|},\qquad 0/0:=0.$$
--
--   Problem (P) maximizes the expectation of this payoff over deterministic subsets $S$. The multilinear relaxation replaces choosing $S$ with independent inclusion probabilities $\pi_i$; `objFour` is the same polynomial after exchanging the summations. The auxiliary function $f_M$, the expression $\varphi_n$ in display (6), and $h_n$ in Lemma 2 are the paper's analytic quantities for its $1-1/e$ bound.
--
--   **Formalization Note** Finite sums and products implement the Bernoulli law. The real division convention makes the empty selected set pay zero. The printed formula for $\varphi_n(y)$ has a removable $0/0$ at $y=1$; the definition assigns its continuous value $2/e$ there, as required by the paper's closed-interval Lemma 2.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), pp. 1455–1458, Lemma 1, (P), (4)–(6), Lemma 2; https://doi.org/10.1287/moor.2020.1105

import Mathlib

namespace CorreaThreshold.Nonadaptive

/-- Expectation under independent Bernoulli indicators with success probabilities `q`. -/
noncomputable def bernExp {n : ℕ} (q : Fin n → ℝ)
    (g : Finset (Fin n) → ℝ) : ℝ :=
  ∑ T : Finset (Fin n),
    (∏ i ∈ T, q i) * (∏ i ∈ Tᶜ, (1 - q i)) * g T

/-- The selected average for accepted set `T` and chosen subset `S`. -/
noncomputable def selRatio {n : ℕ} (b : Fin n → ℝ)
    (S T : Finset (Fin n)) : ℝ :=
  (∑ i ∈ S ∩ T, b i) / (((S ∩ T).card : ℝ))

/-- The optimum of problem (P) over all deterministic subsets. -/
noncomputable def objP {n : ℕ} (q b : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun S : Finset (Fin n) => bernExp q (selRatio b S))

/-- The multilinear relaxation of (P). -/
noncomputable def relaxObj {n : ℕ} (b π : Fin n → ℝ) : ℝ :=
  ∑ S : Finset (Fin n),
    ((∑ i ∈ S, b i) / (S.card : ℝ)) *
      (∏ i ∈ S, π i) * (∏ i ∈ Sᶜ, (1 - π i))

/-- Equation (4), after exchanging the order of summation. -/
noncomputable def objFour {n : ℕ} (b π : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, b i * π i *
    ∑ S ∈ (Finset.univ.erase i).powerset,
      (1 / (1 + (S.card : ℝ))) * (∏ j ∈ S, π j) *
        (∏ j ∈ (Finset.univ.erase i) \ S, (1 - π j))

/-- The paper's auxiliary function `f_M` in display (5). -/
noncomputable def fM {n : ℕ} (M : Finset (Fin n)) (x : Fin n → ℝ) : ℝ :=
  (∏ j ∈ M, 1 / (2 + (Real.exp 1 - 2) * x j)) *
    ∑ S ∈ M.powerset,
      (2 : ℝ) ^ S.card / (1 + (S.card : ℝ)) *
        (∏ j ∈ S, x j) *
        (∏ j ∈ M \ S, (2 - (4 - Real.exp 1) * x j))

/-- The expression `φ_n` in display (6), with its continuous value at `y = 1`. -/
noncomputable def phi (n : ℕ) (y : ℝ) : ℝ :=
  if y = 1 then 2 / Real.exp 1 else
    (2 / (2 + (Real.exp 1 - 2) * y)) *
      ((2 * n + (Real.exp 1 - 2) * (1 - y)) /
        (2 * (n + 1) * (1 - y))) *
      (1 - (1 - 2 * (1 - y) /
        (2 * n + (Real.exp 1 - 2) * (1 - y))) ^ (n + 1))

/-- The function `h_n` in Lemma 2. -/
noncomputable def h (n : ℕ) (x : ℝ) : ℝ :=
  1 / ((n : ℝ) + 1) - (1 - x) ^ (n + 1) / ((n : ℝ) + 1) -
    ((Real.exp 1 - 1) / 2) * x +
    (((Real.exp 1 - 1) * (Real.exp 1 - 2) * n) /
      (Real.exp 1 * (2 - (Real.exp 1 - 2) * x))) * x ^ 2

end CorreaThreshold.Nonadaptive


