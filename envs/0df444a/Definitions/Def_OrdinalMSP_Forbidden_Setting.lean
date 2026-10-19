-- Prove2me | Definitions.Def_OrdinalMSP_Forbidden_Setting
-- name    : OrdinalMSP_Forbidden_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:18:54.425847+00:00
-- url     : https://prove2.me/theorems/8a8e3d33-e0da-49b0-94a6-feb63b8e8d26
-- title:
--   §2, §3.1, pp. 6–9 — ordered matroid, greedy optimum OPT(Q), arrival prefixes R_t, Bin(n,p)-sampled selection probability, Definition 7, probability-competitiveness (3), p(k), α(k)
-- statement:
--   The objects of the ordinal matroid secretary problem and of the forbidden-sets technique of Soto, Turkieltaub and Verdugo.
--
--   1. **Ordered matroid.** $\mathcal M$ is a matroid on a finite ground set $R$ with $|R| = n$, and $\succ$ is a total order on $R$, the *value order*. The **span** of $Q \subseteq R$ is $\mathrm{span}(Q) = \{r \in R : \rho(Q + r) = \rho(Q)\}$, where $\rho$ is the rank function.
--
--   2. **Greedy optimum.** For $Q \subseteq R$, $\mathrm{OPT}(Q)$ is the lexicographically optimum base of $Q$, produced by the greedy algorithm that scans $Q$ in decreasing value order and keeps an element when it keeps the current set independent. Equivalently,
--   $$\mathrm{OPT}(Q) = \{\, r \in Q : r \notin \mathrm{span}(\{q \in Q : q \succ r\}) \,\}.$$
--   We write $\mathrm{OPT} = \mathrm{OPT}(R)$.
--
--   3. **Arrival order.** The elements arrive in an order $r_1, r_2, \dots, r_n$ (a bijection between the times $1, \dots, n$ and $R$), and $R_t = \{r_1, \dots, r_t\}$ is the set of elements arrived up to time $t$.
--
--   4. **Algorithms.** An algorithm is described by its output $\mathrm{ALG}(\sigma, s) \subseteq R$ on arrival order $\sigma$ and sample size $s$.
--
--   5. **Definition 7 (forbidden sets of size $k$).** The algorithm has forbidden sets of size $k$ if
--      - *(Correctness)* every output $\mathrm{ALG}(\sigma, s)$ is independent;
--      - *(Sampling property)* none of the first $s$ arriving elements is ever selected;
--      - *($k$-forbidden property)* there is a map assigning to each triple $(X, Y, r^*)$ with $Y \subseteq R$, $r^* \in \mathrm{OPT}(Y)$ and $X \subseteq Y - r^*$ a set $\mathcal F(X, Y, r^*) \subseteq X$ of at most $k$ forbidden elements, such that for every arrival order and every sample size $s$ and every time $t \ge s+1$: if $r_t \in \mathrm{OPT}(R_t)$ and $r_j \notin \mathcal F(R_j, R_t, r_t)$ for every $j \in \{s+1, \dots, t-1\}$, then $r_t$ is selected.
--
--   6. **Selection probability.** The sample size is $s \sim \mathrm{Bin}(n, p)$ and, independently, the arrival order is uniform over all $n!$ orders. Hence
--   $$\Pr(r \in \mathrm{ALG}) = \sum_{s=0}^{n} \binom{n}{s} p^s (1-p)^{n-s}\, \frac{\#\{\sigma : r \in \mathrm{ALG}(\sigma, s)\}}{n!}.$$
--
--   7. **Probability-competitiveness, (3).** With sampling probability $p$, the algorithm is $\alpha$ probability-competitive if $\Pr(e \in \mathrm{ALG}) \ge 1/\alpha$ for every $e \in \mathrm{OPT}$.
--
--   8. **The constants of Lemma 1.**
--   $$(p(k), \alpha(k)) = \begin{cases} (1/e,\ e) & k = 1,\\ (k^{-1/(k-1)},\ k^{k/(k-1)}) & k \ge 2.\end{cases}$$
--
--   These are the objects in which the Key Lemma and its proof steps are stated; Definition 7 is the interface that the paper's algorithms for transversal, graphic, laminar and other matroid classes verify.
--
--   **Formalization Note** The value order $\succ$ is Lean's `<` read upward ($r \succ q$ iff $q < r$). The matroid is a Mathlib `Matroid R`; the statements assume its ground set is all of `R`, and `Matroid.closure` is the span. `OPT(Q)` is defined through the span characterization above, which is the greedy output (and what the proof of Lemma 4 uses). An arrival order is `σ : Fin n ≃ R`, where `σ i` arrives at time $i+1$: index $i$ is time $t = i + 1$, so "$t \ge s+1$" reads `s ≤ i`, "$j \in \{s+1,\dots,t-1\}$" reads `s ≤ j₀ < i` with $j_0 = j - 1$, and $R_j$ is `arrived σ (j₀ + 1)`. The algorithm is any map $(\sigma, s) \mapsto \mathrm{ALG}(\sigma, s)$: online-ness is not required (a generalization the proof allows), and randomness beyond $s$ is not modelled (the paper's algorithms use none). The map $\mathcal F$ is fixed before the run and does not depend on $\sigma$ or $s$; its bounds $\mathcal F \subseteq X$, $|\mathcal F| \le k$ are required exactly on the printed domain $r^* \in \mathrm{OPT}(Y)$, $X \subseteq Y - r^*$. The probability is a finite sum in $\mathbb R$; $e$ is `Real.exp 1` and the powers are `Real.rpow`; `pK` and `alphaK` branch on $k = 1$ first, so the division by $k - 1$ is never evaluated at $k = 1$.
-- source:
--   Soto, Turkieltaub & Verdugo, Strong Algorithms for the Ordinal Matroid Secretary Problem, arXiv:1802.01997v1, §2 (ordered matroid, OPT(Q), span, R_t), p. 6; (3), p. 7; Definition 7, p. 8; Lemma 1 (Key Lemma) constants, p. 9

import Mathlib

namespace OrdinalMSP.Forbidden

variable {R : Type*} [Fintype R] [DecidableEq R] [LinearOrder R]

/-- An arrival order of the ground set `R` (Soto–Turkieltaub–Verdugo, arXiv:1802.01997v1, §2, p. 6):
`σ i` is the element arriving at time `i + 1` (0-based index `i`, 1-based time on the page). -/
abbrev ArrivalOrder (R : Type*) [Fintype R] := Fin (Fintype.card R) ≃ R

/-- `OPT(Q)` (§2, p. 6): the lexicographically optimum base of `Q`, obtained by running the greedy
algorithm over `Q` in the value order `≻`, where `r ≻ q` is read as `q < r`. Greedy in decreasing
value order keeps `r ∈ Q` exactly when `r` is not spanned by the elements of `Q` valued above `r`. -/
noncomputable def opt (M : Matroid R) (Q : Finset R) : Finset R := by
  classical
  exact Q.filter (fun r => r ∉ M.closure {q | q ∈ Q ∧ r < q})

/-- `R_t` (§2, p. 6): the set of the first `t` arrivals of the order `σ`, i.e. `{σ i | i < t}`. -/
def arrived (σ : ArrivalOrder R) (t : ℕ) : Finset R :=
  (Finset.univ.filter (fun i : Fin (Fintype.card R) => (i : ℕ) < t)).image σ

/-- Definition 7 (§3.1, p. 8): `ALG` has forbidden sets of size `k`. `ALG σ s` is the set returned
on arrival order `σ` with sample size `s`.
1. (Correctness) the output is independent;
2. (Sampling property) none of the first `s` arrivals is accepted;
3. (`k`-forbidden property) there is a map `F(X, Y, r*)` with `F(X, Y, r*) ⊆ X` and
   `|F(X, Y, r*)| ≤ k` whenever `r* ∈ OPT(Y)` and `X ⊆ Y − r*`, such that for every arrival order and
   sample size, if the element `r_t = σ i` arriving at time `t = i + 1 ≥ s + 1` lies in `OPT(R_t)`
   and, for every time `j ∈ {s+1, …, t−1}` (0-based index `j₀ = j − 1`, `s ≤ j₀ < i`),
   `r_j ∉ F(R_j, R_t, r_t)`, then `r_t` is selected. -/
structure HasForbiddenSets (M : Matroid R) (k : ℕ) (ALG : ArrivalOrder R → ℕ → Finset R) :
    Prop where
  correct : ∀ σ s, M.Indep (ALG σ s : Set R)
  sampling : ∀ σ s (i : Fin (Fintype.card R)), (i : ℕ) < s → σ i ∉ ALG σ s
  forbidden : ∃ F : Finset R → Finset R → R → Finset R,
    (∀ X Y r, r ∈ opt M Y → X ⊆ Y.erase r → F X Y r ⊆ X ∧ (F X Y r).card ≤ k) ∧
    ∀ σ s (i : Fin (Fintype.card R)), s ≤ (i : ℕ) →
      σ i ∈ opt M (arrived σ ((i : ℕ) + 1)) →
      (∀ j : Fin (Fintype.card R), s ≤ (j : ℕ) → (j : ℕ) < (i : ℕ) →
          σ j ∉ F (arrived σ ((j : ℕ) + 1)) (arrived σ ((i : ℕ) + 1)) (σ i)) →
      σ i ∈ ALG σ s

/-- `Pr(r ∈ ALG)` when the sample size `s ∼ Bin(n, p)` is drawn independently of a uniformly random
arrival order (all `n!` orders equally likely), `n = |R|`:
`∑_{s=0}^{n} C(n,s) p^s (1-p)^{n-s} · #{σ : r ∈ ALG σ s} / n!`. -/
noncomputable def selProb (ALG : ArrivalOrder R → ℕ → Finset R) (p : ℝ) (r : R) : ℝ :=
  ∑ s ∈ Finset.range (Fintype.card R + 1),
    ((Fintype.card R).choose s : ℝ) * p ^ s * (1 - p) ^ (Fintype.card R - s) *
      (((Finset.univ.filter (fun σ : ArrivalOrder R => r ∈ ALG σ s)).card : ℝ) /
        ((Fintype.card R).factorial : ℝ))

/-- (3) (§2.1, p. 7): with sampling probability `p`, `ALG` is `α` probability-competitive if every
`r ∈ OPT = OPT(R)` is selected with probability at least `1/α`. -/
def IsProbCompetitive (M : Matroid R) (ALG : ArrivalOrder R → ℕ → Finset R) (p α : ℝ) : Prop :=
  ∀ r ∈ opt M Finset.univ, 1 / α ≤ selProb ALG p r

/-- `p(k)` of Lemma 1 (p. 9): `1/e` for `k = 1`, `k^{-1/(k-1)}` for `k ≥ 2`. -/
noncomputable def pK (k : ℕ) : ℝ :=
  if k = 1 then Real.exp (-1) else (k : ℝ) ^ (-(1 / ((k : ℝ) - 1)))

/-- `α(k)` of Lemma 1 (p. 9): `e` for `k = 1`, `k^{k/(k-1)}` for `k ≥ 2`. -/
noncomputable def alphaK (k : ℕ) : ℝ :=
  if k = 1 then Real.exp 1 else (k : ℝ) ^ ((k : ℝ) / ((k : ℝ) - 1))

end OrdinalMSP.Forbidden


