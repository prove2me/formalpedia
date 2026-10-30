-- Prove2me | Definitions.Def_FlexMargin_dmgi
-- name    : FlexMargin_dmgi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:38:34.578185+00:00
-- url     : https://prove2.me/theorems/0e4846e8-a363-42ba-8826-32390201eff8
-- title:
--   The Dual Margin Group Index $\delta^K_\mu(\mathcal A)$, program (4)
-- statement:
--   For a mean demand vector $\mu$ and a parameter set $K\in Q$, the **Dual Margin Group Index** of a design $\mathcal A$ is the optimal value
--
--   $$
--   \delta^K_\mu(\mathcal A)=\min_{w,y,z}\Big\{\sum_{i=1}^n\mu_i y_i+\sum_{j=1}^m C_j z_j\Big\}
--   $$
--
--   subject to: $y_i+z_j\ge p_i$ for every arc $(a_j,b_i)\in\mathcal A$; every product $b_i\in S_t$ receives exactly one level $r\in\{0,\dots,t\}$ and its price is $y_i=\beta_{tr}$; for each $t$ and $r\le t-1$ exactly $k_{tr}$ products of $S_t$ receive level $r$; and $z\ge0$.
--
--   It is the least value of mean demand and capacity needed for dual feasibility when the numbers of products at each price level are prescribed by $K$, and Theorem 1 expresses every robust measure in $\Gamma$ through it.
--
--   **Formalization Note** The constraint $z\ge0$ is not printed in (4); it is the dual feasibility of (3) that (4) is defined from, and the proofs of Proposition 3 and Lemma 2 use it. The binary variables $w_{itr}$ are encoded by assigning one level to each product. The value is an infimum, attained for $K\in Q$ and $C\ge0$.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §3.1, display (4), p. 17

import Mathlib
import Definitions.Def_FlexMargin_betaCoef

open Finset

namespace FlexMargin

/-- **The Dual Margin Group Index `δ^K_μ(𝒜)`, the integer program (4).**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §3.1, display (4), p. 17: "For a fixed µ, we define the Dual Margin Group Index (DMGI) at
parameter set K = {ktr ∈ Z+ : t = 1,...,T, r = 0,...,t − 1} for flexibility design A, denoted by
δK_µ(A), as the objective value of the following integer program:
δK_µ(A) := min_{w,y,z} { Σ_{i=1}^n µi yi + Σ_{j=1}^m Cj zj } s.t. yi + zj ≥ pi, ∀(aj,bi) ∈ A;
yi = Σ_{r=0}^t βtr witr, ∀bi ∈ St, ∀t = 1,...,T; Σ_{bi∈St} witr = ktr, ∀t = 1,...,T,
∀r = 0,...,t−1; Σ_{r=0}^t witr = 1, ∀bi ∈ St, ∀t = 1,...,T; Σ_{r=0}^t witr = 0, ∀bi ∉ St,
∀t = 1,...,T; witr ∈ {0,1} ∀bi ∈ St, ∀r = 0,...,t, ∀t = 1,...,T."

The binary variables `w_{itr}` (exactly one `r` with value 1 for each product, and only for its own
category) are encoded by a level map `w : Fin n → ℕ` with `w i ≤ cat i + 1` (the paper's
`r ∈ {0, …, t}` for the paper's category `t = cat i + 1`). Then `y_i = β_{cat i, w i}`
(`FlexMargin.betaCoef`), the count of products of category `t` at level `r` equals `K t r` for every
`r ≤ t` (the paper's `r = 0, …, t − 1`), `z ≥ 0`, and `y_i + z_j ≥ p_i = P (cat i)` on every arc `(j, i)`
of `A`. `dmgi C P cat μ A K` is the infimum of `Σ_i μ_i y_i + Σ_j C_j z_j` over these.

**Formalization Note.** (a) The constraint `z ≥ 0` is not printed in (4); it is the dual
feasibility of (3) that (4) is built on ("the minimum requirement of the mean demand and plant
capacities to ensure dual feasibility", p. 17), and the proofs of Proposition 3 (p. 41) and Lemma 2
(p. 44) use it. Without it a plant with no arcs makes (4) unbounded below. (b) For `K ∈ Q`
(`FlexMargin.InQ`) and `0 ≤ C` the feasible set is nonempty and, having finitely many `w` and
`z ≥ 0`, the infimum is attained (the paper's min). Every statement uses `dmgi` only for `K ∈ Q` and
`0 ≤ C`; outside `Q` the set is empty and `sInf ∅ = 0` is a junk value. (c) Categories and levels
are 0-based as in `FlexMargin.betaCoef` and `FlexMargin.InQ`. -/
noncomputable def dmgi {m n T : ℕ} (C : Fin m → ℝ) (P : Fin T → ℝ) (cat : Fin n → Fin T)
    (μ : Fin n → ℝ) (A : Finset (Fin m × Fin n)) (K : (t : Fin T) → Fin (t.val + 1) → ℕ) : ℝ :=
  sInf {v : ℝ | ∃ (w : Fin n → ℕ) (y : Fin n → ℝ) (z : Fin m → ℝ),
    (∀ i, w i ≤ (cat i).val + 1) ∧
    (∀ (t : Fin T) (r : Fin (t.val + 1)),
      (univ.filter (fun i => cat i = t ∧ w i = r.val)).card = K t r) ∧
    (∀ i, y i = betaCoef P (cat i) (w i)) ∧
    (∀ j, 0 ≤ z j) ∧
    (∀ a ∈ A, P (cat a.2) ≤ y a.2 + z a.1) ∧
    v = ∑ i, μ i * y i + ∑ j, C j * z j}

end FlexMargin


