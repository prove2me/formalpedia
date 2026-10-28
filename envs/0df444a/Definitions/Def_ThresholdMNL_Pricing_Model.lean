-- Prove2me | Definitions.Def_ThresholdMNL_Pricing_Model
-- name    : ThresholdMNL_Pricing_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:35:35.606259+00:00
-- url     : https://prove2.me/theorems/3e94efbb-925c-469e-82bf-51e3fca6605a
-- title:
--   §2–§3, pp. 7–14 — threshold consideration set (1), TMNL choice probabilities (2), profit (3), S_n (Definition 1), quasi-same-markup/same-utility policy (Definition 2)
-- statement:
--   This module sets up the threshold multinomial logit (TMNL) model of joint assortment and pricing of §2–§3.
--
--   A firm sells products $i\in\mathcal N=\{1,\dots,N\}$ with unit costs $c_i$; an outside option $0$ is always available. At prices $p=(p_i)$, product $i$ has **nominal utility** $u_i=\alpha_i-\beta p_i$, where $\alpha_i$ is its intrinsic utility and $\beta$ the price coefficient; the outside option has nominal utility $u_0$ (with $p_0-c_0=0$). Write $m_i=p_i-c_i$ for the markup and $\hat\alpha_i=\alpha_i-\beta c_i$ for the intrinsic utility net of cost, so $u_i=\hat\alpha_i-\beta m_i$.
--
--   1. **Threshold consideration set** (eq. (1), p. 7; p. 13). For an offer set $S\subseteq\mathcal N$ and $S^+=S\cup\{0\}$, with tolerance $\Delta\ge0$,
--   $$\Psi(S^+,p;\Delta)=\Big\{i\in S^+:\ u_i\ge\max_{j\in S^+}u_j-\Delta\Big\}.$$
--   2. **TMNL choice probabilities** (eq. (2), p. 8, with $\mu=1$ as on p. 12). For $i\in S$,
--   $$q_i(S,p;\Delta)=\begin{cases}\dfrac{e^{u_i}}{\sum_{j\in\Psi(S^+,p;\Delta)}e^{u_j}}, & i\in\Psi(S^+,p;\Delta),\\[1ex] 0, & i\notin\Psi(S^+,p;\Delta),\end{cases}$$
--   where the denominator contains $e^{u_0}$ exactly when the outside option is in $\Psi$.
--   3. **Profit** (eq. (3), p. 12): $R(S,p;\Delta)=\sum_{i\in\Psi(S^+,p;\Delta)}(p_i-c_i)\,q_i(S,p;\Delta)$.
--   4. **Utility-net-cost ordered assortment** (Definition 1, p. 13): $S_n=\{1,2,\dots,n\}$ for $n\in\mathcal N$.
--   5. **Quasi-same-markup/same-utility policy** (Definition 2, p. 14): for indices $1\le n'\le n\le N$, products $2,\dots,n'$ have equal markups and products $n'+1,\dots,n$ have equal nominal utilities; product $1$ is unconstrained.
--   6. **Outside-excluded profit** (proof of Theorem 2, OS p. 2): for a nonempty set $S$ that is exactly the consideration set,
--   $$\frac{\sum_{i\in S}m_i e^{u_i}}{\sum_{i\in S}e^{u_i}}.$$
--
--   These objects are shared by every statement of the mission: Theorems 1–4 and the exchange step in the proof of Theorem 2.
--
--   **Formalization Note** Products are `Fin N`, and the paper's product $k$ is the index $k-1$ (product $1$ is index $0$, $S_n$ is the set of indices below $n$). The outside option is not an element of `Fin N`: it is the separate real parameter `u0`. Membership in $\Psi$ is written as "$u_i\ge u_j-\Delta$ for every $j\in S^+$", which is equivalent to (1) because $S^+$ is finite and nonempty; `InCons` is product membership and `OutsideInCons` that of the outside option. Prices are real vectors on all of `Fin N` (they may be negative); only their values on $S$ enter any definition. The scale $\mu$ is fixed to $1$, as the paper does for (3), and the Gumbel derivation of (2) is not formalized: the closed form (2) is the model. Under $\Delta\ge0$ the alternative of largest nominal utility in $S^+$ is always in $\Psi$, so the denominator of (2) is positive; every theorem assumes $\Delta\ge0$.
-- source:
--   Wang, The Threshold Effects on Consumer Choice and Pricing Decisions, SSRN 3765711 (version of 2020), pp. 5–8, eqs. (1)–(2); p. 12, eq. (3); p. 13, Definition 1; p. 14, Definition 2; OS p. 2, proof of Theorem 2 (profit formula R(S, m; Δ))

import Mathlib

namespace ThresholdMNL.Pricing

open Finset

/-- Nominal utility `u_i = α_i − β p_i` of product `i` at prices `p` (p. 12). Products are `Fin N`;
the paper's product `k` is the index `k − 1`. -/
def nomUtil {N : ℕ} (α : Fin N → ℝ) (β : ℝ) (p : Fin N → ℝ) (i : Fin N) : ℝ :=
  α i - β * p i

/-- Product `i` belongs to the threshold consideration set `Ψ(S⁺, p; Δ)` of eq. (1), `S⁺ = S ∪ {0}`:
`i ∈ S` and `u_i ≥ u_j − Δ` for every `j ∈ S⁺`, where `u0` is the nominal utility of the outside
option `0`. This is `u_i ≥ max_{j ∈ S⁺} u_j − Δ` written without a maximum. -/
def InCons {N : ℕ} (S : Finset (Fin N)) (α : Fin N → ℝ) (β u0 Δ : ℝ) (p : Fin N → ℝ)
    (i : Fin N) : Prop :=
  i ∈ S ∧ u0 - Δ ≤ nomUtil α β p i ∧ ∀ j ∈ S, nomUtil α β p j - Δ ≤ nomUtil α β p i

/-- The outside option `0` belongs to `Ψ(S⁺, p; Δ)`: `u_0 ≥ u_j − Δ` for every `j ∈ S⁺`. -/
def OutsideInCons {N : ℕ} (S : Finset (Fin N)) (α : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) : Prop :=
  ∀ j ∈ S, nomUtil α β p j - Δ ≤ u0

open Classical in
/-- The products of the consideration set `Ψ(S⁺, p; Δ)`. -/
noncomputable def consSet {N : ℕ} (S : Finset (Fin N)) (α : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) : Finset (Fin N) :=
  S.filter (fun i => InCons S α β u0 Δ p i)

open Classical in
/-- The denominator `∑_{j ∈ Ψ(S⁺, p; Δ)} exp(u_j)` of eq. (2) with `µ = 1`; the outside option
contributes `exp(u_0)` exactly when it is in the consideration set. -/
noncomputable def consDenom {N : ℕ} (S : Finset (Fin N)) (α : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) : ℝ :=
  (if OutsideInCons S α β u0 Δ p then Real.exp u0 else 0) +
    ∑ j ∈ consSet S α β u0 Δ p, Real.exp (nomUtil α β p j)

open Classical in
/-- The TMNL choice probability `q_i(S, p; Δ)` of eq. (2) with `µ = 1`: `exp(u_i)` over the
denominator if `i ∈ Ψ(S⁺, p; Δ)`, and `0` otherwise. -/
noncomputable def choiceProb {N : ℕ} (S : Finset (Fin N)) (α : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) (i : Fin N) : ℝ :=
  if InCons S α β u0 Δ p i then Real.exp (nomUtil α β p i) / consDenom S α β u0 Δ p else 0

/-- The total expected profit `R(S, p; Δ) = ∑_{i ∈ Ψ(S⁺, p; Δ)} (p_i − c_i) q_i(S, p; Δ)` of
eq. (3); the outside option earns `p_0 − c_0 = 0`. -/
noncomputable def profit {N : ℕ} (S : Finset (Fin N)) (α c : Fin N → ℝ) (β u0 Δ : ℝ)
    (p : Fin N → ℝ) : ℝ :=
  ∑ i ∈ consSet S α β u0 Δ p, (p i - c i) * choiceProb S α β u0 Δ p i

/-- The utility-net-cost ordered assortment `S_n = {1, …, n}` of Definition 1, 0-based: the indices
`i` with `i.val < n`. -/
def ordAssort (N n : ℕ) : Finset (Fin N) :=
  univ.filter (fun i : Fin N => i.val < n)

/-- The quasi-same-markup/same-utility policy of Definition 2 on `S_n`, 0-based: `1 ≤ n' ≤ n ≤ N`;
the paper's products `2, …, n'` (indices `1, …, n' − 1`) have equal markups `p_i − c_i`, and its
products `n' + 1, …, n` (indices `n', …, n − 1`) have equal nominal utilities. Product `1`
(index `0`) is unconstrained. -/
def IsQuasiSameMarkupSameUtility {N : ℕ} (α c : Fin N → ℝ) (β : ℝ) (n n' : ℕ)
    (p : Fin N → ℝ) : Prop :=
  1 ≤ n' ∧ n' ≤ n ∧ n ≤ N ∧
  (∀ i j : Fin N, 1 ≤ i.val → i.val < n' → 1 ≤ j.val → j.val < n' →
      p i - c i = p j - c j) ∧
  (∀ i j : Fin N, n' ≤ i.val → i.val < n → n' ≤ j.val → j.val < n →
      nomUtil α β p i = nomUtil α β p j)

/-- The total expected profit when the consideration set is exactly `S` (outside option excluded),
`∑_{i ∈ S} m_i exp(u_i) / ∑_{i ∈ S} exp(u_i)` with `m_i = p_i − c_i`: the formula
`R(S, m; Δ)` of the proof of Theorem 2 (OS p. 2). -/
noncomputable def exclProfit {N : ℕ} (S : Finset (Fin N)) (α c : Fin N → ℝ) (β : ℝ)
    (p : Fin N → ℝ) : ℝ :=
  (∑ i ∈ S, (p i - c i) * Real.exp (nomUtil α β p i)) / ∑ i ∈ S, Real.exp (nomUtil α β p i)

end ThresholdMNL.Pricing


