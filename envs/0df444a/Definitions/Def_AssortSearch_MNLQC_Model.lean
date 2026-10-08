-- Prove2me | Definitions.Def_AssortSearch_MNLQC_Model
-- name    : AssortSearch_MNLQC_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:49.401463+00:00
-- url     : https://prove2.me/theorems/6c1b201a-dfbb-4c67-94aa-2dc4be729305
-- title:
--   No-search MNL assortment model: $\pi_i(S)$, $q_i(v_j)$, $\pi_i(v_j)$, $L(v_j)$, $h^m(v_j)$ and the numerator of (6)
-- statement:
--   A retailer chooses an assortment $S \subseteq N = \{1,\dots,n\}$ of product variants. Variant $i$ has **preference** $v_i > 0$ (in the paper $v_i = \exp((u_i - p_i)/\mu)$), and the no-purchase option has preference $v_0 > 0$. In the traditional multinomial logit (MNL) model without consumer search, variant $i \in S$ has demand
--
--   $$q_i^m(S) = \frac{v_i}{\sum_{k \in S} v_k + v_0}, \qquad (2)$$
--
--   which is the published MNL share $\mathrm{share}(v, v_0, S, i)$. Variant $i$ has margin $m_i = p_i - c_i$, and including it costs $c(q_i(S))$ for an operational cost function $c$. Its profit is $\pi_i(S) = m_i q_i(S) - c(q_i(S))$, and the retailer's profit is $\pi(S) = \sum_{i \in S} \pi_i(S)$, formula (1).
--
--   Now fix $S$ and a variant $j \notin S$, and treat $j$'s preference $v_j$ as a free variable $x$. With $S_j = S \cup \{j\}$, this definition introduces:
--
--   1. $V_S = v_0 + \sum_{i \in S} v_i$;
--   2. $q_i(v_j)$, the MNL demand (2) of variant $i$ in the assortment $S_j$ when $j$ has preference $v_j$;
--   3. $\pi_i(v_j) = m_i q_i(v_j) - c(q_i(v_j))$, variant $i$'s profit with assortment $S_j$;
--   4. $L(v_j) = \sum_{i \in S} \pi_i(S) - \sum_{i \in S} \pi_i(v_j)$, the profit lost on the variants already in $S$ when $j$ is introduced;
--   5. $h^m(v_j) = \pi_j^m(v_j) - L^m(v_j)$, the net change in the retailer's profit from adding $j$, so that adding $j$ is profitable exactly when $h^m(v_j) > 0$;
--   6. the numerator of (6), with per-variant margins:
--
--   $$\Big[m_j V_S - c'\Big(\tfrac{v_j}{v_j+V_S}\Big) V_S\Big] - \Big[\sum_{i\in S} m_i v_i - \sum_{i\in S} c'\Big(\tfrac{v_i}{v_j+V_S}\Big) v_i\Big].$$
--
--   These are the objects of §4 and §4.1 of the paper. Theorem 4 and the steps of its proof are stated in terms of them.
--
--   **Formalization Note** Variants are `Fin n`, 0-based. The no-purchase option is not a variant: $v_0$ is a separate real number. $q_i(v_j)$ is `share (Function.update v j x) v0 (insert j S) i`; the theorems assume $j \notin S$, so the update only sets $j$'s own preference. $c'$ is Mathlib's `deriv c`, which is the true derivative only where $c$ is differentiable; the theorems that use the numerator assume this on $(0,1)$. The paper writes one margin $m$ in (6). With all $m_i = m$ the numerator above is exactly the printed one.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 6 (PDF 8), (1); p. 7 (PDF 9), (2); p. 12 (PDF 14), §4, π_i(v_j) and L(v_j); p. 13 (PDF 15), Theorem 4, h^m; p. 14 (PDF 16), V_S and (6)

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model

namespace AssortSearch.MNLQC

open RetailVariety.Structure

/-- `V_S = v_0 + ∑_{i∈S} v_i` (proof of Theorem 4, p. 14): the total preference of the
no-purchase option and the variants of `S`. -/
noncomputable def prefTotal {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n)) : ℝ :=
  v0 + ∑ i ∈ S, v i

/-- The profit `π_i(S) = m_i q_i^m(S) − c(q_i^m(S))` of variant `i` with assortment `S`
in the no-search (MNL) model (§3, p. 6), with `q_i^m(S)` the MNL share (2), p. 7. -/
noncomputable def profitS {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  m i * share v v0 S i - c (share v v0 S i)

/-- `q_i(v_j)` (§4, p. 12): the MNL demand (2) of variant `i` with assortment
`S_j = S ∪ {j}` when the added variant `j` has preference `x` (the paper's `v_j`, treated as a
free variable). -/
noncomputable def demandAdded {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n))
    (j : Fin n) (x : ℝ) (i : Fin n) : ℝ :=
  share (Function.update v j x) v0 (insert j S) i

/-- `π_i(v_j) = m_i q_i(v_j) − c(q_i(v_j))` (§4, p. 12): the profit of variant `i` with
assortment `S_j = S ∪ {j}` when `j` has preference `x`. -/
noncomputable def profitAdded {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n) (x : ℝ) (i : Fin n) : ℝ :=
  m i * demandAdded v v0 S j x i - c (demandAdded v v0 S j x i)

/-- `L(v_j) = ∑_{i∈S} π_i(S) − ∑_{i∈S} π_i(v_j)` (§4, p. 12): the change in the profit of the
variants already in `S` when variant `j`, with preference `x`, is introduced. -/
noncomputable def lossL {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n) (x : ℝ) : ℝ :=
  ∑ i ∈ S, profitS m c v v0 S i - ∑ i ∈ S, profitAdded m c v v0 S j x i

/-- `h^m(v_j) = π_j^m(v_j) − L^m(v_j)` (Theorem 4, p. 13): the profit of the added variant `j`
minus the loss it causes on the variants of `S`, as a function of `j`'s preference `x`. -/
noncomputable def hm {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n) (x : ℝ) : ℝ :=
  profitAdded m c v v0 S j x j - lossL m c v v0 S j x

/-- The numerator of (6), p. 14, with per-variant margins:
`[m_j V_S − c′(v_j/(v_j+V_S)) V_S] − [∑_{i∈S} m_i v_i − ∑_{i∈S} c′(v_i/(v_j+V_S)) v_i]`,
evaluated at `v_j = x`, with `c′ = deriv c`. With all margins equal to `m` it is the printed
numerator `[m V_S − c′(·) V_S] − [m ∑_{i∈S} v_i − ∑_{i∈S} c′(·) v_i]`. -/
noncomputable def numerator6 {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n) (x : ℝ) : ℝ :=
  (m j * prefTotal v v0 S - deriv c (x / (x + prefTotal v v0 S)) * prefTotal v v0 S)
    - (∑ i ∈ S, m i * v i - ∑ i ∈ S, deriv c (v i / (x + prefTotal v v0 S)) * v i)

end AssortSearch.MNLQC


