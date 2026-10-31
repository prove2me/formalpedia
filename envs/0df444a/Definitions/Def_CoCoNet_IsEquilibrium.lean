-- Prove2me | Definitions.Def_CoCoNet_IsEquilibrium
-- name    : CoCoNet_IsEquilibrium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:56.580651+00:00
-- url     : https://prove2.me/theorems/fc9de49c-f66f-4838-b408-f2266301f927
-- title:
--   $(B,C,H)$-equilibrium of asset values $a$ and stock prices $s$
-- statement:
--   Let $(m,W)$ be a conversion network, $l$ the conversion thresholds, $c$ the convertible debts. Given a partition $(B,C,H)$ of $[n]$ into bankrupt, converting and healthy banks, the asset vector $a$ and price vector $s$ form a **$(B,C,H)$-equilibrium candidate** if
--   $$(1+m_i)s_i=a_i+\sum_{j\in C}w_{ij}m_js_j+\sum_{j\in H}w_{ij}c_j\qquad\text{for all } i\in B\cup C, \tag{1}$$
--   $$s_i=a_i-c_i+\sum_{j\in C}w_{ij}m_js_j+\sum_{j\in H}w_{ij}c_j\qquad\text{for all } i\in H. \tag{2}$$
--   It is a **$(B,C,H)$-equilibrium** if moreover the partition is consistent with the prices:
--   $$B=\{i:s_i<0\},\quad C=\{i:0\le s_i\le l_i\},\quad H=\{i:s_i>l_i\}.$$
--
--   Equation (1) says that the total value of a converting (or bankrupt) bank's stocks equals its assets plus the stocks received from converting banks plus the cash received from healthy banks; (2) is the same balance for a healthy bank, which pays back its debt $c_i$ and issues no new stocks.
--
--   **Formalization Note** A partition is three pairwise disjoint sets of banks covering `Fin n`; blocks may be empty.
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, §2 'Equilibrium Concept', p.9, equations (1)–(2)

import Mathlib
import Definitions.Def_CoCoNet_bankrupt
import Definitions.Def_CoCoNet_converting
import Definitions.Def_CoCoNet_healthy

namespace CoCoNet

/-- **`(B, C, H)`-equilibrium.**
Balter, Schweizer & Vera, arXiv:2011.06474v1, §2 "Equilibrium Concept", p.9: "Given a partition
(B, C, H) of the set [n] of banks into bankrupt (B), converting (C) and healthy (H) banks, we say
that the price vector s and asset vector a form a (B, C, H)-equilibrium candidate if they solve
the following system of equations:
(1 + mᵢ)sᵢ = aᵢ + Σ_{j∈C} wᵢⱼ mⱼ sⱼ + Σ_{j∈H} wᵢⱼ cⱼ for all i ∈ B ∪ C (1)
sᵢ = aᵢ − cᵢ + Σ_{j∈C} wᵢⱼ mⱼ sⱼ + Σ_{j∈H} wᵢⱼ cⱼ for all i ∈ H (2)
… A (B, C, H)-equilibrium candidate (a, s) is a (B, C, H)-equilibrium if … B = {i|sᵢ < 0},
C = {i|0 ≤ sᵢ ≤ lᵢ} and H = {i|sᵢ > lᵢ}."

Here `m` are the conversion ratios, `W i j = wᵢⱼ`, `l` the thresholds, `c` the convertible debts,
`a` the asset values and `s` the stock prices.

**Formalization Note.** A partition of `[n]` is three pairwise disjoint `Finset (Fin n)`s whose
union is everything (blocks may be empty). -/
structure IsEquilibrium {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (l c a s : Fin n → ℝ) (B C H : Finset (Fin n)) : Prop where
  disjoint_BC : Disjoint B C
  disjoint_BH : Disjoint B H
  disjoint_CH : Disjoint C H
  cover : B ∪ C ∪ H = Finset.univ
  /-- Equation (1). -/
  eq1 : ∀ i ∈ B ∪ C,
    (1 + m i) * s i = a i + ∑ j ∈ C, W i j * m j * s j + ∑ j ∈ H, W i j * c j
  /-- Equation (2). -/
  eq2 : ∀ i ∈ H,
    s i = a i - c i + ∑ j ∈ C, W i j * m j * s j + ∑ j ∈ H, W i j * c j
  /-- Consistency: `B = {i | sᵢ < 0}`. -/
  B_eq : B = bankrupt s
  /-- Consistency: `C = {i | 0 ≤ sᵢ ≤ lᵢ}`. -/
  C_eq : C = converting l s
  /-- Consistency: `H = {i | sᵢ > lᵢ}`. -/
  H_eq : H = healthy l s

end CoCoNet


