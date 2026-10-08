-- Prove2me | Definitions.Def_AssortSearch_SearchQC_Model
-- name    : AssortSearch_SearchQC_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:12.449145+00:00
-- url     : https://prove2.me/theorems/ea96acfa-a950-4a61-be72-a22fda793eb6
-- title:
--   Independent-assortment search demand $q_i^{si}(S)=q_i^m(S)(1-H(\bar U,S))$, profits $\pi_i^{si}$, $L^{si}(v_j)$ and $h^{si}(v_j)$
-- statement:
--   This file fixes the objects of Theorem 5 of Cachon, Terwiesch and Xu: the retailer's profit under the independent-assortment search model, and the change in profit from adding one variant.
--
--   A retailer chooses an assortment $S\subseteq N=\{1,\dots,n\}$ of variants. Variant $i$ has preference $v_i>0$ and the no-purchase option has preference $v_0>0$. The multinomial-logit (MNL) purchase probability without search is
--   $$q_i^m(S)=\frac{v_i}{\sum_{k\in S}v_k+v_0},\qquad i\in S,$$
--   the published `share` of the van Ryzin–Mahajan model. A consumer whose best alternative in $S\cup\{0\}$ falls below the search threshold $\bar U$ leaves to search; this happens with probability
--   $$H(\bar U,S)=\exp\Bigl(-\lambda\bigl(v_0+\textstyle\sum_{j\in S}v_j\bigr)\Bigr),\qquad \lambda=\exp\bigl[-(\bar U/\mu+\gamma)\bigr],$$
--   with $\mu>0$ the Gumbel scale and $\gamma$ Euler's constant. By Theorem 1, formula (3), variant $i$'s demand in the independent-assortment model is
--   $$q_i^{si}(S)=q_i^m(S)\bigl(1-H(\bar U,S)\bigr).$$
--   With a margin $m$ and an operational cost function $c$, variant $i$'s profit is $\pi_i^{si}(S)=m\,q_i^{si}(S)-c(q_i^{si}(S))$. We also write $V_S=v_0+\sum_{i\in S}v_i$.
--
--   Now fix $j\notin S$ and let $S_j=S\cup\{j\}$, with variant $j$'s preference a free variable $v_j=x$. Following §4:
--   1. $q_i^{si}(v_j)$ is variant $i$'s demand (3) in $S_j$, and $\pi_i^{si}(v_j)=m\,q_i^{si}(v_j)-c(q_i^{si}(v_j))$;
--   2. $L^{si}(v_j)=\sum_{i\in S}\pi_i^{si}(S)-\sum_{i\in S}\pi_i^{si}(v_j)$ is the profit lost on the variants already in $S$ (cannibalization);
--   3. $h^{si}(v_j)=\pi_j^{si}(v_j)-L^{si}(v_j)$ is the net change in profit from adding $j$.
--
--   Note that $\pi_i^{si}(S)$ uses the search factor $1-H(\bar U,S)=1-e^{-\lambda V_S}$ of the old assortment, while $\pi_i^{si}(v_j)$ uses $1-H(\bar U,S_j)=1-e^{-\lambda(v_j+V_S)}$.
--
--   **Formalization Note** Variants are `Fin n` (0-based); the no-purchase option is the separate real `v0`, not an element of `Fin n`. The model is stated with one margin `m` for every variant, as in the proof of Theorem 5. The parameter `lam` stands for $\lambda$; since every real $\bar U$ gives a $\lambda>0$ and conversely, the theorems take $\lambda>0$ as a free parameter. Adding $j$ with preference $x$ is `Function.update v j x` on `insert j S`; the value `v j` itself is never used.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 6 (PDF 8) profit (1); p. 7 (PDF 9) formula (2); p. 8 (PDF 10) Theorem 1, formula (3); p. 12 (PDF 14) pi_i(v_j), L(v_j); p. 14 (PDF 16) Theorem 5, V_S

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model

namespace AssortSearch.SearchQC

open RetailVariety.Structure

/-- `V_S = v_0 + ∑_{i∈S} v_i` (p. 14): the preference mass of the assortment `S` together with
the no-purchase option. -/
noncomputable def VS {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n)) : ℝ :=
  v0 + ∑ i ∈ S, v i

/-- `H(Ū, S) = exp(-λ (v_0 + ∑_{j∈S} v_j))` of Theorem 1 (p. 8): the probability that the best
alternative in `S ∪ {0}` falls below the search threshold `Ū`, i.e. that the consumer searches.
Here `lam` is `λ = exp[-(Ū/μ + γ)]`. -/
noncomputable def searchProb {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) : ℝ :=
  Real.exp (-(lam * (v0 + ∑ j ∈ S, v j)))

/-- Independent-assortment demand (3), Theorem 1 (p. 8):
`q_i^si(S) = q_i^m(S) (1 - H(Ū, S))`, with `q_i^m(S) = share v v0 S i` the MNL probability (2). -/
noncomputable def demandSI {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n))
    (i : Fin n) : ℝ :=
  share v v0 S i * (1 - searchProb lam v v0 S)

/-- Profit of variant `i` in assortment `S` under independent-assortment search (p. 6, with a
margin `m` common to all variants): `π_i^si(S) = m q_i^si(S) - c(q_i^si(S))`. -/
noncomputable def profitSI {n : ℕ} (m : ℝ) (c : ℝ → ℝ) (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (i : Fin n) : ℝ :=
  m * demandSI lam v v0 S i - c (demandSI lam v v0 S i)

/-- `q_i^si(v_j)` (§4, p. 12): demand (3) of variant `i` in `S_j = S ∪ {j}` when variant `j`
has preference `x`. -/
noncomputable def demandAdd {n : ℕ} (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (S : Finset (Fin n))
    (j : Fin n) (x : ℝ) (i : Fin n) : ℝ :=
  demandSI lam (Function.update v j x) v0 (insert j S) i

/-- `π_i^si(v_j) = m q_i^si(v_j) - c(q_i^si(v_j))` (§4, p. 12). -/
noncomputable def profitAdd {n : ℕ} (m : ℝ) (c : ℝ → ℝ) (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n) (x : ℝ) (i : Fin n) : ℝ :=
  m * demandAdd lam v v0 S j x i - c (demandAdd lam v v0 S j x i)

/-- `L^si(v_j) = ∑_{i∈S} π_i^si(S) - ∑_{i∈S} π_i^si(v_j)` (§4, p. 12): the profit lost on the
variants of `S` when `j` (with preference `x`) is added. -/
noncomputable def lossSI {n : ℕ} (m : ℝ) (c : ℝ → ℝ) (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n) (x : ℝ) : ℝ :=
  ∑ i ∈ S, profitSI m c lam v v0 S i - ∑ i ∈ S, profitAdd m c lam v v0 S j x i

/-- `h^si(v_j) = π_j^si(v_j) - L^si(v_j)` (Theorem 5, p. 14), as a function of `x = v_j`. -/
noncomputable def hSI {n : ℕ} (m : ℝ) (c : ℝ → ℝ) (lam : ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n) (x : ℝ) : ℝ :=
  profitAdd m c lam v v0 S j x j - lossSI m c lam v v0 S j x

end AssortSearch.SearchQC


