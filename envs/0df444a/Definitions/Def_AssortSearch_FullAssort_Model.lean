-- Prove2me | Definitions.Def_AssortSearch_FullAssort_Model
-- name    : AssortSearch_FullAssort_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:14.388343+00:00
-- url     : https://prove2.me/theorems/1fe40ae9-2686-469c-b0dd-0285d3af4fe1
-- title:
--   Overlapping assortment search model: $H$, $w(\bar y,S)$, the threshold $\bar U(S)$, $q_i^{so}(S)$ and $\pi^{so}(S)$
-- statement:
--   A retailer chooses an assortment $S \subseteq N = \{1,\dots,n\}$ of product variants. Variant $i$ has **preference** $v_i > 0$ (in the paper $v_i = \exp((u_i - p_i)/\mu)$, where $u_i - p_i$ is its expected net utility and $\mu > 0$ is the scale of the zero-mean Gumbel utility shocks), and the no-purchase option has preference $v_0 > 0$. Without search, variant $i \in S$ has the multinomial logit demand
--
--   $$q_i^m(S) = \frac{v_i}{\sum_{k \in S} v_k + v_0}, \qquad (2)$$
--
--   which is the published share $\mathrm{share}(v, v_0, S, i)$. Write $\gamma$ for Euler's constant. This definition introduces the objects of the **overlapping assortment model**, in which a consumer who searches pays a cost $b$ and can then buy the best variant of the whole set $N$.
--
--   1. The **Gumbel distribution function** $F(x) = \exp[-\exp(-(x/\mu + \gamma))]$ of the zero-mean shocks, and the predicate that a probability measure on $\mathbb R$ has this distribution function.
--   2. For a utility level $u$, $\lambda(u) = \exp[-(u/\mu + \gamma)]$ and $H(u, S) = \exp\big(-\lambda(u)\,(v_0 + \sum_{j \in S} v_j)\big)$, as in Theorem 1.
--   3. The total preference outside the assortment, $\bar V_S = \sum_{i \in \bar S} v_i$ with $\bar S = N - S$, the function $G_S(y) = \exp(-\lambda(y)\bar V_S)$ (the distribution function of the best utility $\max_{i \in \bar S} U_i$ outside the assortment), and its density
--   $$w(\bar y, S) = \frac{\bar V_S}{\mu}\,\lambda(\bar y)\,G_S(\bar y).$$
--   4. The expected incremental gain from search for a consumer assured of utility $u$,
--   $$\Phi_S(u) = \int_u^\infty (\bar y - u)\, w(\bar y, S)\, d\bar y,$$
--   the left-hand side of (4) and (5).
--   5. The **search threshold** $\bar U(S)$ for search cost $b$: the least $u$ with $\Phi_S(u) \le b$. For $S \ne N$ and $b > 0$ this is the unique solution of (4), $\Phi_S(\bar U(S)) = b$; that fact is a milestone of the mission, not part of the definition.
--   6. Variant $i$'s demand with search cost $b$:
--   $$q_i^{so}(S) = \begin{cases} q_i^m(S)\,\big(1 - H(\bar U(S), S)\big), & S \ne N, \\ q_i^m(N), & S = N. \end{cases}$$
--   The first line is Theorem 3's formula. For the full assortment there is no variant outside the store, so no consumer searches (the paper, p. 28: "If the retailer offers the full assortment, there will be no consumer search").
--   7. The retailer's profit $\pi^{so}(S) = \sum_{i \in S} \big[m_i\, q_i^{so}(S) - c(q_i^{so}(S))\big]$ for margins $m_i$ and an operational cost function $c$, formulas (1) and (13); and the full-assortment profit $\pi(N) = \sum_{i \in N}\big[m_i q_i^m(N) - c(q_i^m(N))\big]$, together with the identity $\pi^{so}(N) = \pi(N)$ for every $b$.
--
--   These are the objects in which Theorem 3 and Theorem 6 of the paper are stated.
--
--   **Formalization Note** Variants are `Fin n`, 0-based; $v_0$ is a separate real number, not a variant. The demand for $S = N$ is defined by the separate case above, so the junk value of the threshold at $S = N$ (where $w \equiv 0$ and $\Phi_N \equiv 0$) is never used. $\Phi_S$ is a Lebesgue integral over $(u, \infty)$; its convergence is part of a milestone, not assumed. $\bar U(S)$ is defined as an infimum so that it is a function of the data; that it solves (4) is the milestone `theorem_3_threshold`.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 5 (PDF 7), F(x); p. 6 (PDF 8), (1); p. 8 (PDF 10), Theorem 1 (H, λ); p. 10 (PDF 12), S̄ = N − S; p. 11 (PDF 13), Theorem 3, (4), (5); p. 18 (PDF 20), (13); p. 28 (PDF 30), no search under the full assortment

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model

namespace AssortSearch.FullAssort

open MeasureTheory RetailVariety.Structure

/-! # The overlapping assortment search model (§3, §3.1, §4.3)

Cachon, Terwiesch & Xu, *Retail Assortment Planning in the Presence of Consumer Search*,
working paper (Dec. 20, 2002), §3 (pp. 5–6), §3.1 (pp. 7–11), §4.3 (p. 18).

Variants are `Fin n` (the paper's variant `i` is `⟨i - 1, _⟩`). The no-purchase option is not a
variant: its preference `v0` is a separate real number. The MNL share `q_i^m(S)` of (2) is the
published `RetailVariety.Structure.share v v0 S i`. -/

/-- `V̄_S = ∑_{i ∈ S̄} v_i`, the total preference of the variants outside the assortment,
`S̄ = N − S` (p. 10). -/
noncomputable def outsidePref {n : ℕ} (v : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ Sᶜ, v i

/-- `G_S(y) = exp(-e^{-(y/μ + γ)} V̄_S)`: with i.i.d. zero-mean Gumbel shocks of scale `μ` and
`v_i = exp((u_i - p_i)/μ)`, this is the distribution function of `max_{i ∈ S̄} U_i`, the best
utility outside the assortment (p. 11; milestone `outside_max_law`). -/
noncomputable def outsideCdf {n : ℕ} (μ : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) (y : ℝ) : ℝ :=
  Real.exp (-(AssortSearch.Cannibal.lam μ y * outsidePref v S))

/-- `w(y, S) = (V̄_S/μ) e^{-(y/μ + γ)} G_S(y)`, the density of `max_{i ∈ S̄} U_i`, the
maximum utility observed in `S̄ = N − S` (Theorem 3, p. 11: "straightforward to evaluate").
For `S = N` it is identically `0`; it is only used for `S ⊊ N`. -/
noncomputable def w {n : ℕ} (μ : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) (y : ℝ) : ℝ :=
  outsidePref v S / μ * AssortSearch.Cannibal.lam μ y * outsideCdf μ v S y

/-- `Φ_S(u) = ∫_u^∞ (ȳ − u) w(ȳ, S) dȳ`, the expected incremental gain over `u` from search,
the left-hand side of (4)/(5), p. 11 (a Lebesgue integral over `(u, ∞)`). -/
noncomputable def searchGain {n : ℕ} (μ : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) (u : ℝ) : ℝ :=
  ∫ y in Set.Ioi u, (y - u) * w μ v S y

/-- The search threshold `Ū(S)` for search cost `b` (Theorem 3, (4), p. 11): the least `u` with
`Φ_S(u) ≤ b`. For `S ⊊ N` and `b > 0` this is the unique solution of `Φ_S(u) = b`
(milestone `theorem_3_threshold`). It is used only for `S ⊊ N`. -/
noncomputable def Ubar {n : ℕ} (μ : ℝ) (v : Fin n → ℝ) (S : Finset (Fin n)) (b : ℝ) : ℝ :=
  sInf {u : ℝ | searchGain μ v S u ≤ b}

/-- Variant `i`'s demand `q_i^so(S)` in the overlapping assortment model with search cost `b`.
* For `S ⊊ N`: `q_i^so(S) = q_i^m(S) (1 − AssortSearch.Cannibal.H(Ū(S), S))` (Theorem 3, p. 11).
* For `S = N`: `q_i^so(N) = q_i^m(N)`. There are no variants outside the assortment, so there is
  no consumer search (p. 28: "If the retailer offers the full assortment, there will be no
  consumer search"); no threshold `Ū(N)` is used. -/
noncomputable def demandSO {n : ℕ} (μ : ℝ) (v : Fin n → ℝ) (v0 b : ℝ) (S : Finset (Fin n))
    (i : Fin n) : ℝ :=
  if S = Finset.univ then share v v0 S i
  else share v v0 S i * (1 - AssortSearch.Cannibal.H μ (Ubar μ v S b) v v0 S)

/-- The retailer's expected profit `π^so(S) = ∑_{i∈S} [m_i q_i^so(S) − c(q_i^so(S))]`
((1), p. 6, and (13), p. 18) in the overlapping assortment model with search cost `b`. -/
noncomputable def profitSO {n : ℕ} (μ : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (m : Fin n → ℝ)
    (c : ℝ → ℝ) (b : ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ i ∈ S, (m i * demandSO μ v v0 b S i - c (demandSO μ v v0 b S i))

/-- The full-assortment profit `π(N) = ∑_{i∈N} [m_i q_i^m(N) − c(q_i^m(N))]`, which involves no
search and hence no search cost. -/
noncomputable def fullProfit {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ) : ℝ :=
  ∑ i, (m i * share v v0 Finset.univ i - c (share v v0 Finset.univ i))

/-- `π^so_b(N)` does not depend on `b`: it is the full-assortment profit. -/
theorem profitSO_univ {n : ℕ} (μ : ℝ) (v : Fin n → ℝ) (v0 : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ)
    (b : ℝ) : profitSO μ v v0 m c b Finset.univ = fullProfit v v0 m c := by
  simp [profitSO, demandSO, fullProfit]

end AssortSearch.FullAssort


