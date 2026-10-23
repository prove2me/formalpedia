-- Prove2me | Definitions.Def_NonRandomChoice_Assort_Model
-- name    : NonRandomChoice_Assort_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:50.700996+00:00
-- url     : https://prove2.me/theorems/4c27ce9b-6857-48ae-aacc-3c582c8882c6
-- title:
--   §2, (1), §3.1, (12)–(13) — the choice model with one deterministic product utility, its revenue and the revenue-ordered assortments
-- statement:
--   Let $\mathcal N=\{1,\dots,N\}$ be the set of products and let $0$ denote the no-purchase option, which is always available. A consumer's utility for product $i$ is $U_i=u_i+\xi_i$ and for the no-purchase option $U_0=u_0+\xi_0$, where the $\xi$'s are i.i.d. Gumbel with scale parameter $\mu>0$ and mean $0$; one product $i'\in\mathcal N$ is special: its utility is deterministic, $U_{i'}=u_{i'}$. Product $i$ sells at price $p_i$.
--
--   The model is described through the following quantities:
--   1. the attraction values $a_i=\exp(u_i/\mu)$ for $i\in\mathcal N$ and $a_0=\exp(u_0/\mu)$ for the no-purchase option;
--   2. $\Lambda=\exp(-u_{i'}/\mu-\gamma)$, where $\gamma\approx 0.5772$ is the Euler–Mascheroni constant;
--   3. for an offer set $S\subseteq\mathcal N$, the total attraction of the random alternatives offered together with $i'$,
--   $$\Psi(S^+/\{i'\})=a_0+\sum_{j\in S\setminus\{i'\}}a_j .$$
--
--   **Choice probabilities.** If $i'\notin S$, the model is the multinomial logit (MNL) model: $q_i(S)=a_i/(a_0+\sum_{j\in S}a_j)$ for $i\in S$. If $i'\in S$, writing $\Psi=\Psi(S^+/\{i'\})$, the choice probabilities are those of model (1),
--   $$q_i(S)=\frac{a_i}{\Psi}\bigl[1-\exp(-\Lambda\Psi)\bigr]\quad(i\in S\setminus\{i'\}),\qquad q_{i'}(S)=\exp(-\Lambda\Psi).$$
--   Products outside $S$ are never chosen, $q_i(S)=0$ for $i\notin S$, and the no-purchase probability is $q_0(S)=1-\sum_{i\in S}q_i(S)$.
--
--   **Revenue (12).** The expected revenue of the offer set $S$ is
--   $$R(S)=\begin{cases}\dfrac{\sum_{i\in S}p_i a_i}{a_0+\sum_{j\in S}a_j}, & i'\notin S,\\[2ex] \dfrac{\sum_{i\in S\setminus\{i'\}}p_i a_i}{\Psi(S^+/\{i'\})}\bigl[1-\exp(-\Lambda\Psi(S^+/\{i'\}))\bigr]+p_{i'}\exp(-\Lambda\Psi(S^+/\{i'\})), & i'\in S,\end{cases}$$
--   and the assortment problem (13) is $\max_{S\subseteq\mathcal N}R(S)$.
--
--   **Revenue-ordered assortments.** When the products, $i'$ included, are labelled so that $p_1\ge p_2\ge\dots\ge p_N$, the sets $S_n=\{1,2,\dots,n\}$ are the revenue-ordered assortments.
--
--   Finally, $h_\Lambda(y)=\Lambda(1-y)/(-\log y)$ expresses the no-purchase probability $q_0$ as a function of $y=q_{i'}$ when $a_0=1$ (proof of Theorem 5, p. 29).
--
--   These objects are the setting of Theorem 5 and of its proof via Lemma 1.
--
--   **Formalization Note** Products are `Fin N`; the paper's label $k$ is the index $k-1$, the deterministic product $i'$ is a parameter `ip`, and the no-purchase option is not an element of `Fin N`. `attr`, `attr0`, `Lam`, `Psi` are $a_i$, $a_0$, $\Lambda$, $\Psi$; `choiceProb` is $q_i(S)$; `revenue12` is (12) written literally as on the page (not through `choiceProb`); `roSet N n` is $S_n$, with `roSet N 0 = ∅`; `qZeroOfQip Λ y` is $h_\Lambda(y)$. The attraction $a_{i'}$ plays no role in (12) and is never used. Real division by zero cannot occur in (12) because $a_0>0$.
-- source:
--   Wang, What Is the Impact of Non-Randomness on Random Choice Models?, SSRN 3579781 (PDF sha256 93af6c3d…), pp. 5–6, 13–14, 29, §2, Theorem 1 eq. (1), §3.1, eqs. (12)–(13), revenue-ordered assortments, proof of Theorem 5

import Mathlib
import Definitions.Def_RevenueOrdered_Ratio_Model

namespace NonRandomChoice.Assort

/-- The attraction value `a_i = exp(u_i / μ)` of product `i` (Wang, §2, p. 6; §3.1, p. 13).
Products are `Fin N`; the paper's label `k ∈ {1, …, N}` is the index `k - 1`. -/
noncomputable def attr {N : ℕ} (μ : ℝ) (u : Fin N → ℝ) (i : Fin N) : ℝ :=
  Real.exp (u i / μ)

/-- The attraction value `a_0 = exp(u_0 / μ)` of the no-purchase option `0` (§3.1, p. 13).
The no-purchase option is not an element of `Fin N`. -/
noncomputable def attr0 (μ u0 : ℝ) : ℝ :=
  Real.exp (u0 / μ)

/-- `Λ = exp(-u_{i'} / μ - γ)`, with `γ` the Euler–Mascheroni constant (§3.1, p. 13).
The deterministic product `i'` is `ip`; its utility `u_{i'}` enters the model only here. -/
noncomputable def Lam {N : ℕ} (μ : ℝ) (u : Fin N → ℝ) (ip : Fin N) : ℝ :=
  Real.exp (-(u ip) / μ - Real.eulerMascheroniConstant)

/-- `Ψ(S⁺/{i'}) = a_0 + ∑_{j ∈ S ∖ {i'}} a_j` (§3.1, p. 13): the total attraction of the random
alternatives offered together with `i'`, the no-purchase option included. -/
noncomputable def Psi {N : ℕ} (μ u0 : ℝ) (u : Fin N → ℝ) (ip : Fin N) (S : Finset (Fin N)) : ℝ :=
  attr0 μ u0 + ∑ j ∈ S.erase ip, attr μ u j

/-- The choice probability `q_i(S)` of product `i` from the offer set `S` (§3.1, p. 13):
* if `i' ∉ S`, the MNL probability `a_i / (a_0 + ∑_{j ∈ S} a_j)` for `i ∈ S`;
* if `i' ∈ S`, model (1) (Theorem 1, p. 6) on the random alternatives `(S ∖ {i'}) ∪ {0}`:
  `q_i(S) = a_i / Ψ · [1 - exp(-Λ Ψ)]` for `i ∈ S ∖ {i'}` and `q_{i'}(S) = exp(-Λ Ψ)`;
* `q_i(S) = 0` for `i ∉ S`. -/
noncomputable def choiceProb {N : ℕ} (μ u0 : ℝ) (u : Fin N → ℝ) (ip : Fin N) :
    Fin N → Finset (Fin N) → ℝ :=
  fun i S =>
    if i ∈ S then
      if ip ∈ S then
        if i = ip then Real.exp (-(Lam μ u ip * Psi μ u0 u ip S))
        else attr μ u i / Psi μ u0 u ip S * (1 - Real.exp (-(Lam μ u ip * Psi μ u0 u ip S)))
      else attr μ u i / (attr0 μ u0 + ∑ j ∈ S, attr μ u j)
    else 0

/-- The total expected revenue `R(S)` of the offer set `S`, equation (12), p. 13, written as on
the page:
`R(S) = ∑_{i ∈ S} p_i a_i / (a_0 + ∑_{j ∈ S} a_j)` if `i' ∉ S`, and
`R(S) = ∑_{i ∈ S ∖ {i'}} p_i a_i / Ψ · [1 - exp(-Λ Ψ)] + p_{i'} exp(-Λ Ψ)` if `i' ∈ S`. -/
noncomputable def revenue12 {N : ℕ} (μ u0 : ℝ) (u : Fin N → ℝ) (ip : Fin N) (p : Fin N → ℝ)
    (S : Finset (Fin N)) : ℝ :=
  if ip ∈ S then
    (∑ i ∈ S.erase ip, p i * attr μ u i) / Psi μ u0 u ip S *
        (1 - Real.exp (-(Lam μ u ip * Psi μ u0 u ip S)))
      + p ip * Real.exp (-(Lam μ u ip * Psi μ u0 u ip S))
  else
    (∑ i ∈ S, p i * attr μ u i) / (attr0 μ u0 + ∑ j ∈ S, attr μ u j)

/-- The revenue-ordered assortment `S_n = {1, …, n}` (pp. 13–14): the first `n` products in the
label order, i.e. the indices `0, …, n - 1` of `Fin N`. `roSet N 0 = ∅`. -/
def roSet (N n : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i : Fin N => i.val < n)

/-- `h(y) = Λ (1 - y) / (-log y)`: the no-purchase probability `q_0` written as a function of
`q_{i'} = y` (proof of Theorem 5, p. 29, with `a_0 = 1`). -/
noncomputable def qZeroOfQip (Λ y : ℝ) : ℝ :=
  Λ * (1 - y) / (-Real.log y)

end NonRandomChoice.Assort


