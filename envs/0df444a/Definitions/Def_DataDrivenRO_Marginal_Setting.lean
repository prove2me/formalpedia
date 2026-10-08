-- Prove2me | Definitions.Def_DataDrivenRO_Marginal_Setting
-- name    : DataDrivenRO_Marginal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:00:23.600135+00:00
-- url     : https://prove2.me/theorems/cb31e483-3eb8-4f2c-802b-513ef593989a
-- title:
--   (6), p. 10; (26), (28) and 𝒫^M, pp. 20–21 — VaR, order statistics û^(j)_i, the index s, the box 𝒰^M_ε and the region 𝒫^M
-- statement:
--   The objects of §6 of Bertsimas, Gupta and Kallus, *Data-Driven Robust Optimization*, on uncertainty sets built from marginal samples.
--
--   1. **Value at Risk.** For a probability measure $\mathbb P$ on $\mathbb R^d$, a direction $\mathbf v\in\mathbb R^d$ and a level $\epsilon$, display (6) defines
--   $$\mathrm{VaR}^{\mathbb P}_\epsilon(\mathbf v)=\inf\{t:\mathbb P(\tilde{\mathbf u}^T\mathbf v\le t)\ge 1-\epsilon\},$$
--   the $(1-\epsilon)$-quantile of $\tilde{\mathbf u}^T\mathbf v$ under $\mathbb P$.
--   2. **The a priori box.** For vectors $\hat{\mathbf u}^{(0)}\le\hat{\mathbf u}^{(N+1)}$ in $\mathbb R^d$, $[\hat{\mathbf u}^{(0)},\hat{\mathbf u}^{(N+1)}]=\{\mathbf u:\hat u^{(0)}_i\le u_i\le\hat u^{(N+1)}_i,\ i=1,\dots,d\}$ is a box known to contain the support of the unknown distribution $\mathbb P^*$.
--   3. **Order statistics.** Given a sample $\hat{\mathbf u}^1,\dots,\hat{\mathbf u}^N\in\mathbb R^d$, $\hat u^{(j)}_i$ for $1\le j\le N$ is the $j$-th smallest of $\hat u^1_i,\dots,\hat u^N_i$; for $j=0$ and $j=N+1$ it is the corresponding end of the a priori box.
--   4. **The index $s$** of (26):
--   $$s=\min\Big\{k\in\mathbb N:\sum_{j=k}^N\binom Nj(\epsilon/d)^{N-j}(1-\epsilon/d)^j\le\frac{\alpha}{2d}\Big\},$$
--   with $s=N+1$ if the set is empty. The sum is the probability that a Binomial$(N,1-\epsilon/d)$ variable is at least $k$.
--   5. **The uncertainty set** (28):
--   $$\mathcal U^M_\epsilon=\{\mathbf u\in\mathbb R^d:\hat u^{(N-s+1)}_i\le u_i\le\hat u^{(s)}_i,\ i=1,\dots,d\}.$$
--   6. **The confidence region** $\mathcal P^M$: the probability measures $\mathbb P$ on the box $[\hat{\mathbf u}^{(0)},\hat{\mathbf u}^{(N+1)}]$ such that, for every $i$,
--   $$\mathrm{VaR}^{\mathbb P}_{\epsilon/d}(\mathbf e_i)\le\hat u^{(s)}_i\quad\text{and}\quad\mathrm{VaR}^{\mathbb P}_{\epsilon/d}(-\mathbf e_i)\le-\hat u^{(N-s+1)}_i .$$
--
--   7. **The sampling model.** The data are $N$ samples of each marginal: a law $Q$ of the array $(\hat u^k_i)_{k\le N,\,i\le d}$ is admissible for $\mathbb P^*$ if it is a probability measure and, for every $i$, the samples $\hat u^1_i,\dots,\hat u^N_i$ are i.i.d. with law $\mathbb P^*_i$ (the $i$-th marginal of $\mathbb P^*$). The dependence between samples of different marginals is arbitrary; i.i.d. draws of whole vectors from $\mathbb P^*$ are one admissible law.
--
--   These are the data of Theorem 7: the region $\mathcal P^M$ is the confidence region of an order-statistic test that observes the marginals separately, and $\mathcal U^M_\epsilon$ is the box whose support function bounds the worst-case Value at Risk over it.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ` with 0-based coordinates; the sample is `S : Fin N → (Fin d → ℝ)`. VaR is the published `MultistageStochastic.valueAtRisk P (fun u => u ⬝ᵥ v) (1 - ε)`, a real infimum that is genuine for a probability measure and $0<\epsilon<1$. The order statistics use Mathlib's `Tuple.sort`. The index $N-s+1$ is written `N + 1 - s` in natural numbers, which equals the paper's value for $1\le s\le N+1$ (the only values $s$ takes when $0<\alpha<1$, $0<\epsilon<1$, $d\ge1$). The page prints the second condition of $\mathcal P^M$ as "$\mathrm{VaR}^{\mathbb P_i}_{\epsilon/d}\ge\hat u^{(N-s+1)}_i$"; the definition states the lower-tail condition that the hypothesis $H_0$, its rejection rule and the proof (EC.8) use.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, (6), p. 10; §5.1, p. 15 (order statistics, a priori box); §6, (26), 𝒫^M and (28), pp. 20–21

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_RobustMDP_Shared_supportFunction

open MeasureTheory

namespace DataDrivenRO.Marginal

/-- Value at Risk at level `ε` in direction `v`, display (6), p. 10 of Bertsimas–Gupta–Kallus,
arXiv:1401.0212v2: `VaR^ℙ_ε(v) = inf {t : ℙ(ũᵀv ≤ t) ≥ 1 − ε}`, with `ũ` the identity on
`ℝᵈ = Fin d → ℝ`. It is the published `MultistageStochastic.valueAtRisk` at level `1 − ε` applied
to `u ↦ uᵀv` (a real `sInf`, genuine when `0 < ε < 1` and `P` is a probability measure). -/
noncomputable def VaR {d : ℕ} (P : Measure (Fin d → ℝ)) (ε : ℝ) (v : Fin d → ℝ) : ℝ :=
  MultistageStochastic.valueAtRisk P (fun u => u ⬝ᵥ v) (1 - ε)

/-- The a priori box `[û^(0), û^(N+1)] = {u : loᵢ ≤ uᵢ ≤ hiᵢ, i = 1, …, d}` (§5.1, p. 15). -/
def box {d : ℕ} (lo hi : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {u | ∀ i, lo i ≤ u i ∧ u i ≤ hi i}

/-- The sampling model of §6, p. 20: "we observe samples from the marginal distributions of `ℙ*`
separately, but do not assume these marginals are independent", exactly `N` samples of each
marginal. A law `Q` of the data `S : Fin N → Fin d → ℝ` (`S k i` is the `k`-th sample of marginal
`i`) is admissible when it is a probability measure and, for every coordinate `i`, the `N` samples
`S 0 i, …, S (N-1) i` are i.i.d. from the marginal `ℙ*ᵢ`; the dependence between the samples of
different marginals is arbitrary. Joint i.i.d. draws, `Measure.pi (fun _ => ℙ*)`, are one such law. -/
def IsMarginalSampleLaw {d N : ℕ} (Pstar : Measure (Fin d → ℝ))
    (Q : Measure (Fin N → Fin d → ℝ)) : Prop :=
  IsProbabilityMeasure Q ∧
    ∀ i : Fin d, Q.map (fun S k => S k i) = Measure.pi (fun _ : Fin N => Pstar.map (fun u => u i))

/-- The order statistics of coordinate `i` of the sample `S = (û¹, …, ûᴺ)`, sorted increasingly:
`orderStat S i ⟨j, _⟩` is the `(j+1)`-th smallest of `û¹ᵢ, …, ûᴺᵢ` (§5.1, p. 15). -/
noncomputable def orderStat {d N : ℕ} (S : Fin N → Fin d → ℝ) (i : Fin d) : Fin N → ℝ :=
  (fun k => S k i) ∘ Tuple.sort (fun k => S k i)

/-- The paper's `û^(j)_i` for `j = 0, 1, …, N + 1` (§5.1, p. 15): `û^(0)_i = loᵢ` and
`û^(N+1)_i = hiᵢ` are the ends of the a priori box, and for `1 ≤ j ≤ N`, `û^(j)_i` is the `j`-th
smallest of the `N` sample values of coordinate `i`. (Indices `j > N + 1` are never used.) -/
noncomputable def uhat {d N : ℕ} (S : Fin N → Fin d → ℝ) (lo hi : Fin d → ℝ) (i : Fin d)
    (j : ℕ) : ℝ :=
  if h : j = 0 then lo i
  else if h' : N < j then hi i
  else orderStat S i ⟨j - 1, by omega⟩

open Classical in
/-- The index `s` of (26), p. 20:
`s = min {k ∈ ℕ : ∑_{j=k}^N (N choose j) (ε/d)^{N−j} (1 − ε/d)^j ≤ α/(2d)}`, and `s = N + 1` if
that set is empty. -/
noncomputable def sIndex (N d : ℕ) (ε α : ℝ) : ℕ :=
  if h : ∃ k : ℕ, ∑ j ∈ Finset.Icc k N,
      (N.choose j : ℝ) * (ε / d) ^ (N - j) * (1 - ε / d) ^ j ≤ α / (2 * d) then
    Nat.find h
  else N + 1

/-- The uncertainty set (28), p. 21:
`𝒰^M_ε = {u ∈ ℝᵈ : û^(N−s+1)_i ≤ uᵢ ≤ û^(s)_i, i = 1, …, d}` with `s` from (26). -/
noncomputable def UM {d N : ℕ} (S : Fin N → Fin d → ℝ) (lo hi : Fin d → ℝ) (ε α : ℝ) :
    Set (Fin d → ℝ) :=
  {u | ∀ i, uhat S lo hi i (N + 1 - sIndex N d ε α) ≤ u i ∧ u i ≤ uhat S lo hi i (sIndex N d ε α)}

/-- The confidence region `𝒫^M`, p. 21, with the lower-tail condition in its corrected form:
the probability measures `ℙ` on the box `[û^(0), û^(N+1)]` with, for every `i`,
`VaR^ℙ_{ε/d}(eᵢ) ≤ û^(s)_i` and `VaR^ℙ_{ε/d}(−eᵢ) ≤ −û^(N−s+1)_i`. -/
noncomputable def PM {d N : ℕ} (S : Fin N → Fin d → ℝ) (lo hi : Fin d → ℝ) (ε α : ℝ) :
    Set (Measure (Fin d → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (box lo hi)ᶜ = 0 ∧
    ∀ i, VaR P (ε / d) (Pi.single i 1) ≤ uhat S lo hi i (sIndex N d ε α) ∧
      VaR P (ε / d) (Pi.single i (-1)) ≤ -uhat S lo hi i (N + 1 - sIndex N d ε α)}

end DataDrivenRO.Marginal


