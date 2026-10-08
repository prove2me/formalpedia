-- Prove2me | Definitions.Def_ClassifAgg_Aggregation_Procedure
-- name    : ClassifAgg_Aggregation_Procedure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:16:02.407537+00:00
-- url     : https://prove2.me/theorems/97c28ad5-295b-4fcc-81e6-e5a7d069a662
-- title:
--   §3, pp. 143–144; proof of Theorem 3, p. 152 — ERM classifiers G_nk, thresholds T_nk, the sets 𝒩_kj, admissibility, ĵ, G*_n and G_nkj
-- statement:
--   The aggregation procedure of Section 3 at one sample size $n$.
--
--   Let $\mathcal N_1,\dots,\mathcal N_N$ be classes of sets (the approximating sets) with complexities $\rho_1,\dots,\rho_N$, and let $s=((X_1,Y_1),\dots,(X_n,Y_n))$ be the sample.
--
--   1. **ERM classifiers.** $G_{nk}=\arg\min_{G\in\mathcal N_k}R_n(G)$, $k=1,\dots,N$: any choice, measurable or not, of a minimizer of the empirical risk over $\mathcal N_k$ at every sample.
--   2. **Thresholds.**
--   $$T_{nk}(G,G')=(\log^2 n)\max\Big\{n^{-1/(1+\rho_k)},\ \frac1{\sqrt n}\,d_{\triangle,e}^{(1-\rho_k)/2}(G,G')\Big\}.$$
--   3. **The sets $\mathcal N_{kj}$.** For $j\le k$, $\mathcal N_{kj}=\{G\in\mathcal N_j:|R_n(G)-R_n(G_{nk})|\le T_{nk}(G,G_{nk})\}$.
--   4. **Admissibility.** The index $j$ is admissible if $\mathcal N_{kj}\ne\emptyset$ for all $k$ with $j\le k\le N$.
--   5. **The selected index and the adaptive classifier.** $\hat j=\min\{\text{admissible } j\}$ and $G^*_n=G_{n\hat j}$.
--   6. **Pseudoclassifiers (proof of Theorem 3, p. 152).** $G_{nkj}=\arg\min_{G\in\mathcal N_{kj}}R_n(G)$ if $\mathcal N_{kj}\ne\emptyset$, and $G_{nkj}=G_{nk}$ otherwise.
--
--   The adaptive classifier $G^*_n$ is the object of Theorem 3: it uses neither the true class containing $G^*$ nor the margin parameter.
--
--   **Formalization Note** $\log^2 n$ is $(\log n)^2$. "arg min" is read as *any* minimizer, as the remark after Theorem 1 presupposes (pp. 141–142); the theorems are stated for every such selection. $\hat j$ is the natural-number infimum of the set of admissible indices in $\{1,\dots,N\}$; when $N\ge1$ and $G_{nN}\in\mathcal N_N$, the index $N$ is admissible ($G_{nN}\in\mathcal N_{NN}$), so the set is nonempty and the infimum is its minimum, as the page notes. The page defines $G_{nkj}$ only for $k\ge j$; the selection rule here also covers $j>k$ by the page's fallback branch $G_{nk}$. This only matters on the event $\{\hat j>j^*\}$ in Lemmas 4–6, whose probability is $o(1/n)$ by Lemma 1, and all quantities involved are bounded.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, §3, pp. 143–144 (G_nk, (A3)–(A4), T_nk, 𝒩_kj, ĵ, G*_n); proof of Theorem 3, p. 152 (G_nkj)

import Mathlib
import Definitions.Def_ClassifAgg_Aggregation_Classes

namespace ClassifAgg.Aggregation

open MeasureTheory

/-- `Ĝ` is an empirical risk minimizer over `𝒩` (display (8), p. 140, and `G_{nk}`, p. 143): at
every sample `s`, `Ĝ(s) ∈ 𝒩` and `Rₙ(Ĝ(s)) ≤ Rₙ(G)` for all `G ∈ 𝒩`. "arg min" is read as *any*
minimizer; for nonempty `𝒩` one exists, since `Rₙ` takes at most `n + 1` values. -/
def IsERM {d n : ℕ} (net : Set (Set (E d))) (Ghat1 : (Fin n → E d × Bool) → Set (E d)) : Prop :=
  ∀ s, Ghat1 s ∈ net ∧ ∀ G ∈ net, empRisk s (Ghat1 s) ≤ empRisk s G

/-- The threshold `T_{nk}(G, G') = (log² n) · max{n^{-1/(1+ρ_k)}, n^{-1/2} d_{△,e}^{(1-ρ_k)/2}(G, G')}`
(p. 143), with `ρk = ρ_k` and `log² n = (log n)²`. -/
noncomputable def threshold {d : ℕ} (n : ℕ) (ρk : ℝ) (G G' : Set (E d))
    (s : Fin n → E d × Bool) : ℝ :=
  (Real.log n) ^ 2 *
    max ((n : ℝ) ^ (-1 / (1 + ρk))) (1 / Real.sqrt n * dTriEmp s G G' ^ ((1 - ρk) / 2))

/-- The set `𝒩_{kj} = {G ∈ 𝒩_j : |Rₙ(G) − Rₙ(G_{nk})| ≤ T_{nk}(G, G_{nk})}` (p. 143), for the
nets `net j = 𝒩_j`, complexities `ρ j = ρ_j` and ERM classifiers `Ghat k = G_{nk}` at sample size
`n`. -/
def admSet {d : ℕ} (n : ℕ) (net : ℕ → Set (Set (E d))) (ρ : ℕ → ℝ)
    (Ghat : ℕ → (Fin n → E d × Bool) → Set (E d)) (k j : ℕ) (s : Fin n → E d × Bool) :
    Set (Set (E d)) :=
  {G | G ∈ net j ∧ |empRisk s G - empRisk s (Ghat k s)| ≤ threshold n (ρ k) G (Ghat k s) s}

/-- The index `j` is admissible (p. 143) if `𝒩_{kj} ≠ ∅` for every `k` with `j ≤ k ≤ N`. -/
def Admissible {d : ℕ} (n N : ℕ) (net : ℕ → Set (Set (E d))) (ρ : ℕ → ℝ)
    (Ghat : ℕ → (Fin n → E d × Bool) → Set (E d)) (j : ℕ) (s : Fin n → E d × Bool) : Prop :=
  ∀ k, j ≤ k → k ≤ N → (admSet n net ρ Ghat k j s).Nonempty

/-- `ĵ = min{admissible j}` (p. 143), the least admissible index in `{1, …, N}`. When
`1 ≤ N` and `Ghat N s ∈ net N`, the index `N` is admissible (`G_{nN} ∈ 𝒩_{NN}`, since
`|Rₙ − Rₙ| = 0 ≤ T_{nN}`), so the set is nonempty and `sInf` is its minimum. -/
noncomputable def jhat {d : ℕ} (n N : ℕ) (net : ℕ → Set (Set (E d))) (ρ : ℕ → ℝ)
    (Ghat : ℕ → (Fin n → E d × Bool) → Set (E d)) (s : Fin n → E d × Bool) : ℕ :=
  sInf {j | 1 ≤ j ∧ j ≤ N ∧ Admissible n N net ρ Ghat j s}

/-- The adaptive classifier `G*ₙ = G_{nĵ}` (p. 144). -/
noncomputable def adaptive {d : ℕ} (n N : ℕ) (net : ℕ → Set (Set (E d))) (ρ : ℕ → ℝ)
    (Ghat : ℕ → (Fin n → E d × Bool) → Set (E d)) (s : Fin n → E d × Bool) : Set (E d) :=
  Ghat (jhat n N net ρ Ghat s) s

/-- `Gtil k j` is a choice of the pseudoclassifiers `G_{nkj}` of the proof of Theorem 3 (p. 152):
if `j ≤ k` and `𝒩_{kj} ≠ ∅`, then `Gtil k j s` is a minimizer of `Rₙ` over `𝒩_{kj}`; otherwise it is
`G_{nk}`. The page defines `G_{nkj}` for `k ≥ j` only; the fallback branch `G_{nk}` is extended
to `j > k`. -/
def IsPseudoSel {d : ℕ} (n : ℕ) (net : ℕ → Set (Set (E d))) (ρ : ℕ → ℝ)
    (Ghat : ℕ → (Fin n → E d × Bool) → Set (E d))
    (Gtil : ℕ → ℕ → (Fin n → E d × Bool) → Set (E d)) : Prop :=
  ∀ k j : ℕ, ∀ s : Fin n → E d × Bool,
    ((j ≤ k ∧ (admSet n net ρ Ghat k j s).Nonempty) →
      Gtil k j s ∈ admSet n net ρ Ghat k j s ∧
        ∀ G ∈ admSet n net ρ Ghat k j s, empRisk s (Gtil k j s) ≤ empRisk s G) ∧
    (¬ (j ≤ k ∧ (admSet n net ρ Ghat k j s).Nonempty) → Gtil k j s = Ghat k s)

end ClassifAgg.Aggregation


