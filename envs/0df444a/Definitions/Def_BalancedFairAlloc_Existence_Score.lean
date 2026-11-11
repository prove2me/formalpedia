-- Prove2me | Definitions.Def_BalancedFairAlloc_Existence_Score
-- name    : BalancedFairAlloc_Existence_Score
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:36:46.625706+00:00
-- url     : https://prove2.me/theorems/bd949e11-49d4-46ab-ac6a-3ce6acb42896
-- title:
--   Price profiles, the prefix potential Φ_p, the score S and its maximizers R, residual envy f_ij, flows F_ij, KKM labels d_i, label sets F_i, and L_i, U_i (§3.3-§3.6)
-- statement:
--   Fix a price vector $p\in\mathbb R^M$ (`p : Fin m → ℝ`) and write $r=\lfloor m/n\rfloor$, $q=\lceil m/n\rceil$.
--
--   **Profiles and prefix potential (§3.3).** For a bundle $X$, the **positive-price profile** lists the prices $p_g>0$ of the items of $X$ in non-increasing order, padded with zeros (`posProfile p X k` is its entry at 0-based position $k$); the **negative-price magnitude profile** does the same with the magnitudes $-p_g$ of the negative prices (`negProfile`). $h^{p,+}_\ell(X)$ and $h^{p,-}_\ell(X)$ are the sums of their first $\ell$ entries (`prefixPos`, `prefixNeg`), and eq. (12) defines
--
--   $$\Phi_p(A)=\sum_{i\in N}\sum_{\ell=1}^{r+1}\big(h^{p,+}_\ell(A_i)+h^{p,-}_\ell(A_i)\big).$$
--
--   For weights $\alpha$ and $\varepsilon>0$ the **score** (13) is $S(A)=\sum_i\alpha_iv_i(A_i)+\varepsilon\Phi_p(A)$ (`score v α p ε A`), and `scoreMaximizers v α p ε` is the set $R$ of its maximizers over balanced integral allocations. In the paper $\alpha=\alpha(w)$ and $p=p^\lambda(w)$, the regularized dual prices; then this set is $R_{\lambda,\varepsilon}(w)$. `ProfilesInterlace p X Y` says that, for the positive profiles $a$ of $X$ and $b$ of $Y$ (1-based), $a_{\ell+1}\le b_\ell$ and $b_{\ell+1}\le a_\ell$ for every $\ell\ge1$, and the same for the negative-price magnitude profiles.
--
--   **Private items and residual envy (§3.5).** A bundle of the smaller size $q-1$, which happens exactly when $n\nmid m$ and $|A_i|=r$ (`IsPadded A i`), receives a private item of value $0$; the result is $\widehat A_i$. With the envy $e_{ij}(A)=v_i(A_j)-v_i(A_i)$, the residual envy (20) is
--
--   $$f_{ij}(A)=\min\Big(e_{ij}(A),\ e_{ij}(A)+\min_{h\in\widehat A_i}v_{ih}-\max_{g\in\widehat A_j}v_{ig}\Big)\qquad(\texttt{residualEnvy}).$$
--
--   **Flows and labels.** For $\gamma>0$ and weights $\alpha$: $F_{ij}(A)=[\alpha_if_{ij}(A)+\gamma(\alpha_j-\alpha_i)]_+$ (`flow`, eq. (21)) and $d_i(A)=\sum_{j\ne i}F_{ij}(A)-\sum_{j\ne i}F_{ji}(A)$ (`label`, eq. (22)). For a price map $w\mapsto p(w)$, the label set (23) is $F_i=\{w\in\Delta:\ \text{some }A\in R(\alpha(w),p(w),\varepsilon)\text{ has }d_i(A)=\min_kd_k(A)\}$, labels taken with weights $\alpha(w)$ (`labelSet v ρ γ ε pmap i`); with $p=p^\lambda$ it is $F_i^{\lambda,\varepsilon}$.
--
--   **Price intervals (26).** With $S_i(X)=\sum_{g\in X_i}p_g$, $M_i(X)=\max_{g\in X_i}p_g$, $m_i(X)=\min_{g\in X_i}p_g$: $L_i(X)=S_i-M_i$ if $|X_i|=q$ and $S_i-\max\{0,M_i\}$ if $|X_i|=q-1$ (`priceL`); $U_i(X)=S_i-m_i$ if $|X_i|=q$ or $\xi_i<0$, and $S_i-\min\{0,m_i\}$ otherwise (`priceU p ξ`).
--
--   **Formalization Note.** Profiles are functions of a 0-based index, padded with zeros indefinitely, so the paper's padding to length $r+1$ is the restriction to the first $r+1$ entries. Minima and maxima over a bundle (`minOn`, `maxOn`) take the value $0$ on an empty bundle; balanced bundles are nonempty when $r\ge1$. Lemma 11 also allows unbalanced witnesses, where the zero fallback may be used; its flow argument only needs the stated residual-envy bounds and minimum-label inequalities. "Size $q-1$" is encoded as `m % n ≠ 0 ∧ |A_i| = m / n`, which for balanced allocations with $m\ge1$ is the same condition.
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), pp. 15-16 (PDF 17-18), eqs. (12), (13) and Lemma 5; pp. 19-20 (PDF 21-22), eqs. (20)-(23); p. 22 (PDF 24), eq. (26)

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Model

namespace BalancedFairAlloc.Existence

open Finset

noncomputable section

/-! ### Price profiles, the prefix potential, the score, residual envy, flows and KKM labels

Cookson, Shah, Verma, *Fair and Efficient Balanced Allocations for Additive Valuations*,
arXiv:2608.06325, §3.3–§3.6 (pp. 15–22): eqs. (12), (13), (20)–(23), (26).
Throughout, `p : Fin m → ℝ` is a price vector and `r = m / n`. -/

/-- The positive-price profile of a bundle `X` (§3.3, Lemma 5): the prices `p_g > 0` of the items
of `X`, sorted in non-increasing order and padded with zeros; `posProfile p X k` is the
`(k+1)`-st entry (0-based index `k`). -/
def posProfile {m : ℕ} (p : Fin m → ℝ) (X : Finset (Fin m)) (k : ℕ) : ℝ :=
  (((X.filter (fun g => 0 < p g)).val.map p).sort (· ≥ ·)).getD k 0

/-- The negative-price magnitude profile of `X`: the magnitudes `-p_g` of the negative prices of
the items of `X`, sorted in non-increasing order and padded with zeros (0-based index `k`). -/
def negProfile {m : ℕ} (p : Fin m → ℝ) (X : Finset (Fin m)) (k : ℕ) : ℝ :=
  (((X.filter (fun g => p g < 0)).val.map (fun g => -p g)).sort (· ≥ ·)).getD k 0

/-- `h^{p,+}_ℓ(X)`: the sum of the first `ℓ` entries of the positive-price profile. -/
def prefixPos {m : ℕ} (p : Fin m → ℝ) (X : Finset (Fin m)) (ℓ : ℕ) : ℝ :=
  ∑ k ∈ range ℓ, posProfile p X k

/-- `h^{p,−}_ℓ(X)`: the sum of the first `ℓ` entries of the negative-price magnitude profile. -/
def prefixNeg {m : ℕ} (p : Fin m → ℝ) (X : Finset (Fin m)) (ℓ : ℕ) : ℝ :=
  ∑ k ∈ range ℓ, negProfile p X k

/-- The prefix potential of eq. (12):
`Φ_p(A) = ∑_i ∑_{ℓ=1}^{r+1} (h^{p,+}_ℓ(A_i) + h^{p,−}_ℓ(A_i))`. -/
def prefixPotential {n m : ℕ} (p : Fin m → ℝ) (A : Allocation n m) : ℝ :=
  ∑ i, ∑ ℓ ∈ Icc 1 (m / n + 1), (prefixPos p (bundle A i) ℓ + prefixNeg p (bundle A i) ℓ)

/-- The score of eq. (13) with weights `α` and prices `p`:
`S(A) = ∑_i α_i v_i(A_i) + ε Φ_p(A)`. In the paper `α = α(w)` and `p = p^λ(w)`. -/
def score {n m : ℕ} (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ) (p : Fin m → ℝ) (ε : ℝ)
    (A : Allocation n m) : ℝ :=
  ∑ i, α i * bval v i (bundle A i) + ε * prefixPotential p A

/-- `R` (p. 16): the maximizers of the score over the finite set of balanced integral
allocations. `R_{λ,ε}(w)` is `scoreMaximizers v (alphaW ρ w) (p^λ(w)) ε`. -/
def scoreMaximizers {n m : ℕ} (v : Fin n → Fin m → ℝ) (α : Fin n → ℝ) (p : Fin m → ℝ)
    (ε : ℝ) : Set (Allocation n m) :=
  {A | IsBalanced A ∧ ∀ B : Allocation n m, IsBalanced B → score v α p ε B ≤ score v α p ε A}

/-- Price interlacing between two bundles (the conclusion of Lemma 5): with `a`, `b` the
positive-price profiles of `X`, `Y` (0-based), `a_{k+1} ≤ b_k` and `b_{k+1} ≤ a_k` for every
`k ≥ 0`, and the same for the negative-price magnitude profiles. -/
def ProfilesInterlace {m : ℕ} (p : Fin m → ℝ) (X Y : Finset (Fin m)) : Prop :=
  ∀ k : ℕ,
    posProfile p X (k + 1) ≤ posProfile p Y k ∧ posProfile p Y (k + 1) ≤ posProfile p X k ∧
    negProfile p X (k + 1) ≤ negProfile p Y k ∧ negProfile p Y (k + 1) ≤ negProfile p X k

/-- Agent `i`'s bundle has the smaller size `q − 1` (`q = ⌈m/n⌉`) and so receives a private
zero-valued item (§3.5): this happens exactly when `n ∤ m` and `|A_i| = r`. -/
abbrev IsPadded {n m : ℕ} (A : Allocation n m) (i : Fin n) : Prop :=
  m % n ≠ 0 ∧ (bundle A i).card = m / n

/-- `min_{g ∈ S} f g`, and `0` on the empty set (balanced bundles are nonempty when `r ≥ 1`). -/
def minOn {m : ℕ} (f : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  if h : S.Nonempty then S.inf' h f else 0

/-- `max_{g ∈ S} f g`, and `0` on the empty set (balanced bundles are nonempty when `r ≥ 1`). -/
def maxOn {m : ℕ} (f : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  if h : S.Nonempty then S.sup' h f else 0

/-- `min_{h ∈ Â_i} v_{ih}`, where `Â_i` adds a private item of value `0` to a bundle of size
`q − 1` (§3.5). -/
def hatMin {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Allocation n m) (i : Fin n) : ℝ :=
  if IsPadded A i then min 0 (minOn (v i) (bundle A i)) else minOn (v i) (bundle A i)

/-- `max_{g ∈ Â_j} v_{ig}`, where `Â_j` adds a private item of value `0` to a bundle of size
`q − 1` (§3.5). -/
def hatMax {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Allocation n m) (i j : Fin n) : ℝ :=
  if IsPadded A j then max 0 (maxOn (v i) (bundle A j)) else maxOn (v i) (bundle A j)

/-- The envy `e_{ij}(A) = v_i(A_j) − v_i(A_i)`. -/
def envy {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Allocation n m) (i j : Fin n) : ℝ :=
  bval v i (bundle A j) - bval v i (bundle A i)

/-- The residual envy of eq. (20):
`f_{ij}(A) = min(e_{ij}(A), e_{ij}(A) + min_{h ∈ Â_i} v_{ih} − max_{g ∈ Â_j} v_{ig})`. -/
def residualEnvy {n m : ℕ} (v : Fin n → Fin m → ℝ) (A : Allocation n m) (i j : Fin n) : ℝ :=
  min (envy v A i j) (envy v A i j + hatMin v A i - hatMax v A i j)

/-- The flow of eq. (21) for weights `α` and tolerance `γ`:
`F_{ij}(A) = [α_i f_{ij}(A) + γ (α_j − α_i)]_+` (used for `i ≠ j`). In the paper `α = α(w)`. -/
def flow {n m : ℕ} (v : Fin n → Fin m → ℝ) (γ : ℝ) (α : Fin n → ℝ) (A : Allocation n m)
    (i j : Fin n) : ℝ :=
  max (α i * residualEnvy v A i j + γ * (α j - α i)) 0

/-- The label of eq. (22): `d_i(A) = ∑_{j ≠ i} F_{ij}(A) − ∑_{j ≠ i} F_{ji}(A)`. -/
def label {n m : ℕ} (v : Fin n → Fin m → ℝ) (γ : ℝ) (α : Fin n → ℝ) (A : Allocation n m)
    (i : Fin n) : ℝ :=
  ∑ j ∈ univ.erase i, flow v γ α A i j - ∑ j ∈ univ.erase i, flow v γ α A j i

/-- The label set of eq. (23) for a price map `w ↦ pmap w` (in the paper `pmap = p^λ`):
`F_i = {w ∈ Δ : some A ∈ R(w) has d_i(A, w) = min_k d_k(A, w)}`, with weights `α(w)`. -/
def labelSet {n m : ℕ} (v : Fin n → Fin m → ℝ) (ρ γ ε : ℝ) (pmap : (Fin n → ℝ) → Fin m → ℝ)
    (i : Fin n) : Set (Fin n → ℝ) :=
  {w | w ∈ stdSimplex ℝ (Fin n) ∧
    ∃ A ∈ scoreMaximizers v (alphaW ρ w) (pmap w) ε,
      ∀ k, label v γ (alphaW ρ w) A i ≤ label v γ (alphaW ρ w) A k}

/-- `L_i(X)` of eq. (26), with `S_i = p(X_i)`, `M_i = max_{g ∈ X_i} p_g`:
`S_i − M_i` if `|X_i| = q`, and `S_i − max{0, M_i}` if `|X_i| = q − 1`. -/
def priceL {n m : ℕ} (p : Fin m → ℝ) (X : Allocation n m) (i : Fin n) : ℝ :=
  if IsPadded X i then (∑ g ∈ bundle X i, p g) - max 0 (maxOn p (bundle X i))
  else (∑ g ∈ bundle X i, p g) - maxOn p (bundle X i)

/-- `U_i(X)` of eq. (26), with `S_i = p(X_i)`, `m_i = min_{g ∈ X_i} p_g`: `S_i − m_i` if
`|X_i| = q` or `ξ_i < 0`, and `S_i − min{0, m_i}` otherwise. -/
def priceU {n m : ℕ} (p : Fin m → ℝ) (ξ : Fin n → ℝ) (X : Allocation n m) (i : Fin n) : ℝ :=
  if IsPadded X i ∧ 0 ≤ ξ i then (∑ g ∈ bundle X i, p g) - min 0 (minOn p (bundle X i))
  else (∑ g ∈ bundle X i, p g) - minOn p (bundle X i)

end

end BalancedFairAlloc.Existence


