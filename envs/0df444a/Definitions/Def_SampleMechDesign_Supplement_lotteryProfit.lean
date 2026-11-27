-- Prove2me | Definitions.Def_SampleMechDesign_Supplement_lotteryProfit
-- name    : SampleMechDesign_Supplement_lotteryProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:47:29.568712+00:00
-- url     : https://prove2.me/theorems/3e082306-d05b-5bb8-a8b5-1509466d0a98
-- title:
--   Section 3.4.4 — lottery menus and the class $\mathcal M'$
-- statement:
--   A length-$\ell$ **lottery menu** is $\{(\varphi^{(0)},p^{(0)}),\dots,(\varphi^{(\ell)},p^{(\ell)})\}\subseteq\mathbb R^m\times\mathbb R$ with $\varphi^{(0)}=0$ and $p^{(0)}=0$. Under the lottery $(\varphi^{(j)},p^{(j)})$ the buyer pays $p^{(j)}$ and receives each item $i$ with probability $\varphi^{(j)}[i]$. A buyer with values $v$ takes the entry $(\varphi_v,p_v)$ that maximizes her expected utility $\sum_iv(e_i)\varphi[i]-p$. For $z\in[0,1]^m$,
--   $$
--   \mathrm{profit}'_M(v,z)=p_v-c\Big(\sum_{j:\,z[j]<\varphi_v[j]}e_j\Big),
--   $$
--   and $\mathcal M'=\{\mathrm{profit}'_M\}$. Its parameters are the $\ell(m+1)$ numbers $(\varphi^{(1..\ell)},p^{(1..\ell)})$. For a single additive buyer the parameter set requires $\varphi^{(j)}\in[0,1]^m$.
--
--   **Formalization Note** Parameters are a vector in $\mathbb R^{\ell(m+1)}$ indexed through `finProdFinEquiv : Fin ℓ × Fin (m+1) ≃ Fin (ℓ*(m+1))`, the last coordinate of each block being the price. Points $(v,z)$ range over $\mathbb R^m\times\mathbb R^m$, which contains $z\in[0,1]^m$. Ties among utility-maximizing entries are broken by a rule that may depend on $v$; $c$ is the cost of a bundle.
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, Section 3.4.4, p.14 (PDF p.14)

import Mathlib

namespace SampleMechDesign.Supplement

open Finset

/-- **Lottery menus and the class `M′`.** Balcan, Sandholm, Vitercik, arXiv:1705.00243v6,
Section 3.4.4, p.14.

A length-`ℓ` lottery menu is `{(φ^(0), p^(0)), …, (φ^(ℓ), p^(ℓ))} ⊆ ℝ^m × ℝ` with `φ^(0) = 0`,
`p^(0) = 0`. Its parameters are the `ℓ (m + 1)` numbers `(φ^(1..ℓ), p^(1..ℓ))`, encoded as
`p : Fin (ℓ * (m + 1)) → ℝ` through `finProdFinEquiv : Fin ℓ × Fin (m + 1) ≃ Fin (ℓ * (m + 1))`:
entry `k = j + 1` has `φ^(k)[i] = p (j, i)` and price `p^(k) = p (j, m)` (`lotteryPhi`,
`lotteryPrice`). A buyer with values `v ∈ ℝ^m` takes an entry `(φ_v, p_v)` maximizing the expected
utility `∑_i v(e_i) φ[i] − p` (`lotteryDemand`; the tie-breaking rule `tb` picks one), and for
`z ∈ [0, 1]^m` the bundle is `∑_{j : z[j] < φ_v[j]} e_j` (`lotteryBundle`). The class `M′`
consists of the functions

`profit′_M(v, z) = p_v − c(∑_{j : z[j] < φ_v[j]} e_j)` (`lotteryProfit c tb p (v, z)`).

`lotteryParams ℓ m` is the parameter set of a single additive buyer: every `φ^(j)` lies in
`[0, 1]^m`, the prices are arbitrary reals.

**Formalization Note.**
* The points of `M′` are pairs `(v, z)`; the definition accepts every `z ∈ ℝ^m`, which contains
  the paper's `z ∈ [0, 1]^m`.
* Ties among utility-maximizing entries are broken by `tb`, which may depend on `v`.
* `c` is the cost of a bundle. -/
noncomputable def lotteryPhi {ℓ m : ℕ} (p : Fin (ℓ * (m + 1)) → ℝ) (k : Fin (ℓ + 1))
    (i : Fin m) : ℝ :=
  Fin.cases 0 (fun j : Fin ℓ => p (finProdFinEquiv (j, i.castSucc))) k

/-- The price `p^(k)` of menu entry `k` (`p^(0) = 0`). -/
noncomputable def lotteryPrice {ℓ m : ℕ} (p : Fin (ℓ * (m + 1)) → ℝ) (k : Fin (ℓ + 1)) : ℝ :=
  Fin.cases 0 (fun j : Fin ℓ => p (finProdFinEquiv (j, Fin.last m))) k

/-- Expected utility `∑_i v(e_i) φ^(k)[i] − p^(k)` of entry `k`. -/
noncomputable def lotteryUtility {ℓ m : ℕ} (v : Fin m → ℝ) (p : Fin (ℓ * (m + 1)) → ℝ)
    (k : Fin (ℓ + 1)) : ℝ :=
  ∑ i, v i * lotteryPhi p k i - lotteryPrice p k

/-- The utility-maximizing menu entries. -/
noncomputable def lotteryDemand {ℓ m : ℕ} (v : Fin m → ℝ) (p : Fin (ℓ * (m + 1)) → ℝ) :
    Finset (Fin (ℓ + 1)) :=
  univ.filter fun k => ∀ k', lotteryUtility v p k' ≤ lotteryUtility v p k

/-- The entry the buyer takes. -/
noncomputable def lotteryChoice {ℓ m : ℕ} (tb : (Fin m → ℝ) → Finset (Fin (ℓ + 1)) → Fin (ℓ + 1))
    (v : Fin m → ℝ) (p : Fin (ℓ * (m + 1)) → ℝ) : Fin (ℓ + 1) :=
  tb v (lotteryDemand v p)

/-- The bundle `∑_{j : z[j] < φ_v[j]} e_j`. -/
noncomputable def lotteryBundle {ℓ m : ℕ} (tb : (Fin m → ℝ) → Finset (Fin (ℓ + 1)) → Fin (ℓ + 1))
    (v z : Fin m → ℝ) (p : Fin (ℓ * (m + 1)) → ℝ) : Finset (Fin m) :=
  univ.filter fun i => z i < lotteryPhi p (lotteryChoice tb v p) i

/-- `profit′_M(v, z) = p_v − c(∑_{j : z[j] < φ_v[j]} e_j)`. -/
noncomputable def lotteryProfit {ℓ m : ℕ} (c : Finset (Fin m) → ℝ)
    (tb : (Fin m → ℝ) → Finset (Fin (ℓ + 1)) → Fin (ℓ + 1)) (p : Fin (ℓ * (m + 1)) → ℝ)
    (x : (Fin m → ℝ) × (Fin m → ℝ)) : ℝ :=
  lotteryPrice p (lotteryChoice tb x.1 p) - c (lotteryBundle tb x.1 x.2 p)

/-- Lottery parameters of an additive buyer: `φ^(j) ∈ [0, 1]^m` for `j = 1, …, ℓ`. -/
def lotteryParams (ℓ m : ℕ) : Set (Fin (ℓ * (m + 1)) → ℝ) :=
  {p | ∀ (j : Fin ℓ) (i : Fin m), lotteryPhi p j.succ i ∈ Set.Icc 0 1}

end SampleMechDesign.Supplement


