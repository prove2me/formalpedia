-- Prove2me | Definitions.Def_StratifyMarkets_DoubleAuction_Instance
-- name    : StratifyMarkets_DoubleAuction_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:52:15.612854+00:00
-- url     : https://prove2.me/theorems/d0cc3051-1c53-45be-bc29-5e8a83b3e20e
-- title:
--   Double auction instances, the efficient number of trades τ, RealizedFB and the first-best FB (§2.2)
-- statement:
--   A **double auction instance** has $n$ buyers and $m$ sellers ($n,m\ge0$). Buyer $i$ has value $v_i\sim F_i$, seller $j$ has cost $c_j\sim G_j$; every $F_i$, $G_j$ is a continuous distribution supported on $[0,1]$, and all $n+m$ values and costs are mutually independent: the law of $(\mathbf v,\mathbf c)$ is the product $F_1\otimes\dots\otimes F_n\otimes G_1\otimes\dots\otimes G_m$.
--
--   For a realization, sort $v_{(1)}\ge v_{(2)}\ge\dots\ge v_{(n)}$ and $c_{(1)}\le c_{(2)}\le\dots\le c_{(m)}$. The number of trades of the efficient allocation is
--   $$\tau=\max\Big(\big\{i\in\{1,\dots,\min\{n,m\}\}:v_{(i)}>c_{(i)}\big\}\cup\{0\}\Big),$$
--   the **realized first-best gains from trade** are $\mathrm{RealizedFB}=\sum_{i=1}^{\tau}(v_{(i)}-c_{(i)})$, and the **first-best gains from trade** are
--   $$\mathrm{FB}=\mathbb E_{\mathbf v,\mathbf c}[\mathrm{RealizedFB}].$$
--   The proof of Theorem 4.1 splits FB as $\mathbb E[\mathrm{RealizedFB}\cdot\mathbb 1\{\tau>5\}]+\mathbb E[\mathrm{RealizedFB}\cdot\mathbb 1\{\tau\le5\}]$; both parts are defined here.
--
--   **Formalization Note.** `DAInstance n m` bundles `μB : Fin n → Measure ℝ`, `μS : Fin m → Measure ℝ`, each a probability measure with no atoms (`NullSingletonClass`) and mass 1 on `Icc 0 1`. `law = (Measure.pi μB).prod (Measure.pi μS)`; a point is `x = (𝐯, 𝐜)`. The sorted lists are `List.mergeSort` of `List.ofFn v` (descending) and of `List.ofFn c` (ascending); `tau` takes 0-based indices `i < min n m` (the paper's $i+1$) with `c_(i+1) < v_(i+1)` and returns the largest `i+1` (0 if none); `realizedFB` sums `v_(i+1) − c_(i+1)` over `i < τ`. Ties among values do not affect the sorted lists. All integrands are bounded on the support and measurable, hence integrable.
-- source:
--   Deng, Lin, Schoepflin, Wang, Stratifying Markets for Efficient Trade, STOC 2027 submission (manuscript sha256 49372bcf…), pp. 11–12, §2.2

import Mathlib

open MeasureTheory

namespace StratifyMarkets.DoubleAuction

/-- A double auction instance (§2.2, pp. 11–12): `n` buyers and `m` sellers, buyer `i` has value
`v_i ∼ F_i` (law `μB i`), seller `j` has cost `c_j ∼ G_j` (law `μS j`); every law is a continuous
(no atoms) probability measure supported on `[0, 1]`. Mutual independence of all `n + m` values and
costs is built into `DAInstance.law`, the product measure. Any `n, m : ℕ` are allowed. -/
structure DAInstance (n m : ℕ) where
  /-- the law of buyer `i`'s value (CDF `F_i`) -/
  μB : Fin n → Measure ℝ
  /-- the law of seller `j`'s cost (CDF `G_j`) -/
  μS : Fin m → Measure ℝ
  isProb_B : ∀ i, IsProbabilityMeasure (μB i)
  isProb_S : ∀ j, IsProbabilityMeasure (μS j)
  noAtoms_B : ∀ i, NullSingletonClass (μB i)
  noAtoms_S : ∀ j, NullSingletonClass (μS j)
  support_B : ∀ i, μB i (Set.Icc 0 1) = 1
  support_S : ∀ j, μS j (Set.Icc 0 1) = 1

/-- The joint law of `(𝐯, 𝐜)`: the product `F₁ ⊗ ⋯ ⊗ F_n ⊗ G₁ ⊗ ⋯ ⊗ G_m` (all values and costs
mutually independent). A point `x` is `x.1 = 𝐯 : Fin n → ℝ`, `x.2 = 𝐜 : Fin m → ℝ`. -/
noncomputable def DAInstance.law {n m : ℕ} (I : DAInstance n m) :
    Measure ((Fin n → ℝ) × (Fin m → ℝ)) :=
  (Measure.pi I.μB).prod (Measure.pi I.μS)

/-- The values sorted in descending order, `v_(1) ≥ v_(2) ≥ ⋯ ≥ v_(n)` (p. 12), as a list
(0-based: entry `i` is `v_(i+1)`). -/
noncomputable def valuesDesc {n : ℕ} (v : Fin n → ℝ) : List ℝ :=
  (List.ofFn v).mergeSort (fun a b => decide (b ≤ a))

/-- The costs sorted in ascending order, `c_(1) ≤ c_(2) ≤ ⋯ ≤ c_(m)` (p. 12), as a list
(0-based: entry `i` is `c_(i+1)`). -/
noncomputable def costsAsc {m : ℕ} (c : Fin m → ℝ) : List ℝ :=
  (List.ofFn c).mergeSort (fun a b => decide (a ≤ b))

/-- `τ = max({i ∈ {1, …, min{n, m}} : v_(i) > c_(i)} ∪ {0})` (p. 12), the number of trades of the
efficient allocation. The 0-based index `i < min n m` stands for the paper's `i + 1`. -/
noncomputable def tau {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) : ℕ :=
  ((Finset.range (min n m)).filter
      (fun i => (costsAsc c).getD i 0 < (valuesDesc v).getD i 0)).sup (fun i => i + 1)

/-- `RealizedFB = Σ_{i=1}^{τ} (v_(i) − c_(i))` (p. 12), the realized first-best gains from trade. -/
noncomputable def realizedFB {n m : ℕ} (v : Fin n → ℝ) (c : Fin m → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (tau v c), ((valuesDesc v).getD i 0 - (costsAsc c).getD i 0)

/-- The first-best gains from trade `FB = E_{𝐯,𝐜}[RealizedFB]` (p. 12). -/
noncomputable def DAInstance.FB {n m : ℕ} (I : DAInstance n m) : ℝ :=
  ∫ x, realizedFB x.1 x.2 ∂I.law

/-- `E_{𝐯,𝐜}[RealizedFB · 1{τ > 5}]` (Lemmas 4.10, 4.11). -/
noncomputable def DAInstance.FBtauGt5 {n m : ℕ} (I : DAInstance n m) : ℝ :=
  ∫ x, (if 5 < tau x.1 x.2 then realizedFB x.1 x.2 else 0) ∂I.law

/-- `E_{𝐯,𝐜}[RealizedFB · 1{τ ≤ 5}]` (Lemma 4.20). -/
noncomputable def DAInstance.FBtauLe5 {n m : ℕ} (I : DAInstance n m) : ℝ :=
  ∫ x, (if tau x.1 x.2 ≤ 5 then realizedFB x.1 x.2 else 0) ∂I.law

end StratifyMarkets.DoubleAuction


