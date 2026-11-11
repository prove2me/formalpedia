-- Prove2me | Definitions.Def_DistMapClust_Main_Selection
-- name    : DistMapClust_Main_Selection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:04:43.794206+00:00
-- url     : https://prove2.me/theorems/1d3798d6-ff51-47e5-b7dd-a2e26fa64a5d
-- title:
--   Row-Wise Ordered Norm Mapping Selection, ε-nice instances, counts, cost of a count, ε-nice selections
-- statement:
--   In **Row-Wise Ordered Norm Mapping Selection** (Definition 1.8; Definition 1.3 is the case of one type) the $k$ centers are fixed and known only through distances $\delta(x_i,p)\ge0$ (not necessarily a metric); points have types $\mathrm{type}:P\to[\tau]$; the distance mappings $h_{t,\ell}:\mathbb R^k_{\ge0}\to\mathbb R^d_{\ge0}$ are arbitrary functions; the objective is a row-wise ordered norm $f=\mathrm{rowOrdNorm}(W,f')$. The goal is a selection $\sigma$ minimizing $f(U(X,\sigma))$, column $p$ being $h_{\mathrm{type}(p),\sigma(p)}(\delta_X(p))$; $\mathrm{OPT}_I$ is the minimum.
--
--   §4 writes an instance as $I=(P,U,W,f')$ with values $u(p,\ell)_i\in\bar{\mathbb R}$ and $\mathrm{cost}_I(\sigma)=f'\big((\mathrm{ord}_{w_i}((u(p,\sigma(p))_i)_p))_i\big)$, infinite if a selected value is $\infty$. With $b=2\lceil\log_{1+\varepsilon}(nd/\varepsilon)\rceil$ and $h=\lceil3\log_{1+\varepsilon}(2db/\varepsilon)\rceil$, $I$ is **$\varepsilon$-nice** (Definition 4.1) if some $a\ge0$ has every value in $\{(1+\varepsilon)^ja_i\mid j\in[b/2,b]\}\cup\{\infty\}$, optimal selections avoid $\infty$, and $(w_i)_n\ge\varepsilon(w_i)_1/n$. Writing $u(p,\ell)_i=(1+\varepsilon)^{v(p,\ell)_i}a_i$, the **count** of $\sigma$ is $c_\sigma(i,j)=|\{p\mid v(p,\sigma(p))_i=j\}|$; a count $c:[d]\times[0,b]\to\mathbb N$ is **$\varepsilon$-nice** if $c(i,j)\ge c(i,j')\,db/\varepsilon$ whenever $j\le j'-h$ (Definition 4.3). The **cost of a count** (Definition 4.4) is
--   $$\mathrm{cost}(c,i)=\sum_{j=0}^b\sum_{x=1}^n (w_i)_x\,a_i(1+\varepsilon)^j\,\big|[x-1,x)\cap\big[\textstyle\sum_{j'=j+1}^b c(i,j'),\sum_{j'=j}^b c(i,j')\big)\big| .$$
--   A selection $\sigma$ is **$\varepsilon$-nice with respect to $c$** (Definition 4.6) if $c_\sigma\le(1+\varepsilon)c$ and no point $p$ has a choice $\ell$ with $\min_i c(i,v(p,\ell)_i)\ge\min_{i'}c(i',v(p,\sigma(p))_{i'})\cdot db/\varepsilon$.
--
--   **Formalization Note.** `MapSelInstance`, `SelInstance` (values in `ℝ≥0∞`; validity of `W`, `f'` is the predicate `Valid`), `bb`, `hh`, `IsNice`, `NiceRep`, `selCount`, `IsNiceCount`, `countCost`, `IsNiceSelection`. Definition 4.4 is stated with the summand $c(i,j')$; the page prints $c(i,j)$, a typo (with it, the consistency $\mathrm{cost}(c_\sigma,i)=\mathrm{ord}_{w_i}$ claimed on p. 48 fails). "Row-wise monotone norm" in Definition 1.8 is read as row-wise ordered norm. "The optimal mapping selection" in Definition 4.1(2) is read as every optimal selection.
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 8 (Definition 1.3), p. 17 (Definition 1.8), pp. 45–46 (§4), pp. 47–49 (Definitions 4.1, 4.3, 4.4, 4.6)

import Mathlib
import Definitions.Def_DistMapClust_Main_Norms

/-!
# Row-Wise Ordered Norm Mapping Selection: instances, ε-nice instances, counts, cost of a count,
# ε-nice selections

Herold, Spoerhase, Kipouridis, Marx, *A Unified Framework for Parameterized Approximation of
Clustering Objectives via Distance Mappings*, STOC 2027 submission (manuscript sha256 1d00c842…):
Definition 1.3 (p. 8), Definition 1.8 (p. 17), §4 (pp. 45–46), Definitions 4.1, 4.3, 4.4, 4.6
(pp. 47–49).

Encoding.
* `MapSelInstance` is Definition 1.8 (Definition 1.3 is the case `τ = 1`): points `Fin n`, a fixed
  tuple of `k` centers known only through the distances `δ p i = δ(xᵢ, p) ≥ 0` (not necessarily a
  metric), types `type : Fin n → Fin τ`, distance mappings `h t ℓ : ℝ^k → ℝ^d` that are arbitrary
  functions sending `ℝ^k_{≥0}` into `ℝ^d_{≥0}`, and a row-wise ordered norm `f = rowOrdNorm W f'`
  given by `(W, f')` ("row-wise monotone norm" in Definition 1.8 is read as row-wise ordered norm).
* `SelInstance` is §4's value form `I = (P, U, W, f')`: `U p ℓ i = u(p, ℓ)ᵢ ∈ R̄ = ℝ≥0∞` (an `∞` value
  arises from Lemma 4.2's rounding). `cost_I(σ, i) = ord_{wᵢ}((u(p, σ(p))ᵢ)_p)`,
  `cost_I(σ) = f'((cost_I(σ, i))ᵢ)`; a selection meeting an `∞` value has cost `∞`.
  `OPT_I` is the minimum over the finitely many selections.
* `b = 2⌈log_{1+ε}(nd/ε)⌉`, `h = ⌈3 log_{1+ε}(2db/ε)⌉` (p. 46); `[0, b]` is `{0, …, b}`, and a
  count is a function `Fin d → ℕ → ℝ` of which only the arguments `j ≤ b` are used.
* `NiceRep I ε a v`: every value is `u(p, ℓ)ᵢ = (1 + ε)^{v(p,ℓ)ᵢ} aᵢ` with `v(p, ℓ)ᵢ ∈ [b/2, b]`; this
  is the paper's `v(p, ℓ)` under its standing assumption (p. 47, after Lemma 4.2) that every value is
  finite.
* Definition 4.4 is stated with the summand `c(i, j')` (the page prints `c(i, j)`: a typo).
-/

open scoped ENNReal

namespace DistMapClust.Main

/-- An instance of Row-Wise Ordered Norm Mapping Selection (Definition 1.8; Definition 1.3 when
`τ = 1`). -/
structure MapSelInstance where
  n : ℕ
  k : ℕ
  d : ℕ
  ψ : ℕ
  τ : ℕ
  n_pos : 0 < n
  k_pos : 0 < k
  d_pos : 0 < d
  ψ_pos : 0 < ψ
  τ_pos : 0 < τ
  /-- `δ p i = δ(xᵢ, p)`, the distance of point `p` to the `i`-th fixed center -/
  δ : Fin n → Fin k → ℝ
  /-- the type of each point -/
  type : Fin n → Fin τ
  /-- the distance mappings `h_{t,ℓ}` -/
  h : Fin τ → Fin ψ → (Fin k → ℝ) → (Fin d → ℝ)
  /-- the weight vectors of the row-wise ordered norm -/
  W : Fin d → Fin n → ℝ
  /-- the outer monotone norm -/
  f' : (Fin d → ℝ) → ℝ
  δ_nonneg : ∀ p i, 0 ≤ δ p i
  h_nonneg : ∀ t ℓ z, 0 ≤ z → 0 ≤ h t ℓ z
  W_weight : ∀ i, IsWeightVector (W i)
  f'_norm : IsMonotoneNorm f'

namespace MapSelInstance

variable (I : MapSelInstance)

/-- The cost matrix `U(X, σ)`: column `p` is `h_{type(p), σ(p)}(δ_X(p))`. -/
def costMatrix (σ : Fin I.n → Fin I.ψ) : Mat I.d I.n :=
  fun j p => I.h (I.type p) (σ p) (I.δ p) j

/-- The objective `f(U(X, σ))` with `f = rowOrdNorm W f'`. -/
noncomputable def cost (σ : Fin I.n → Fin I.ψ) : ℝ :=
  rowOrdNorm I.W I.f' (I.costMatrix σ)

/-- `OPT_I = min_σ f(U(X, σ))` over the finitely many selections. -/
noncomputable def OPT : ℝ :=
  haveI : Nonempty (Fin I.ψ) := ⟨⟨0, I.ψ_pos⟩⟩
  Finset.univ.inf' Finset.univ_nonempty I.cost

end MapSelInstance

/-- §4's value form `I = (P, U, W, f')` of an instance of Row-Wise Ordered Norm Mapping Selection,
with values in `R̄ = ℝ≥0∞`. -/
structure SelInstance where
  n : ℕ
  d : ℕ
  ψ : ℕ
  n_pos : 0 < n
  d_pos : 0 < d
  ψ_pos : 0 < ψ
  /-- `U p ℓ i = u(p, ℓ)ᵢ`, the `i`-cost of `p`'s `ℓ`-choice -/
  U : Fin n → Fin ψ → Fin d → ℝ≥0∞
  /-- the weight vectors -/
  W : Fin d → Fin n → ℝ
  /-- the outer monotone norm -/
  f' : (Fin d → ℝ) → ℝ

namespace SelInstance

variable (I : SelInstance)

/-- The weights are weight vectors and `f'` is a monotone norm (kept as a predicate, so that a list
of instances written by a program can be decoded before its validity is asserted). -/
def Valid : Prop := (∀ i, IsWeightVector (I.W i)) ∧ IsMonotoneNorm I.f'

/-- `cost_I(σ) = f'((ord_{wᵢ}((u(p, σ(p))ᵢ)_p))ᵢ)`, and `∞` if some selected value is `∞`. -/
noncomputable def cost (σ : Fin I.n → Fin I.ψ) : ℝ≥0∞ :=
  open Classical in
  if ∀ p i, I.U p (σ p) i ≠ ⊤ then
    ENNReal.ofReal (I.f' (fun i => ordNorm (I.W i) (fun p => (I.U p (σ p) i).toReal)))
  else ⊤

/-- `OPT_I = min_σ cost_I(σ)`. -/
noncomputable def OPT : ℝ≥0∞ :=
  haveI : Nonempty (Fin I.ψ) := ⟨⟨0, I.ψ_pos⟩⟩
  Finset.univ.inf' Finset.univ_nonempty I.cost

/-- `σ` is an optimal mapping selection. -/
def IsOptimal (σ : Fin I.n → Fin I.ψ) : Prop := I.cost σ = I.OPT

/-- `b = 2⌈log_{1+ε}(nd/ε)⌉` (p. 46). -/
noncomputable def bb (ε : ℝ) : ℕ := 2 * ⌈Real.logb (1 + ε) ((I.n : ℝ) * I.d / ε)⌉₊

/-- `h = ⌈3 log_{1+ε}(2db/ε)⌉` (p. 46). -/
noncomputable def hh (ε : ℝ) : ℕ := ⌈3 * Real.logb (1 + ε) (2 * (I.d : ℝ) * I.bb ε / ε)⌉₊

/-- The instance is `ε`-nice (Definition 4.1): (1) there is `a ∈ ℝ^d` with every `u(p, ℓ)ᵢ` in
`{(1 + ε)^j aᵢ | j ∈ [b/2, b]} ∪ {∞}` (`a ≥ 0`, as the values are nonnegative reals); (2) an optimal selection has no `∞` value (read for every
optimal selection); (3) `(wᵢ)_n ≥ ε (wᵢ)_1 / n` for every weight vector. -/
def IsNice (ε : ℝ) : Prop :=
  (∃ a : Fin I.d → ℝ, 0 ≤ a ∧ ∀ p ℓ i, I.U p ℓ i = ⊤ ∨
    ∃ j : ℕ, I.bb ε / 2 ≤ j ∧ j ≤ I.bb ε ∧ I.U p ℓ i = ENNReal.ofReal ((1 + ε) ^ j * a i)) ∧
  (∀ σ, I.IsOptimal σ → ∀ p i, I.U p (σ p) i ≠ ⊤) ∧
  (∀ i, ε * I.W i ⟨0, I.n_pos⟩ / I.n ≤ I.W i ⟨I.n - 1, Nat.sub_lt I.n_pos Nat.one_pos⟩)

/-- `a ≥ 0`, and every value is finite and equals `(1 + ε)^{v(p,ℓ)ᵢ} aᵢ` with `v(p, ℓ)ᵢ ∈ [b/2, b]`; `v` is the
paper's `v(p, ℓ)` (p. 47). -/
def NiceRep (ε : ℝ) (a : Fin I.d → ℝ) (v : Fin I.n → Fin I.ψ → Fin I.d → ℕ) : Prop :=
  0 ≤ a ∧ ∀ p ℓ i, I.bb ε / 2 ≤ v p ℓ i ∧ v p ℓ i ≤ I.bb ε ∧
    I.U p ℓ i = ENNReal.ofReal ((1 + ε) ^ (v p ℓ i) * a i)

/-- The count of a selection (Definition 4.3): `c_σ(i, j) = |{p | v(p, σ(p))ᵢ = j}|`. -/
def selCount (v : Fin I.n → Fin I.ψ → Fin I.d → ℕ) (σ : Fin I.n → Fin I.ψ) (i : Fin I.d)
    (j : ℕ) : ℕ :=
  (Finset.univ.filter (fun p => v p (σ p) i = j)).card

/-- An `ε`-nice count (Definition 4.3): `c(i, j) ≥ c(i, j') · (d · b / ε)` for all `i` and all
`j, j' ∈ [0, b]` with `j ≤ j' − h`. -/
def IsNiceCount (ε : ℝ) (c : Fin I.d → ℕ → ℕ) : Prop :=
  ∀ i j j', j' ≤ I.bb ε → j + I.hh ε ≤ j' →
    (c i j' : ℝ) * ((I.d : ℝ) * I.bb ε / ε) ≤ c i j

/-- Lower end of `interval(c, i, j) = [∑_{j'=j+1}^b c(i, j'), ∑_{j'=j}^b c(i, j'))_ℝ`
(Definition 4.4; for `j = b` this is `[0, c(i, b))_ℝ`). -/
noncomputable def intervalLo (ε : ℝ) (c : Fin I.d → ℕ → ℝ) (i : Fin I.d) (j : ℕ) : ℝ :=
  ∑ j' ∈ Finset.Icc (j + 1) (I.bb ε), c i j'

/-- Upper end of `interval(c, i, j)`. -/
noncomputable def intervalHi (ε : ℝ) (c : Fin I.d → ℕ → ℝ) (i : Fin I.d) (j : ℕ) : ℝ :=
  ∑ j' ∈ Finset.Icc j (I.bb ε), c i j'

/-- `cost(c, i, j) = ∑_{x=1}^n (wᵢ)_x · aᵢ (1 + ε)^j · |[x − 1, x)_ℝ ∩ interval(c, i, j)|`; the
length of `[x − 1, x) ∩ [lo, hi)` is `max(0, min(x, hi) − max(x − 1, lo))`. -/
noncomputable def countCostAt (ε : ℝ) (a : Fin I.d → ℝ) (c : Fin I.d → ℕ → ℝ) (i : Fin I.d) (j : ℕ) : ℝ :=
  ∑ x : Fin I.n, I.W i x * a i * (1 + ε) ^ j *
    max 0 (min ((x : ℝ) + 1) (I.intervalHi ε c i j) - max (x : ℝ) (I.intervalLo ε c i j))

/-- `cost(c, i) = ∑_{j=0}^b cost(c, i, j)` (Definition 4.4). -/
noncomputable def countCost (ε : ℝ) (a : Fin I.d → ℝ) (c : Fin I.d → ℕ → ℝ) (i : Fin I.d) : ℝ :=
  ∑ j ∈ Finset.range (I.bb ε + 1), I.countCostAt ε a c i j

/-- `σ` is an `ε`-nice selection with respect to the count `c` (Definition 4.6): `c_σ ≤ (1 + ε) c`
on `[d] × [0, b]`, and no point `p` has a choice `ℓ` with
`minᵢ c(i, v(p, ℓ)ᵢ) ≥ min_{i'} c(i', v(p, σ(p))_{i'}) · (d · b / ε)`. -/
def IsNiceSelection (ε : ℝ) (v : Fin I.n → Fin I.ψ → Fin I.d → ℕ) (c : Fin I.d → ℕ → ℕ)
    (σ : Fin I.n → Fin I.ψ) : Prop :=
  haveI : Nonempty (Fin I.d) := ⟨⟨0, I.d_pos⟩⟩
  (∀ i j, j ≤ I.bb ε → (I.selCount v σ i j : ℝ) ≤ (1 + ε) * c i j) ∧
  (∀ p ℓ, ¬ ((Finset.univ.inf' Finset.univ_nonempty (fun i' => c i' (v p (σ p) i')) : ℝ)
      * ((I.d : ℝ) * I.bb ε / ε)
      ≤ (Finset.univ.inf' Finset.univ_nonempty (fun i => c i (v p ℓ i)) : ℝ)))

end SelInstance

end DistMapClust.Main


