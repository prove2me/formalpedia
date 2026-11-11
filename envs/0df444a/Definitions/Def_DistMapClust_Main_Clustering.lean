-- Prove2me | Definitions.Def_DistMapClust_Main_Clustering
-- name    : DistMapClust_Main_Clustering
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:04:47.859958+00:00
-- url     : https://prove2.me/theorems/1b3d7a8e-1a28-45ac-be3c-be9f1bb9f2f2
-- title:
--   k-Clustering with Linear Distance Mappings, Ball Intersection oracles, χ-shifted algorithmic scatter dimension, ε-relevant distances
-- statement:
--   An instance of **k-Clustering with Linear Distance Mappings** (Definition 1.1) has positive integers $k,d,\psi$, a finite nonempty point set $P$ ($n=|P|$), a nonempty, possibly infinite facility set $F$, a metric $\delta$ on $P\cup F$, a column-symmetric monotone norm $f$ on $d\times n$ matrices, and linear **distance mappings** $h_\ell:\mathbb R^k_{\ge0}\to\mathbb R^d_{\ge0}$, $\ell\in[\psi]$, given by nonnegative coefficients, $(h_\ell z)_j=\sum_i c_{\ell,j,i}z_i$. A solution is $X=(x_1,\dots,x_k)\in F^k$ and a selection $\sigma:P\to[\psi]$; with $\delta_X(p)=(\delta(x_i,p))_{i\in[k]}$, the **cost matrix** $U(X,\sigma)$ has column $p$ equal to $h_{\sigma(p)}(\delta_X(p))$, and the objective is $f(U(X,\sigma))$. $\mathrm{OPT}_I$ is its infimum.
--
--   A **request** $(p,r)$ is satisfied by $x$ if $\delta(x,p)\le r$; $F(Q)$ is the set of centers satisfying a finite request set $Q$. A **Ball Intersection oracle** $C$ (Definition 2.2) maps $(Q,\mu)$, $\mu>0$, to a center of $F((1+\mu)Q)$ or to failure, and does not fail when $F(Q)\neq\emptyset$. A **$(C,\chi,\varepsilon)$-scattering** (Definition 2.3) is a nonempty sequence $(x^a,p^a,d'^a)$ with $p^a\in P\cup F$, $x^a\in F$, $d'^a>0$, such that
--   $$x^a=C\big(\{(p^1,d'^1),\dots,(p^{a-1},d'^{a-1})\},\varepsilon/2\big)\ (a\ge2),\qquad \delta(x^a,p^a)>(1+\chi+\varepsilon)\,d'^a .$$
--   The space has **$\chi$-shifted algorithmic $(\varepsilon,C)$-scatter dimension $\lambda(\cdot)$** (Definition 2.4) if for every $\varepsilon\in(0,1)$ every scattering has at most $\lambda(\varepsilon)$ triples with any one radius value.
--
--   For an optimal $(X^*,\sigma^*)$, a finite $D\subseteq\bar{\mathbb R}=\mathbb R_{\ge0}\cup\{\infty\}$ with $\infty\in D$ is a set of **$\varepsilon$-relevant distances** (Definition 3.1) if there are $\Delta'_p\in D^k$ with $\Delta'_p\ge\delta_{X^*}(p)$ and $f\big((h_{\sigma^*(p)}(\Delta'_p))_{p}\big)\le(1+4\varepsilon)\mathrm{OPT}_I$, and no $d'_1<d'_2\le(1+\varepsilon)d'_1$ in $D$. A **row-wise ordered instance** additionally carries $(W,f')$ with $f=\mathrm{rowOrdNorm}(W,f')$.
--
--   **Formalization Note.** Points are elements of a type `α`; `P : Fin n → α` injective; the instance carries its oracle `C : Finset (α × ℝ) → ℝ → Option α`. `OPT` is `⨅` over `X ∈ F^k` and `σ` (nonempty, bounded below by 0). $\bar{\mathbb R}$ is `ℝ≥0∞`, with `0 · ∞ = 0` (p. 80); the objective of a matrix with an `∞` entry is `∞`, so `IsRelevant` asks all entries to be finite. Scattering positions are 0-based; radii $d'^a\in\mathbb R_+$ are read as positive.
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 7 (Definition 1.1), p. 8 (row-wise ordered norms), pp. 19–20 (Definitions 2.1–2.4), p. 22 (Definition 3.1), pp. 79–80 (§C.1)

import Mathlib
import Definitions.Def_DistMapClust_Main_Norms

/-!
# k-Clustering with Linear Distance Mappings, Ball Intersection oracles, scatter dimension and
# ε-relevant distances

Herold, Spoerhase, Kipouridis, Marx, *A Unified Framework for Parameterized Approximation of
Clustering Objectives via Distance Mappings*, STOC 2027 submission (manuscript sha256 1d00c842…):
Definition 1.1 (p. 7), row-wise ordered norms (p. 8), Definitions 2.1–2.4 (pp. 19–20),
Definition 3.1 (p. 22), proof of Lemma 3.2 (p. 79: the coefficients `c_{ℓ,j,i}`, the convention
`0 · ∞ = 0`).

Encoding.
* Points live in an arbitrary type `α`. The point set `P` is an injective family `Fin n → α`
  (column `p` of the cost matrix is point `P p`); the facility set `F ⊆ α` is any nonempty set,
  possibly infinite (p. 68: "The facility set F may be infinite"). `δ` is a metric on `P ∪ F`.
* A linear distance mapping `h_ℓ : ℝ^k_{≥0} → ℝ^d_{≥0}` is given by its nonnegative coefficients:
  `(h_ℓ z)_j = ∑ᵢ c_{ℓ,j,i} zᵢ` (p. 79). Every linear map sending `ℝ^k_{≥0}` into `ℝ^d_{≥0}` has this
  form, so this is an encoding. Indices `[k]`, `[d]`, `[ψ]`, `[n]` are `Fin` (0-based).
* The instance carries the Ball Intersection oracle `C` of its metric space, as a function of a finite
  request set and an error `μ`, returning a center or failure (`none`); `C_ball` is Definition 2.2's
  clauses 1–2. Clause 3 (polynomial running time) is not a property of the function: the machine
  charges one step per call.
* `OPT` is the infimum of the objective over `X ∈ F^k` and `σ : P → [ψ]`; with `F` infinite a minimum
  need not exist. The set is nonempty (`F ≠ ∅`) and bounded below by `0`.
* Requests `(p, ∞)` are satisfied by every center and are never passed to the oracle (p. 23), so
  request radii are real.
* `R̄ = ℝ_{≥0} ∪ {∞}` is `ℝ≥0∞`. A mapped vector `h_ℓ(Δ')` with `Δ' ∈ R̄^k` is computed in `ℝ≥0∞`,
  where `0 · ∞ = 0` (the paper's convention, p. 80); the objective of a matrix with an `∞` entry is
  read as `∞`, so `relevant` asks every entry to be finite.
-/

open scoped ENNReal

namespace DistMapClust.Main

/-- `δ` is a metric on the set `S`. -/
def IsMetricOn {α : Type} (S : Set α) (δ : α → α → ℝ) : Prop :=
  (∀ x ∈ S, ∀ y ∈ S, 0 ≤ δ x y) ∧
  (∀ x ∈ S, ∀ y ∈ S, δ x y = 0 ↔ x = y) ∧
  (∀ x ∈ S, ∀ y ∈ S, δ x y = δ y x) ∧
  (∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, δ x z ≤ δ x y + δ y z)

/-- `C` is an Approximate Ball Intersection Algorithm for the metric space `(Pts, F, δ)`
(Definition 2.2, clauses 1 and 2): for every finite request set `Q ⊆ (Pts ∪ F) × ℝ_{≥0}` and every
`μ > 0`, a returned center lies in `F((1 + μ)Q)`, and `C` does not fail when `F(Q) ≠ ∅`. -/
def IsBallIntersection {α : Type} (Pts F : Set α) (δ : α → α → ℝ)
    (C : Finset (α × ℝ) → ℝ → Option α) : Prop :=
  ∀ Q : Finset (α × ℝ), (∀ q ∈ Q, q.1 ∈ Pts ∪ F ∧ 0 ≤ q.2) → ∀ μ : ℝ, 0 < μ →
    (∀ x : α, C Q μ = some x → x ∈ F ∧ ∀ q ∈ Q, δ x q.1 ≤ (1 + μ) * q.2) ∧
    ((∃ x ∈ F, ∀ q ∈ Q, δ x q.1 ≤ q.2) → C Q μ ≠ none)

open Classical in
/-- An algorithmic `(C, χ, ε)`-scattering (Definition 2.3): a nonempty list of triples
`(xᵃ, pᵃ, d'ᵃ)` with `pᵃ ∈ P ∪ F`, `xᵃ ∈ F`, `d'ᵃ > 0`, such that for every position `a ≥ 1`
(0-based; the paper's `2 ≤ a ≤ ℓ`) `xᵃ = C({(p¹, d'¹), …, (p^{a-1}, d'^{a-1})}, ε/2)`, and
`δ(xᵃ, pᵃ) > (1 + χ + ε) d'ᵃ` for every `a`. The first center is arbitrary in `F`. -/
def IsScattering {α : Type} (Pts F : Set α) (δ : α → α → ℝ)
    (C : Finset (α × ℝ) → ℝ → Option α) (χ ε : ℝ) (L : List (α × α × ℝ)) : Prop :=
  L ≠ [] ∧
  (∀ t ∈ L, t.2.1 ∈ Pts ∪ F ∧ t.1 ∈ F ∧ 0 < t.2.2) ∧
  (∀ (a : ℕ) (ha : a < L.length), 1 ≤ a →
    C ((L.take a).map (fun t => (t.2.1, t.2.2))).toFinset (ε / 2) = some (L[a]'ha).1) ∧
  (∀ t ∈ L, (1 + χ + ε) * t.2.2 < δ t.1 t.2.1)

open Classical in
/-- `(Pts, F, δ)` with the Ball Intersection oracle `C` has `χ`-shifted algorithmic `(ε, C)`-scatter
dimension `λ(·)` (Definition 2.4): for every `ε ∈ (0, 1)`, every `(C, χ, ε)`-scattering contains at
most `λ(ε)` triples with the same radius value. -/
def HasScatterDim {α : Type} (Pts F : Set α) (δ : α → α → ℝ)
    (C : Finset (α × ℝ) → ℝ → Option α) (χ : ℝ) (lam : ℝ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ L : List (α × α × ℝ), IsScattering Pts F δ C χ ε L →
    ∀ r : ℝ, L.countP (fun t => decide (t.2.2 = r)) ≤ lam ε

/-- An instance of k-Clustering with Linear Distance Mappings (Definition 1.1), with the Ball
Intersection oracle of its metric space. -/
structure Instance (α : Type) where
  /-- number of centers -/
  k : ℕ
  /-- number of rows of the cost matrix -/
  d : ℕ
  /-- number of distance mappings -/
  ψ : ℕ
  /-- number of points -/
  n : ℕ
  k_pos : 0 < k
  d_pos : 0 < d
  ψ_pos : 0 < ψ
  n_pos : 0 < n
  /-- the points -/
  P : Fin n → α
  /-- the facilities -/
  F : Set α
  /-- the distance function -/
  δ : α → α → ℝ
  /-- the objective, a norm on nonnegative `d × n` matrices -/
  f : Mat d n → ℝ
  /-- `coef ℓ j i = c_{ℓ,j,i}`, the coefficients of the linear mapping `h_ℓ` -/
  coef : Fin ψ → Fin d → Fin k → ℝ
  /-- the Ball Intersection oracle of the metric space `(P, F, δ)` -/
  C : Finset (α × ℝ) → ℝ → Option α
  P_injective : Function.Injective P
  F_nonempty : F.Nonempty
  metric : IsMetricOn (Set.range P ∪ F) δ
  f_norm : IsMonotoneMatrixNorm f
  f_colSymm : IsColumnSymmetric f
  coef_nonneg : ∀ ℓ j i, 0 ≤ coef ℓ j i
  C_ball : IsBallIntersection (Set.range P) F δ C

namespace Instance

variable {α : Type} (I : Instance α)

/-- The linear distance mapping `h_ℓ`: `(h_ℓ z)_j = ∑ᵢ c_{ℓ,j,i} zᵢ`. -/
def mapping (ℓ : Fin I.ψ) (z : Fin I.k → ℝ) : Fin I.d → ℝ :=
  fun j => ∑ i, I.coef ℓ j i * z i

/-- `δ_X(p) = (δ(xᵢ, p))_{i ∈ [k]}`. -/
def distVec (X : Fin I.k → α) (p : Fin I.n) : Fin I.k → ℝ :=
  fun i => I.δ (X i) (I.P p)

/-- The cost matrix `U(X, σ)`: column `p` is `u(p, σ(p)) = h_{σ(p)}(δ_X(p))`. -/
def costMatrix (X : Fin I.k → α) (σ : Fin I.n → Fin I.ψ) : Mat I.d I.n :=
  fun j p => I.mapping (σ p) (I.distVec X p) j

/-- The objective `f(U(X, σ))`. -/
def cost (X : Fin I.k → α) (σ : Fin I.n → Fin I.ψ) : ℝ :=
  I.f (I.costMatrix X σ)

/-- `OPT_I`: the infimum of `f(U(X, σ))` over `X ∈ F^k` and `σ : P → [ψ]`. -/
noncomputable def OPT : ℝ :=
  ⨅ Xσ : {X : Fin I.k → α // ∀ i, X i ∈ I.F} × (Fin I.n → Fin I.ψ), I.cost Xσ.1.1 Xσ.2

/-- `(X, σ)` is an optimal solution: `X ∈ F^k` and `f(U(X, σ)) = OPT_I`. -/
def IsOptimal (X : Fin I.k → α) (σ : Fin I.n → Fin I.ψ) : Prop :=
  (∀ i, X i ∈ I.F) ∧ I.cost X σ = I.OPT

/-- `D ⊆ R̄` is a set of `ε`-relevant distances for `I` with respect to the optimal solution
`(X*, σ*)` (Definition 3.1): `∞ ∈ D`; there are `Δ'_p ∈ D^k` with `Δ'_p ≥ Δ_p = δ_{X*}(p)`
componentwise and `f((h_{σ*(p)}(Δ'_p)ᵀ)_{p ∈ P}) ≤ (1 + 4ε) OPT_I` (all entries finite, `0 · ∞ = 0`);
and no `d'₁ < d'₂ ≤ (1 + ε) d'₁` in `D`. -/
def IsRelevant (ε : ℝ) (Xs : Fin I.k → α) (σs : Fin I.n → Fin I.ψ) (D : Finset ℝ≥0∞) : Prop :=
  ⊤ ∈ D ∧
  (∃ Δ' : Fin I.n → Fin I.k → ℝ≥0∞,
    (∀ p i, Δ' p i ∈ D) ∧
    (∀ p i, ENNReal.ofReal (I.δ (Xs i) (I.P p)) ≤ Δ' p i) ∧
    (∀ j p, (∑ i, ENNReal.ofReal (I.coef (σs p) j i) * Δ' p i) ≠ ⊤) ∧
    I.f (fun j p => (∑ i, ENNReal.ofReal (I.coef (σs p) j i) * Δ' p i).toReal)
      ≤ (1 + 4 * ε) * I.OPT) ∧
  (∀ d₁ ∈ D, ∀ d₂ ∈ D, ¬ (d₁ < d₂ ∧ d₂ ≤ ENNReal.ofReal (1 + ε) * d₁))

end Instance

/-- An instance whose objective is a row-wise ordered norm (p. 8): `f = rowOrdNorm W f'` for weight
vectors `W` and a monotone norm `f'` on `ℝ^d_{≥0}`. The instance carries `(W, f')` (§4, p. 46). -/
structure RowInstance (α : Type) extends Instance α where
  /-- the weight vectors of the ordered norms of the rows -/
  W : Fin d → Fin n → ℝ
  /-- the outer monotone norm -/
  f' : (Fin d → ℝ) → ℝ
  W_weight : ∀ i, IsWeightVector (W i)
  f'_norm : IsMonotoneNorm f'
  f_eq : f = rowOrdNorm W f'

end DistMapClust.Main


