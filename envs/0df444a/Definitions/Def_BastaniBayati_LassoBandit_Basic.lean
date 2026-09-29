-- Prove2me | Definitions.Def_BastaniBayati_LassoBandit_Basic
-- name    : BastaniBayati_LassoBandit_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T08:56:10.600049+00:00
-- url     : https://prove2.me/theorems/f8619287-8616-4aff-ad93-2eeada51d140
-- title:
--   LASSO estimator, $\ell_1$ norm, support and the compatibility set $\mathcal C(I,\phi)$
-- statement:
--   Basic objects of Bastani and Bayati's LASSO Bandit paper, for vectors in $\mathbb R^d$ (coordinates indexed by $[d]$).
--
--   1. The $\ell_1$ norm $\|v\|_1=\sum_{j}|v_j|$, the support $\mathrm{supp}(v)=\{j : v_j\neq 0\}$, and, for $I\subseteq[d]$, the vector $v_I$ obtained from $v$ by setting the entries outside $I$ to zero.
--   2. **Compatibility set** (Definition 2). For $I\subseteq[d]$ and $\phi>0$,
--   $$\mathcal C(I,\phi)=\Big\{M\in\mathbb R^{d\times d}_{\succeq 0}\;\Big|\;\forall v\in\mathbb R^d \text{ with } \|v_{I^c}\|_1\le 3\|v_I\|_1:\ \|v_I\|_1^2\le |I|\,\frac{v^\top M v}{\phi^2}\Big\}.$$
--   3. **Sample covariance.** For a design $\mathbf Z$ with $n$ rows $Z_t\in\mathbb R^d$, $\hat\Sigma(\mathbf Z)=\mathbf Z^\top\mathbf Z/n$.
--   4. **LASSO** (Definition 3). For rows $X_t$, responses $Y_t$ ($n$ of them) and $\lambda\ge 0$, the LASSO objective is
--   $$\frac{\|Y-\mathbf X\beta'\|_2^2}{n}+\lambda\|\beta'\|_1,$$
--   and a LASSO estimator $\hat\beta_{\mathbf X,Y}(\lambda)$ is any global minimizer of it.
--
--   These are the objects in which the paper's LASSO tail inequalities are stated; the compatibility condition is the identifiability assumption on which they rest.
--
--   **Formalization Note** The objective uses the paper's $1/n$ scaling (not $1/(2n)$). The minimizer need not be unique; `IsLassoMinimizer` is the predicate "is a global minimizer", and every theorem of the mission holds for an arbitrary minimizer. Rows are indexed by an arbitrary finite type.
-- source:
--   Bastani & Bayati, Online Decision Making with High-Dimensional Covariates, Operations Research 68(1):276–294 (2020), doi:10.1287/opre.2019.1902, p. 280 (§2.1 notation), p. 282 (Definition 2), p. 283 (§3.1, Definition 3, Eq. (1))

import Mathlib

open Finset

namespace BastaniBayati.LassoBandit

/-- The `ℓ₁` norm `‖v‖₁ = ∑ⱼ |vⱼ|` of a vector `v ∈ ℝᵈ`. -/
def l1Norm {d : ℕ} (v : Fin d → ℝ) : ℝ := ∑ j, |v j|

/-- The support `supp(v) = {j ∈ [d] | vⱼ ≠ 0}` of a vector `v ∈ ℝᵈ` (Bastani–Bayati §2.1). -/
noncomputable def supp {d : ℕ} (v : Fin d → ℝ) : Finset (Fin d) :=
  by classical exact Finset.univ.filter (fun j => v j ≠ 0)

/-- `v_I`: the vector obtained from `v` by setting the entries outside `I` to zero (§2.1). -/
noncomputable def restrictTo {d : ℕ} (I : Finset (Fin d)) (v : Fin d → ℝ) : Fin d → ℝ :=
  by classical exact fun j => if j ∈ I then v j else 0

/-- **Definition 2** (Compatibility Condition), Bastani–Bayati p. 282. For `I ⊆ [d]` and `φ > 0`,
`𝒞(I, φ)` is the set of `d × d` positive semidefinite matrices `M` such that every `v ∈ ℝᵈ` with
`‖v_{Iᶜ}‖₁ ≤ 3‖v_I‖₁` satisfies `‖v_I‖₁² ≤ |I| (vᵀ M v) / φ²`. -/
noncomputable def compatSet {d : ℕ} (I : Finset (Fin d)) (φ : ℝ) :
    Set (Matrix (Fin d) (Fin d) ℝ) :=
  {M | M.PosSemidef ∧ ∀ v : Fin d → ℝ,
      l1Norm (restrictTo Iᶜ v) ≤ 3 * l1Norm (restrictTo I v) →
        l1Norm (restrictTo I v) ^ 2 ≤ (I.card : ℝ) * (v ⬝ᵥ (M.mulVec v)) / φ ^ 2}

/-- The sample covariance matrix `Σ̂(Z) = Zᵀ Z / n` of a design whose rows are `Z t ∈ ℝᵈ`, indexed
by a finite set of size `n` (§3.1, p. 283). -/
noncomputable def sampleCov {ι : Type*} [Fintype ι] {d : ℕ} (Z : ι → Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun a b => (∑ t, Z t a * Z t b) / (Fintype.card ι : ℝ)

/-- The LASSO objective of **Definition 3**, Eq. (1), p. 283:
`‖Y − Xβ'‖₂² / n + λ ‖β'‖₁`, for a design with rows `X t` and responses `Y t`, `t` ranging over a
finite index set of size `n`. Note the `1/n` (not `1/(2n)`) scaling. -/
noncomputable def lassoObjective {ι : Type*} [Fintype ι] {d : ℕ} (X : ι → Fin d → ℝ) (Y : ι → ℝ)
    (lam : ℝ) (β' : Fin d → ℝ) : ℝ :=
  (∑ t, (Y t - X t ⬝ᵥ β') ^ 2) / (Fintype.card ι : ℝ) + lam * l1Norm β'

/-- `β̂` is a LASSO estimator (Definition 3, Eq. (1)): a global minimizer of the LASSO objective.
The minimizer need not be unique; every statement of this mission quantifies over an arbitrary
minimizer. -/
def IsLassoMinimizer {ι : Type*} [Fintype ι] {d : ℕ} (X : ι → Fin d → ℝ) (Y : ι → ℝ) (lam : ℝ)
    (βhat : Fin d → ℝ) : Prop :=
  ∀ β' : Fin d → ℝ, lassoObjective X Y lam βhat ≤ lassoObjective X Y lam β'

end BastaniBayati.LassoBandit


