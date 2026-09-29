-- Prove2me | Definitions.Def_LassoDantzig_Equivalence_Model
-- name    : LassoDantzig_Equivalence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T10:46:30.511827+00:00
-- url     : https://prove2.me/theorems/3c21ff46-fb20-43a2-a9ee-9574f870822b
-- title:
--   Regression with a dictionary: Lasso (2.1), Dantzig selector (2.4), RE$(s,c_0)$ and the noise events $\mathcal A$, $\mathcal B$
-- statement:
--   Fix integers $n\ge1$ and $M$. The data of the regression problem are a **design matrix** $X=(X_{ij})\in\mathbb R^{n\times M}$, whose $j$-th column $(f_j(Z_1),\dots,f_j(Z_n))$ holds the values of the $j$-th dictionary function $f_j$ at the design points $Z_1,\dots,Z_n$, and a **target vector** $f=(f(Z_1),\dots,f(Z_n))\in\mathbb R^n$ holding the values of the unknown regression function. For $\beta\in\mathbb R^M$ the combination $f_\beta=\sum_j\beta_jf_j$ has the vector of values $X\beta$.
--
--   This file defines the following objects.
--
--   1. The **empirical norm** $\|g\|_n=\big(\tfrac1n\sum_{i=1}^n g_i^2\big)^{1/2}$ of $g\in\mathbb R^n$; the column norms $\|f_j\|_n$ (the empirical norms of the columns of $X$); and $f_{\max}=\max_{1\le j\le M}\|f_j\|_n$.
--   2. The squared **prediction loss** $\|f_\beta-f\|_n^2=\tfrac1n\sum_{i=1}^n\big((X\beta)_i-f_i\big)^2$.
--   3. The **support** $J(\beta)=\{j:\beta_j\ne0\}$ and the **sparsity** $\mathcal M(\beta)=|J(\beta)|$; for $J\subseteq\{1,\dots,M\}$, $|\delta_J|_1=\sum_{j\in J}|\delta_j|$ and $|\delta_J|_2=\big(\sum_{j\in J}\delta_j^2\big)^{1/2}$; and the Euclidean norm $|v|_2$ on $\mathbb R^n$.
--   4. The **Lasso** (2.1): given observations $y\in\mathbb R^n$ and $r\in\mathbb R$, a vector $\hat\beta_L$ is a Lasso solution if it minimises over all $\beta\in\mathbb R^M$
--   $$
--   \frac1n\sum_{i=1}^n\big(y_i-(X\beta)_i\big)^2+2r\sum_{j=1}^M\|f_j\|_n\,|\beta_j| .
--   $$
--   5. The **Dantzig constraint**: $\beta$ satisfies it if
--   $$
--   \Big|\frac1n\sum_{i=1}^n X_{ij}\big(y_i-(X\beta)_i\big)\Big|\le r\,\|f_j\|_n\qquad\text{for all }j,
--   $$
--   which is the coordinatewise form of $\big|\tfrac1n D^{-1/2}X^\top(y-X\beta)\big|_\infty\le r$ with $D=\mathrm{diag}(\|f_1\|_n^2,\dots,\|f_M\|_n^2)$. A **Dantzig selector** (2.4) $\hat\beta_D$ satisfies the constraint and has the smallest unweighted $\ell_1$ norm $|\beta|_1=\sum_j|\beta_j|$ among all $\beta$ that satisfy it.
--   6. The **cone condition** $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$ and **Assumption RE$(s,c_0)$ with witness $\kappa$**: for every $J_0\subseteq\{1,\dots,M\}$ with $|J_0|\le s$ and every $\delta\ne0$ satisfying the cone condition,
--   $$
--   \kappa\sqrt n\,|\delta_{J_0}|_2\le|X\delta|_2 .
--   $$
--   7. For a realised noise vector $w\in\mathbb R^n$ and $V_j=\tfrac1n\sum_iX_{ij}w_i$, the **noise events** $\mathcal A=\bigcap_j\{2|V_j|\le r\|f_j\|_n\}$ and $\mathcal B=\bigcap_j\{|V_j|\le r\|f_j\|_n\}$ (pp. 21, 23). Clearly $\mathcal A\subseteq\mathcal B$.
--
--   These are the objects in terms of which the paper compares the Lasso and the Dantzig selector.
--
--   **Formalization Note** The dictionary functions and design points enter every statement only through the matrix $X=(f_j(Z_i))$ and the vector $f=(f(Z_i))$, so these are taken as the data. The paper's $\kappa(s,c_0)$ is a minimum over a compact normalised cone and is therefore attained; RE$(s,c_0)$ ("$\kappa(s,c_0)>0$") is equivalent to the existence of a witness $\kappa>0$, every witness is at most $\kappa(s,c_0)$, and every bound in which $\kappa$ appears decreases in $\kappa$. Theorems are therefore stated for every witness; this avoids the junk value of a real infimum over an empty set (for $J_0=\emptyset$). $f_{\max}$ is the supremum of the finitely many column norms, which is their maximum when $M\ge1$ (every theorem assumes $M\ge2$). Lasso and Dantzig solutions are predicates, not chosen minimisers: neither need be unique, and the theorems hold for every solution. The noise events are predicates on a noise vector $w$; in the probabilistic statements $w=(W_1(\omega),\dots,W_n(\omega))$.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, pp. 3–5, Eqs. (2.1), (2.4) and the definitions of ‖·‖_n, f_max, 𝓜(β), δ_J; p. 7, Assumption RE(s, c0); p. 21, event 𝒜 (proof of Lemma B.1); p. 23, event ℬ (proof of Lemma B.3)

import Mathlib

namespace LassoDantzig.Equivalence

/-- The empirical norm `‖g‖_n = ((1/n) ∑ᵢ g(Zᵢ)²)^{1/2}` of a vector of values
`g = (g(Z₁), …, g(Zₙ)) ∈ ℝⁿ` (Bickel–Ritov–Tsybakov, p. 3). -/
noncomputable def empNorm {n : ℕ} (g : Fin n → ℝ) : ℝ :=
  Real.sqrt ((1 / (n : ℝ)) * ∑ i, g i ^ 2)

/-- The empirical norm `‖f_j‖_n` of the `j`-th dictionary function, i.e. of the `j`-th column
of the design matrix `X = (f_j(Z_i))` (p. 3). -/
noncomputable def colNorm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) : ℝ :=
  empNorm (fun i => X i j)

/-- `f_max = max_{1 ≤ j ≤ M} ‖f_j‖_n` (p. 4). The supremum of finitely many reals; it is the
maximum whenever `M ≥ 1`. -/
noncomputable def fmax {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) : ℝ :=
  ⨆ j : Fin M, colNorm X j

/-- The squared empirical prediction loss `‖f_β − f‖_n² = (1/n) ∑ᵢ ((Xβ)ᵢ − f(Zᵢ))²` of the
linear combination `f_β = ∑ⱼ βⱼ fⱼ` (whose vector of values is `Xβ`), p. 4. -/
noncomputable def predLoss {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (f : Fin n → ℝ)
    (β : Fin M → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (X.mulVec β i - f i) ^ 2

/-- The support `J(β) = {j : βⱼ ≠ 0}` (p. 4). -/
noncomputable def supp {M : ℕ} (β : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun j => β j ≠ 0)

/-- The sparsity `𝓜(β) = |J(β)|`, the number of non-zero coordinates of `β` (p. 4). -/
noncomputable def sparsity {M : ℕ} (β : Fin M → ℝ) : ℕ :=
  (supp β).card

/-- `|δ_J|_1 = ∑_{j ∈ J} |δⱼ|`, the ℓ1 norm of the restriction `δ_J` (p. 4). -/
noncomputable def l1On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  ∑ j ∈ J, |δ j|

/-- `|δ_J|_2 = (∑_{j ∈ J} δⱼ²)^{1/2}`, the ℓ2 norm of the restriction `δ_J` (p. 4). -/
noncomputable def l2On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  Real.sqrt (∑ j ∈ J, δ j ^ 2)

/-- The Euclidean norm `|v|_2` of a vector `v ∈ ℝⁿ`. -/
noncomputable def euclNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The Lasso criterion (2.1), p. 4:
`Ŝ(β) + 2r ∑ⱼ ‖fⱼ‖_n |βⱼ|` with `Ŝ(β) = (1/n) ∑ᵢ (Yᵢ − f_β(Zᵢ))²`. -/
noncomputable def lassoObj {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (β : Fin M → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (y i - X.mulVec β i) ^ 2 + 2 * r * ∑ j, colNorm X j * |β j|

/-- `β̂` is a Lasso solution (2.1): it minimises the Lasso criterion over all of `ℝ^M`. -/
def IsLasso {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) : Prop :=
  ∀ β : Fin M → ℝ, lassoObj X y r βhat ≤ lassoObj X y r β

/-- The Dantzig constraint (p. 5), `|(1/n) D^{−1/2} Xᵀ(y − Xβ)|_∞ ≤ r` with
`D = diag(‖f₁‖_n², …, ‖f_M‖_n²)`, written coordinatewise:
`|(1/n) ∑ᵢ X i j (yᵢ − (Xβ)ᵢ)| ≤ r ‖fⱼ‖_n` for every `j`. -/
def DantzigFeasible {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (β : Fin M → ℝ) : Prop :=
  ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec β i)| ≤ r * colNorm X j

/-- `β̂` is a Dantzig selector (2.4), p. 5: it satisfies the Dantzig constraint and has the
smallest (unweighted) ℓ1 norm `|β|_1 = ∑ⱼ |βⱼ|` among all vectors satisfying it. -/
def IsDantzig {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) : Prop :=
  DantzigFeasible X y r βhat ∧
    ∀ β : Fin M → ℝ, DantzigFeasible X y r β → ∑ j, |βhat j| ≤ ∑ j, |β j|

/-- The cone condition `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1` of Assumption RE(s, c₀) (p. 7). -/
def ConeCond {M : ℕ} (c0 : ℝ) (J0 : Finset (Fin M)) (δ : Fin M → ℝ) : Prop :=
  l1On δ J0ᶜ ≤ c0 * l1On δ J0

/-- Assumption RE(s, c₀) (p. 7) with witness `κ`: for every `J₀ ⊆ {1, …, M}` with `|J₀| ≤ s`
and every `δ ≠ 0` with `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1`, `κ √n |δ_{J₀}|_2 ≤ |Xδ|_2`.
The paper's `κ(s, c₀)` is the largest such `κ`; Assumption RE(s, c₀) is "`RE X s c0 κ` for
some `κ > 0`". -/
def RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    κ * Real.sqrt n * l2On δ J0 ≤ euclNorm (X.mulVec δ)

/-- The noise event `𝒜 = ⋂ⱼ {2|Vⱼ| ≤ r ‖fⱼ‖_n}` (p. 21), as a property of a realised noise
vector `w ∈ ℝⁿ`, where `Vⱼ = (1/n) ∑ᵢ fⱼ(Zᵢ) wᵢ`. Equivalently (B.5):
`|(1/n) D^{−1/2} Xᵀ w|_∞ ≤ r/2`. -/
def NoiseEventHalf {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (r : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ j : Fin M, 2 * |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r * colNorm X j

/-- The noise event `ℬ = ⋂ⱼ {|Vⱼ| ≤ r ‖fⱼ‖_n} = {|(1/n) D^{−1/2} Xᵀ w|_∞ ≤ r}` (p. 23), as a
property of a realised noise vector `w ∈ ℝⁿ`. -/
def NoiseEvent {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (r : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r * colNorm X j

end LassoDantzig.Equivalence


