-- Prove2me | Definitions.Def_LassoDantzig_Dantzig_Model
-- name    : LassoDantzig_Dantzig_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:12:11.143043+00:00
-- url     : https://prove2.me/theorems/dd9e5840-9186-4519-ac33-28c0b0b84325
-- title:
--   Dantzig selector, the set $\Lambda$, the noise event $\mathcal B$ and the restricted eigenvalue assumptions RE$(s,c_0)$, RE$(s,m,c_0)$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$ be a deterministic design matrix, $y\in\mathbb R^n$ a vector of observations and $r\in\mathbb R$ a tuning level. The paper's dictionary $f_1,\dots,f_M$ evaluated at the design points $Z_1,\dots,Z_n$ enters only through $X_{ij}=f_j(Z_i)$, so the column empirical norms are
--
--   $$
--   \|f_j\|_n=\Big(\frac1n\sum_{i=1}^n X_{ij}^2\Big)^{1/2}.
--   $$
--
--   For $\beta\in\mathbb R^M$ write $J(\beta)=\{j:\beta_j\neq0\}$ for its support and $\mathcal M(\beta)=|J(\beta)|$ for its sparsity. For $\delta\in\mathbb R^M$ and $J\subseteq\{1,\dots,M\}$, $|\delta_J|_1=\sum_{j\in J}|\delta_j|$ and $|\delta_J|_2=(\sum_{j\in J}\delta_j^2)^{1/2}$; for $v\in\mathbb R^n$, $|v|_2=(\sum_i v_i^2)^{1/2}$.
--
--   1. **Dantzig constraint and Dantzig selector (2.4).** With $D=\mathrm{diag}(\|f_1\|_n^2,\dots,\|f_M\|_n^2)$, $\beta$ satisfies the Dantzig constraint if $\big|\frac1n D^{-1/2}X^T(y-X\beta)\big|_\infty\le r$, i.e. $\big|\frac1n\sum_i X_{ij}(y_i-(X\beta)_i)\big|\le r\|f_j\|_n$ for every $j$. A **Dantzig selector** $\hat\beta_D$ satisfies the constraint and has the smallest $|\beta|_1=\sum_j|\beta_j|$ among all vectors that do.
--   2. **The linear-model Dantzig selector (7.3).** $\Lambda=\{\beta\in\mathbb R^M:\ |\frac1n X^T(y-X\beta)|_\infty\le r\}$, and $\hat\beta_D\in\arg\min_{\beta\in\Lambda}|\beta|_1$: $\hat\beta_D\in\Lambda$ and $|\hat\beta_D|_1\le|\beta|_1$ for every $\beta\in\Lambda$. When every diagonal entry of $X^TX/n$ is 1 (so $\|f_j\|_n=1$ and $D=I$) this is the same as item 1.
--   3. **The noise event $\mathcal B$.** For a noise vector $w\in\mathbb R^n$ let $V_j=\frac1n\sum_i X_{ij}w_i$; the event is $\mathcal B=\{|\frac1n D^{-1/2}X^Tw|_\infty\le r\}=\bigcap_{j=1}^M\{|V_j|\le r\|f_j\|_n\}$.
--   4. **Cone condition (4.1).** For $J_0\subseteq\{1,\dots,M\}$ and $c_0>0$: $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$.
--   5. **Top block.** $J_1$ is a set of "the $m$ largest in absolute value coordinates of $\delta$ outside of $J_0$" if $J_1\subseteq J_0^c$, $|J_1|=m$, and $|\delta_k|\le|\delta_j|$ for all $j\in J_1$, $k\in J_0^c\setminus J_1$.
--   6. **Restricted eigenvalue assumptions.** A number $\kappa$ is a *witness* of RE$(s,c_0)$ if for every $J_0$ with $|J_0|\le s$ and every $\delta\ne0$ satisfying (4.1),
--   $$
--   \kappa\sqrt n\,|\delta_{J_0}|_2\le|X\delta|_2 ,
--   $$
--   and a witness of RE$(s,m,c_0)$ if, in addition for every admissible $J_1$ and $J_{01}=J_0\cup J_1$, $\kappa\sqrt n\,|\delta_{J_{01}}|_2\le|X\delta|_2$. The paper's $\kappa(s,c_0)$ and $\kappa(s,m,c_0)$ are the largest witnesses, and Assumption RE$(s,c_0)$ (resp. RE$(s,m,c_0)$) is the existence of a positive witness.
--
--   These are the objects in which the paper's rates of convergence for the Dantzig selector are stated.
--
--   **Formalization Note** RE is stated through a witness $\kappa$ rather than the minimum $\kappa(s,c_0)$: the minimum is attained (the normalised cone is compact), so it is a witness and every witness is at most it; since all bounds of the paper decrease in $\kappa$, a theorem stated for every positive witness is equivalent to the paper's, and the junk value of a real infimum over an empty set (which arises for $J_0=\emptyset$) is avoided. Under ties all admissible $J_1$ are covered. Vectors are functions `Fin M → ℝ`; the noise event is a predicate on a realised noise vector.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 3 (empirical norm), p. 4 (J(β), M(β)), p. 5, Eq. (2.4) (Dantzig selector); p. 7, Assumptions RE(s, c0) and RE(s, m, c0); p. 9, Eq. (4.1); p. 16, Eq. (7.3); p. 23, proof of Lemma B.3 (event ℬ)

import Mathlib

namespace LassoDantzig.Dantzig

/-- The empirical norm `‖f_j‖_n = ((1/n) ∑ᵢ X i j ²)^{1/2}` of the `j`-th column of the design
matrix `X = (f_j(Z_i))` (Bickel–Ritov–Tsybakov, p. 3). -/
noncomputable def colNorm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (j : Fin M) : ℝ :=
  Real.sqrt ((1 / (n : ℝ)) * ∑ i, X i j ^ 2)

/-- The support `J(β) = {j : βⱼ ≠ 0}` (p. 4). -/
noncomputable def supp {M : ℕ} (β : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun j => β j ≠ 0)

/-- The sparsity `𝓜(β) = |J(β)|`, the number of non-zero coordinates of `β` (p. 4). -/
noncomputable def sparsity {M : ℕ} (β : Fin M → ℝ) : ℕ :=
  (supp β).card

/-- `|δ_J|_1 = ∑_{j ∈ J} |δⱼ|`, the ℓ1 norm of the restriction `δ_J` of `δ` to `J` (p. 4). -/
noncomputable def l1On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  ∑ j ∈ J, |δ j|

/-- `|δ_J|_2 = (∑_{j ∈ J} δⱼ²)^{1/2}`, the ℓ2 norm of the restriction `δ_J` (p. 4). -/
noncomputable def l2On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  Real.sqrt (∑ j ∈ J, δ j ^ 2)

/-- The Euclidean norm `|v|_2 = (∑ᵢ vᵢ²)^{1/2}` of a vector `v ∈ ℝⁿ`. -/
noncomputable def euclNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The general Dantzig constraint (p. 5), `|(1/n) D^{−1/2} Xᵀ(y − Xβ)|_∞ ≤ r` with
`D = diag(‖f₁‖_n², …, ‖f_M‖_n²)`, written coordinatewise:
`|(1/n) ∑ᵢ X i j (yᵢ − (Xβ)ᵢ)| ≤ r ‖fⱼ‖_n` for every `j`. -/
def DantzigConstraint {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (β : Fin M → ℝ) : Prop :=
  ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec β i)| ≤ r * colNorm X j

/-- `β̂` is a Dantzig selector in the general form (2.4), p. 5: it satisfies the general
Dantzig constraint and has the smallest (unweighted) ℓ1 norm `|β|_1 = ∑ⱼ |βⱼ|` among all
vectors that satisfy it. -/
def IsDantzigSelector {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) : Prop :=
  DantzigConstraint X y r βhat ∧
    ∀ β : Fin M → ℝ, DantzigConstraint X y r β → ∑ j, |βhat j| ≤ ∑ j, |β j|

/-- Membership in the set `Λ = {β ∈ ℝ^M : |(1/n) Xᵀ(y − Xβ)|_∞ ≤ r}` of the linear-regression
section (p. 16, under (7.3)), written coordinatewise:
`|(1/n) ∑ᵢ X i j (yᵢ − (Xβ)ᵢ)| ≤ r` for every `j`. -/
def InLambda {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (β : Fin M → ℝ) : Prop :=
  ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * (y i - X.mulVec β i)| ≤ r

/-- `β̂` is a Dantzig selector for the linear model (7.3), p. 16: `β̂ ∈ Λ` and
`|β̂|_1 ≤ |β|_1` for every `β ∈ Λ` (`β̂ ∈ argmin_{β ∈ Λ} |β|_1`). -/
def IsDantzig {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) : Prop :=
  InLambda X y r βhat ∧ ∀ β : Fin M → ℝ, InLambda X y r β → ∑ j, |βhat j| ≤ ∑ j, |β j|

/-- The noise event `ℬ = {|(1/n) D^{−1/2} Xᵀ w|_∞ ≤ r} = ⋂ⱼ {|Vⱼ| ≤ r ‖fⱼ‖_n}` (p. 23), as a
property of a realised noise vector `w ∈ ℝⁿ`, where `Vⱼ = (1/n) ∑ᵢ fⱼ(Zᵢ) wᵢ`. -/
def NoiseEvent {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (r : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ j : Fin M, |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r * colNorm X j

/-- The cone condition (4.1) (p. 9): `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1`. -/
def ConeCond {M : ℕ} (c0 : ℝ) (J0 : Finset (Fin M)) (δ : Fin M → ℝ) : Prop :=
  l1On δ J0ᶜ ≤ c0 * l1On δ J0

/-- `J1` is an admissible choice of "the subset of `{1, …, M}` corresponding to the `m` largest
in absolute value coordinates of `δ` outside of `J0`" (p. 7): `J1 ⊆ J0ᶜ`, `|J1| = m`, and every
coordinate of `δ` in `J0ᶜ \ J1` is, in absolute value, at most every coordinate in `J1`. Under
ties several sets qualify. -/
def IsTopBlock {M : ℕ} (δ : Fin M → ℝ) (J0 J1 : Finset (Fin M)) (m : ℕ) : Prop :=
  J1 ⊆ J0ᶜ ∧ J1.card = m ∧ ∀ j ∈ J1, ∀ k ∈ J0ᶜ \ J1, |δ k| ≤ |δ j|

/-- Assumption RE(s, c₀) (p. 7) with witness `κ`: for every `J₀ ⊆ {1, …, M}` with `|J₀| ≤ s`
and every `δ ≠ 0` with `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1`, `κ √n |δ_{J₀}|_2 ≤ |Xδ|_2`.
The paper's `κ(s, c₀)` is the largest such `κ`; Assumption RE(s, c₀) is "`RE X s c0 κ` for
some `κ > 0`". -/
def RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    κ * Real.sqrt n * l2On δ J0 ≤ euclNorm (X.mulVec δ)

/-- Assumption RE(s, m, c₀) (p. 7) with witness `κ`: for every `J₀` with `|J₀| ≤ s`, every
`δ ≠ 0` with `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1` and every admissible set `J₁` of the `m` largest
`|δⱼ|` outside `J₀`, `κ √n |δ_{J₀₁}|_2 ≤ |Xδ|_2` with `J₀₁ = J₀ ∪ J₁`. The paper's
`κ(s, m, c₀)` is the largest such `κ`. -/
def REm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s m : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    ∀ J1 : Finset (Fin M), IsTopBlock δ J0 J1 m →
      κ * Real.sqrt n * l2On δ (J0 ∪ J1) ≤ euclNorm (X.mulVec δ)

end LassoDantzig.Dantzig


