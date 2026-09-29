-- Prove2me | Definitions.Def_LassoDantzig_Lasso_Model
-- name    : LassoDantzig_Lasso_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:17:36.205165+00:00
-- url     : https://prove2.me/theorems/695c3569-0cde-477e-861e-3aec13ef9363
-- title:
--   Linear regression with a normalised design: the Lasso (7.2), $\phi_{\max}$, RE$(s,c_0)$, RE$(s,m,c_0)$ and the noise event $\mathcal A$
-- statement:
--   Fix integers $n\ge1$ and $M$. The data are a deterministic **design matrix** $X=(X_{ij})\in\mathbb R^{n\times M}$ with columns $x_{(1)},\dots,x_{(M)}$ and, in the linear regression model (7.1), a coefficient vector $\beta^*\in\mathbb R^M$ with observations $y=X\beta^*+w$. This file defines the following objects.
--
--   1. Norms of vectors: $|\delta|_1=\sum_{j}|\delta_j|$; for $J\subseteq\{1,\dots,M\}$, $|\delta_J|_1=\sum_{j\in J}|\delta_j|$ and $|\delta_J|_2=\big(\sum_{j\in J}\delta_j^2\big)^{1/2}$; and the Euclidean norm $|v|_2=\big(\sum_i v_i^2\big)^{1/2}$.
--   2. The squared **prediction loss** $\frac1n\sum_{i=1}^n\big((X\beta)_i-f_i\big)^2$ of $\beta$ with respect to a target vector $f\in\mathbb R^n$; with $f=X\beta^*$ this is $|X(\beta-\beta^*)|_2^2/n$.
--   3. The **support** $J(\beta)=\{j:\beta_j\ne0\}$ and the **sparsity** $\mathcal M(\beta)=|J(\beta)|$.
--   4. The **unit-diagonal condition** of Section 7: every diagonal entry of the Gram matrix $\Psi_n=X^\top X/n$ equals $1$, i.e. $\frac1n\sum_{i}X_{ij}^2=1$ for all $j$.
--   5. The **Lasso** (7.2): given $y\in\mathbb R^n$ and $r\in\mathbb R$, a vector $\hat\beta_L$ is a Lasso solution if it minimises over all $\beta\in\mathbb R^M$
--   $$
--   \frac1n|y-X\beta|_2^2+2r|\beta|_1 .
--   $$
--   6. $\phi_{\max}$, the largest eigenvalue of $\Psi_n$, as the Rayleigh supremum
--   $$
--   \phi_{\max}=\sup\Big\{\tfrac1n|Xx|_2^2:\ x\in\mathbb R^M,\ |x|_2=1\Big\}.
--   $$
--   7. The **cone condition** $|\delta_{J_0^c}|_1\le c_0|\delta_{J_0}|_1$ and **Assumption RE$(s,c_0)$ with witness $\kappa$**: for every $J_0$ with $|J_0|\le s$ and every $\delta\ne0$ in the cone, $\kappa\sqrt n\,|\delta_{J_0}|_2\le|X\delta|_2$.
--   8. For $J_0$ and $\delta$, a set $J_1$ of **$m$ largest coordinates outside $J_0$**: $J_1\cap J_0=\emptyset$, $|J_1|=m$, and $|\delta_k|\le|\delta_j|$ for all $j\in J_1$, $k\notin J_0\cup J_1$. **Assumption RE$(s,m,c_0)$ with witness $\kappa$**: for every $J_0$ with $|J_0|\le s$, every $\delta\ne0$ in the cone and every such $J_1$, $\kappa\sqrt n\,|\delta_{J_{01}}|_2\le|X\delta|_2$ where $J_{01}=J_0\cup J_1$.
--   9. For a realised noise vector $w\in\mathbb R^n$ and $V_j=\frac1n\sum_iX_{ij}w_i$, the **noise event** $\mathcal A=\bigcap_{j}\{2|V_j|\le r\}$ (p. 21, where $r_{n,j}=r\|f_j\|_n=r$ under the unit diagonal).
--
--   These are the objects in terms of which Theorem 7.2 and its proof are stated.
--
--   **Formalization Note** The paper's dictionary $f_1,\dots,f_M$ and design points enter only through the matrix $X=(f_j(Z_i))$, which is taken as the datum. The paper's $\kappa(s,c_0)$ (resp. $\kappa(s,m,c_0)$) is a minimum over a compact normalised cone and is attained; the assumption "$\kappa(s,c_0)>0$" is equivalent to the existence of a witness $\kappa>0$, every witness is at most $\kappa(s,c_0)$, and every bound in which $\kappa$ appears decreases in $\kappa$, so theorems are stated for every witness. This avoids the junk value of a real infimum over an empty set ($J_0=\emptyset$). The paper's $J_1$ is "the" set of the $m$ largest coordinates; under ties every admissible choice gives the same $|\delta_{J_{01}}|_2$, and RE$(s,m,c_0)$ quantifies over all of them. The Rayleigh set defining $\phi_{\max}$ is nonempty for $M\ge1$ and bounded above, so the supremum is the largest eigenvalue. Lasso solutions are a predicate, since minimisers need not be unique.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, pp. 3–5 (notation |·|_p, J(β), 𝓜(β), φ_max); p. 7, Assumptions RE(s, c0) and RE(s, m, c0); p. 15, Eqs. (7.1), (7.2) and the unit-diagonal assumption of Section 7; p. 21, event 𝒜 (proof of Lemma B.1)

import Mathlib

namespace LassoDantzig.Lasso

/-- The ℓ1 norm `|δ|_1 = ∑ⱼ |δⱼ|` of a vector `δ ∈ ℝ^M` (Bickel–Ritov–Tsybakov, p. 4). -/
noncomputable def l1Norm {M : ℕ} (δ : Fin M → ℝ) : ℝ :=
  ∑ j, |δ j|

/-- `|δ_J|_1 = ∑_{j ∈ J} |δⱼ|`, the ℓ1 norm of the restriction `δ_J` of `δ` to `J` (p. 4). -/
noncomputable def l1On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  ∑ j ∈ J, |δ j|

/-- `|δ_J|_2 = (∑_{j ∈ J} δⱼ²)^{1/2}`, the Euclidean norm of the restriction `δ_J` (p. 4). -/
noncomputable def l2On {M : ℕ} (δ : Fin M → ℝ) (J : Finset (Fin M)) : ℝ :=
  Real.sqrt (∑ j ∈ J, δ j ^ 2)

/-- The Euclidean norm `|v|_2 = (∑ᵢ vᵢ²)^{1/2}` of a vector `v ∈ ℝ^k`. -/
noncomputable def euclNorm {k : ℕ} (v : Fin k → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

/-- The squared empirical prediction loss `(1/n) |Xβ − f|_2² = (1/n) ∑ᵢ ((Xβ)ᵢ − fᵢ)²`
(p. 4; in Section 7, with `f = Xβ*`, this is `‖f_β − f‖_n² = |X(β − β*)|_2²/n`, p. 15). -/
noncomputable def predLoss {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (f : Fin n → ℝ)
    (β : Fin M → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (X.mulVec β i - f i) ^ 2

/-- The support `J(β) = {j : βⱼ ≠ 0}` (p. 4). -/
noncomputable def supp {M : ℕ} (β : Fin M → ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun j => β j ≠ 0)

/-- The sparsity `𝓜(β) = |J(β)|`, the number of non-zero coordinates of `β` (p. 4). -/
noncomputable def sparsity {M : ℕ} (β : Fin M → ℝ) : ℕ :=
  (supp β).card

/-- The standing assumption of Section 7 (p. 15): every diagonal element of the Gram matrix
`Ψₙ = XᵀX/n` equals `1`, i.e. `‖f_j‖_n² = (1/n) ∑ᵢ X_{ij}² = 1` for every `j`. -/
def UnitDiag {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) : Prop :=
  ∀ j : Fin M, (1 / (n : ℝ)) * ∑ i, X i j ^ 2 = 1

/-- `β̂` is a Lasso estimator (7.2), p. 15: it minimises
`(1/n) |y − Xβ|_2² + 2r |β|_1` over all `β ∈ ℝ^M`. -/
def IsLasso {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (βhat : Fin M → ℝ) : Prop :=
  ∀ β : Fin M → ℝ,
    (1 / (n : ℝ)) * ∑ i, (y i - X.mulVec βhat i) ^ 2 + 2 * r * l1Norm βhat ≤
      (1 / (n : ℝ)) * ∑ i, (y i - X.mulVec β i) ^ 2 + 2 * r * l1Norm β

/-- `φ_max`, the maximal eigenvalue of the Gram matrix `Ψₙ = XᵀX/n` (p. 5, p. 20), as the
Rayleigh supremum `sup {(1/n) |Xx|_2² : x ∈ ℝ^M, |x|_2 = 1}`. The set is nonempty when `M ≥ 1`
and bounded above, so the supremum is the largest eigenvalue of the symmetric positive
semidefinite matrix `Ψₙ`. -/
noncomputable def phiMax {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) : ℝ :=
  sSup {t : ℝ | ∃ x : Fin M → ℝ, ∑ j, x j ^ 2 = 1 ∧ t = (1 / (n : ℝ)) * ∑ i, (X.mulVec x i) ^ 2}

/-- The cone condition `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1` of (4.1) and Assumption RE(s, c₀) (p. 7). -/
def ConeCond {M : ℕ} (c0 : ℝ) (J0 : Finset (Fin M)) (δ : Fin M → ℝ) : Prop :=
  l1On δ J0ᶜ ≤ c0 * l1On δ J0

/-- Assumption RE(s, c₀) (p. 7) with witness `κ`: for every `J₀ ⊆ {1, …, M}` with `|J₀| ≤ s`
and every `δ ≠ 0` with `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1`, `κ √n |δ_{J₀}|_2 ≤ |Xδ|_2`.
The paper's `κ(s, c₀)` is the largest such `κ`; Assumption RE(s, c₀) is "`RE X s c0 κ` for
some `κ > 0`". -/
def RE {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    κ * Real.sqrt n * l2On δ J0 ≤ euclNorm (X.mulVec δ)

/-- `J₁` is a set of `m` indices outside `J₀` carrying `m` largest absolute values among the
coordinates of `δ` outside `J₀` (p. 7). Under ties several sets qualify; they all give the same
`|δ_{J₀ ∪ J₁}|_2`. -/
def IsTopOutside {M : ℕ} (m : ℕ) (J0 : Finset (Fin M)) (δ : Fin M → ℝ)
    (J1 : Finset (Fin M)) : Prop :=
  J1 ⊆ J0ᶜ ∧ J1.card = m ∧ ∀ j ∈ J1, ∀ k ∈ J0ᶜ \ J1, |δ k| ≤ |δ j|

/-- Assumption RE(s, m, c₀) (p. 7) with witness `κ`: for every `J₀` with `|J₀| ≤ s`, every
`δ ≠ 0` with `|δ_{J₀ᶜ}|_1 ≤ c₀ |δ_{J₀}|_1`, and every set `J₁` of the `m` largest in absolute
value coordinates of `δ` outside `J₀`, `κ √n |δ_{J₀₁}|_2 ≤ |Xδ|_2` with `J₀₁ = J₀ ∪ J₁`.
The paper's `κ(s, m, c₀)` is the largest such `κ`. -/
def REm {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s m : ℕ) (c0 κ : ℝ) : Prop :=
  ∀ J0 : Finset (Fin M), J0.card ≤ s → ∀ δ : Fin M → ℝ, δ ≠ 0 → ConeCond c0 J0 δ →
    ∀ J1 : Finset (Fin M), IsTopOutside m J0 δ J1 →
      κ * Real.sqrt n * l2On δ (J0 ∪ J1) ≤ euclNorm (X.mulVec δ)

/-- The noise event `𝒜 = ⋂ⱼ {2|Vⱼ| ≤ r}` (p. 21, with `r_{n,j} = r‖f_j‖_n = r` under the unit
diagonal of Section 7), as a property of a realised noise vector `w ∈ ℝⁿ`, where
`Vⱼ = (1/n) ∑ᵢ X_{ij} wᵢ`. -/
def NoiseEventHalf {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (r : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ j : Fin M, 2 * |(1 / (n : ℝ)) * ∑ i, X i j * w i| ≤ r

end LassoDantzig.Lasso


