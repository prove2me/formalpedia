-- Prove2me | Definitions.Def_LassoDantzig_REConditions_RestrictedEigenvalues
-- name    : LassoDantzig_REConditions_RestrictedEigenvalues
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T10:04:44.754093+00:00
-- url     : https://prove2.me/theorems/52a5da21-412e-4b38-a331-594d4121c0ac
-- title:
--   Restricted eigenvalues $\phi_{\min}(u),\phi_{\max}(u)$, restricted correlations $\theta_{m_1,m_2}$, Assumptions 1–2 and $\kappa_1,\kappa_2$
-- statement:
--   Let $X\in\mathbb R^{n\times M}$ and $\Psi_n=X^TX/n$ be its Gram matrix, so that $x^T\Psi_nx=\frac1n|Xx|_2^2$. For an integer $u\ge1$ the **restricted eigenvalues** are
--
--   $$
--   \phi_{\min}(u)=\min_{x\in\mathbb R^M:\,1\le\mathcal M(x)\le u}\frac{x^T\Psi_nx}{|x|_2^2},\qquad
--   \phi_{\max}(u)=\max_{x\in\mathbb R^M:\,1\le\mathcal M(x)\le u}\frac{x^T\Psi_nx}{|x|_2^2},
--   $$
--
--   where $\mathcal M(x)$ is the number of non-zero coordinates of $x$. Writing $X_I$ for the $n\times|I|$ submatrix of the columns indexed by $I$, the **restricted correlations** are, for $m_1,m_2\ge1$,
--
--   $$
--   \theta_{m_1,m_2}=\max\left\{\frac{c_1^TX_{I_1}^TX_{I_2}c_2}{n\,|c_1|_2\,|c_2|_2}:\ I_1\cap I_2=\emptyset,\ |I_i|\le m_i,\ c_i\in\mathbb R^{I_i}\setminus\{0\},\ i=1,2\right\}.
--   $$
--
--   **Assumption 1** is $\phi_{\min}(2s)>c_0\,\theta_{s,2s}$ and **Assumption 2** is $m\,\phi_{\min}(s+m)>c_0^2\,s\,\phi_{\max}(m)$. The constants attached to them are
--
--   $$
--   \kappa_1(s,c_0)=\sqrt{\phi_{\min}(2s)}\left(1-\frac{c_0\,\theta_{s,2s}}{\phi_{\min}(2s)}\right),\qquad
--   \kappa_2(s,m,c_0)=\sqrt{\phi_{\min}(s+m)}\left(1-c_0\sqrt{\frac{s\,\phi_{\max}(m)}{m\,\phi_{\min}(s+m)}}\right).
--   $$
--
--   These are the classical sparse-eigenvalue and correlation conditions (Candès–Tao, Meinshausen–Yu) that Lemma 4.1 shows to imply the restricted eigenvalue assumptions.
--
--   **Formalization Note** $u$ is a natural number (the paper allows real $u$, but $\mathcal M(x)$ is an integer, so $\phi(u)=\phi(\lfloor u\rfloor)$). The minimum and maximum are written as `sInf`/`sSup` of the set of Rayleigh quotients: for $1\le u$ and $M\ge1$ the set is nonempty (a basis vector) and bounded (it lies in $[0,\frac1n\sum_{i,j}X_{ij}^2]$) and the extremes are attained, so `sInf`/`sSup` are the paper's min/max. In $\theta$, the vectors $c_i\in\mathbb R^{I_i}$ are encoded as vectors of $\mathbb R^M$ supported in $I_i$, so $c_1^TX_{I_1}^TX_{I_2}c_2=\sum_i(Xc_1)_i(Xc_2)_i$; for $M\ge2$ the set is nonempty (two disjoint singletons), bounded by Cauchy–Schwarz and symmetric under $c_1\mapsto-c_1$, hence $\theta\ge0$ and `sSup` is the maximum. The ranges of $s,m,c_0$ are hypotheses of the theorems, not part of the definitions of Assumptions 1 and 2.
-- source:
--   Bickel, Ritov and Tsybakov, Simultaneous Analysis of Lasso and Dantzig Selector, arXiv:0801.1095v3, p. 8 (restricted eigenvalues, restricted correlations, Assumptions 1 and 2), p. 9 (κ1, κ2)

import Mathlib
import Definitions.Def_LassoDantzig_REConditions_RE

namespace LassoDantzig.REConditions

/-- The quadratic form `xᵀ Ψ_n x = (1/n) |X x|_2²` of the Gram matrix `Ψ_n = XᵀX/n` (p. 5). -/
noncomputable def gramQuad {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (x : Fin M → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (X.mulVec x i) ^ 2

/-- The set of Rayleigh quotients `xᵀΨ_n x / |x|_2²` over `x ∈ ℝ^M` with `1 ≤ 𝓜(x) ≤ u`. -/
def rayleighSet {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (u : ℕ) : Set ℝ :=
  {q | ∃ x : Fin M → ℝ, 1 ≤ sparsity x ∧ sparsity x ≤ u ∧
    q = gramQuad X x / ∑ j, x j ^ 2}

/-- The restricted eigenvalue `φ_min(u) = min_{1 ≤ 𝓜(x) ≤ u} xᵀΨ_n x / |x|_2²` (p. 8).
For `1 ≤ u` and `M ≥ 1` the set is nonempty (a basis vector) and lies in a bounded interval
`[0, C]`, and the minimum is attained, so `sInf` is the paper's minimum. -/
noncomputable def phiMin {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (u : ℕ) : ℝ :=
  sInf (rayleighSet X u)

/-- The restricted eigenvalue `φ_max(u) = max_{1 ≤ 𝓜(x) ≤ u} xᵀΨ_n x / |x|_2²` (p. 8).
For `1 ≤ u` and `M ≥ 1` the set is nonempty and bounded, and the maximum is attained, so
`sSup` is the paper's maximum. -/
noncomputable def phiMax {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (u : ℕ) : ℝ :=
  sSup (rayleighSet X u)

/-- The set whose maximum is the restricted correlation `θ_{m1,m2}` (p. 8): the values
`c1ᵀ X_{I1}ᵀ X_{I2} c2 / (n |c1|_2 |c2|_2)` over disjoint `I1, I2` with `|I1| ≤ m1`,
`|I2| ≤ m2` and non-zero `c1 ∈ ℝ^{I1}`, `c2 ∈ ℝ^{I2}` (encoded as vectors of `ℝ^M` supported in
`I1`, `I2`, so that `c1ᵀ X_{I1}ᵀ X_{I2} c2 = ∑_i (X c1)_i (X c2)_i`). -/
def corrSet {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (m1 m2 : ℕ) : Set ℝ :=
  {t | ∃ I1 I2 : Finset (Fin M), Disjoint I1 I2 ∧ I1.card ≤ m1 ∧ I2.card ≤ m2 ∧
    ∃ c1 c2 : Fin M → ℝ, (∀ j, j ∉ I1 → c1 j = 0) ∧ (∀ j, j ∉ I2 → c2 j = 0) ∧
      c1 ≠ 0 ∧ c2 ≠ 0 ∧
      t = (∑ i, X.mulVec c1 i * X.mulVec c2 i) /
        ((n : ℝ) * Real.sqrt (∑ j, c1 j ^ 2) * Real.sqrt (∑ j, c2 j ^ 2))}

/-- The restricted correlation `θ_{m1,m2}` (p. 8). For `M ≥ 2`, `m1, m2 ≥ 1` the set is
nonempty (two disjoint singletons), bounded (Cauchy–Schwarz) and its maximum is attained, so
`sSup` is the paper's maximum; the set is symmetric under `c1 ↦ -c1`, so `θ ≥ 0`. -/
noncomputable def theta {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (m1 m2 : ℕ) : ℝ :=
  sSup (corrSet X m1 m2)

/-- Assumption 1 (p. 8): `φ_min(2s) > c₀ θ_{s,2s}`. (The ranges `1 ≤ s ≤ M/2`, `c₀ > 0` are
hypotheses of the theorems that use it.) -/
def Assumption1 {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 : ℝ) : Prop :=
  c0 * theta X s (2 * s) < phiMin X (2 * s)

/-- Assumption 2 (pp. 8–9): `m φ_min(s + m) > c₀² s φ_max(m)`. (The ranges `1 ≤ s ≤ M/2`,
`m ≥ s`, `s + m ≤ M`, `c₀ > 0` are hypotheses of the theorems that use it.) -/
def Assumption2 {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s m : ℕ) (c0 : ℝ) : Prop :=
  c0 ^ 2 * (s : ℝ) * phiMax X m < (m : ℝ) * phiMin X (s + m)

/-- `κ₁(s, c₀) = √φ_min(2s) · (1 − c₀ θ_{s,2s} / φ_min(2s))` (p. 9). -/
noncomputable def kappa1 {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s : ℕ) (c0 : ℝ) : ℝ :=
  Real.sqrt (phiMin X (2 * s)) * (1 - c0 * theta X s (2 * s) / phiMin X (2 * s))

/-- `κ₂(s, m, c₀) = √φ_min(s+m) · (1 − c₀ √(s φ_max(m) / (m φ_min(s+m))))` (p. 9). -/
noncomputable def kappa2 {n M : ℕ} (X : Matrix (Fin n) (Fin M) ℝ) (s m : ℕ) (c0 : ℝ) : ℝ :=
  Real.sqrt (phiMin X (s + m)) *
    (1 - c0 * Real.sqrt ((s : ℝ) * phiMax X m / ((m : ℝ) * phiMin X (s + m))))

end LassoDantzig.REConditions


