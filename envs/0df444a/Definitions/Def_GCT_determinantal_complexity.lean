-- Prove2me | Definitions.Def_GCT_determinantal_complexity
-- name    : GCT_determinantal_complexity
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T16:13:12.102093+00:00
-- url     : https://prove2.me/theorems/be509c1b-9d58-48d9-94e2-5d25507f7411
-- title:
--   Determinantal and border determinantal complexity of the permanent
-- statement:
--   The setting of the determinant versus permanent problem, following Landsberg.
--
--   Fix $m$ and let $\mathrm{perm}_m = \sum_{\sigma \in S_m} \prod_i y_{\sigma(i) i}$ be the permanent of an $m \times m$ matrix of variables, a homogeneous polynomial of degree $m$ in $m^2$ variables, and let $\det_n$ be the determinant of an $n \times n$ matrix of variables, a homogeneous polynomial of degree $n$ on $W = \mathbb{C}^{n^2}$. With an auxiliary linear coordinate $\ell$ and a linear inclusion $\mathbb{C}^{m^2+1} \hookrightarrow W$, the padded permanent $\ell^{\,n-m}\mathrm{perm}_m$ is a degree-$n$ element of $S^n W$.
--
--   Acting on $S^n W$ by linear substitution, $\mathrm{End}(W) \cdot \det_n$ is the set of polynomials $\det_n \circ \Lambda$; concretely these are exactly the determinants of $n \times n$ matrices whose entries are homogeneous linear forms. Its closure is the orbit closure $\mathrm{Det}_n = \overline{GL(W) \cdot [\det_n]}$, and membership in that closure is rendered here as a coefficientwise limit of such determinants.
--
--   This gives the two complexity measures of the mission:
--
--   $$\mathrm{dc}(\mathrm{perm}_m) = \min\{n \ge m : \ell^{\,n-m}\mathrm{perm}_m \in \mathrm{End}(W) \cdot \det_n\},$$
--   $$\overline{\mathrm{dc}}(\mathrm{perm}_m) = \min\{n \ge m : \ell^{\,n-m}\mathrm{perm}_m \in \overline{\mathrm{End}(W) \cdot \det_n}\}.$$
--
--   The affine variant — $\mathrm{perm}_m$ is an affine linear projection of $\det_n$, i.e. the determinant of an $n \times n$ matrix of affine-linear forms — is Valiant's original definition of determinantal complexity, and is included so that the equivalence of the two formulations can itself be a milestone.
-- source:
--   J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge Studies in Advanced Mathematics 169, CUP 2017, DOI 10.1017/9781108183192, pp. 14–16: Definition 1.2.4.1 (determinantal complexity), Equation (1.2.4), Definition 1.2.5.1 (border determinantal complexity); J. M. Landsberg, *Geometric Complexity Theory: an introduction for geometers*, arXiv:1305.7387v3, https://arxiv.org/abs/1305.7387, pp. 3–4, §2.1.

import Mathlib

namespace GCT

open MvPolynomial

/-- Variables for the padded permanent of size `m`: `none` is the auxiliary padding
coordinate `ℓ`, and `some (i, j)` is the matrix entry `y_{ij}`. -/
abbrev PadVars (m : ℕ) := Option (Fin m × Fin m)

/-- The permanent polynomial `perm_m = ∑_{σ ∈ S_m} y_{σ(1)1} ⋯ y_{σ(m)m}` in the `m²`
variables `y_{ij}`. -/
noncomputable def permPoly (m : ℕ) : MvPolynomial (Fin m × Fin m) ℂ :=
  Matrix.permanent (Matrix.of fun i j => (X (i, j) : MvPolynomial (Fin m × Fin m) ℂ))

/-- The permanent polynomial `perm_m`, written in the variable set `PadVars m`, which
also carries the padding variable `ℓ`. -/
noncomputable def permPolyPad (m : ℕ) : MvPolynomial (PadVars m) ℂ :=
  Matrix.permanent (Matrix.of fun i j => (X (some (i, j)) : MvPolynomial (PadVars m) ℂ))

/-- The padded permanent `ℓ^(n-m) perm_m`; it is homogeneous of degree `n` when `m ≤ n`. -/
noncomputable def paddedPerm (m n : ℕ) : MvPolynomial (PadVars m) ℂ :=
  (X none) ^ (n - m) * permPolyPad m

/-- `HasLinearDetRep n p` : `p = det_n ∘ Λ` for a linear substitution `Λ`, i.e. `p` is the
determinant of an `n × n` matrix whose entries are homogeneous linear forms (possibly `0`).
This is membership of `p` in the affine cone over `End(W) · det_n`. -/
def HasLinearDetRep {σ : Type*} (n : ℕ) (p : MvPolynomial σ ℂ) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ),
    (∀ i j, (A i j).IsHomogeneous 1) ∧ A.det = p

/-- `HasBorderLinearDetRep n p` : `p` is a coefficientwise limit of determinants
`det_n ∘ Λ_k` of matrices of homogeneous linear forms, i.e. `p` lies in the affine cone
over the orbit closure `Det_n = GL(W) · [det_n]`. -/
def HasBorderLinearDetRep {σ : Type*} (n : ℕ) (p : MvPolynomial σ ℂ) : Prop :=
  ∃ A : ℕ → Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ),
    (∀ k i j, (A k i j).IsHomogeneous 1) ∧
      ∀ d : σ →₀ ℕ,
        Filter.Tendsto (fun k => coeff d ((A k).det)) Filter.atTop (nhds (coeff d p))

/-- `HasAffineDetRep n p` : `p` is the determinant of an `n × n` matrix whose entries are
affine-linear polynomials (total degree at most `1`), i.e. `p` is an affine linear
projection of `det_n`. -/
def HasAffineDetRep {σ : Type*} (n : ℕ) (p : MvPolynomial σ ℂ) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ),
    (∀ i j, (A i j).totalDegree ≤ 1) ∧ A.det = p

/-- The determinantal complexity `dc(perm_m)`: the least `n ≥ m` such that
`ℓ^(n-m) perm_m ∈ End(W) · det_n`. -/
noncomputable def dc (m : ℕ) : ℕ :=
  sInf {n : ℕ | m ≤ n ∧ HasLinearDetRep n (paddedPerm m n)}

/-- The border determinantal complexity `dcBar(perm_m)`: the least `n ≥ m` such that
`ℓ^(n-m) perm_m` lies in the orbit closure `Det_n = GL(W) · [det_n]`. -/
noncomputable def dcBar (m : ℕ) : ℕ :=
  sInf {n : ℕ | m ≤ n ∧ HasBorderLinearDetRep n (paddedPerm m n)}

end GCT


