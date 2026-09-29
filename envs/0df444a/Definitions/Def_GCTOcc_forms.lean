-- Prove2me | Definitions.Def_GCTOcc_forms
-- name    : GCTOcc_forms
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T17:09:12.047921+00:00
-- url     : https://prove2.me/theorems/bc8f167e-b945-4226-8a5f-ba95a66244e8
-- title:
--   Forms, the padded permanent, and orbit closures $\Omega_n$, $Z_{n,m}$
-- statement:
--   This file fixes the objects of the permanent versus determinant problem in the orbit-closure formulation.
--
--   All polynomials live in a single ring of complex polynomials whose variables $X_{ij}$ are indexed by pairs of natural numbers; the $n \times n$ matrix of variables occupies the indices $i, j < n$, so polynomials of different sizes sit in one ring and no renaming maps are needed.
--
--   1. The **permanent** and the **determinant** of the matrix of variables,
--   $$\mathrm{per}_m = \sum_{\sigma \in S_m} \prod_{i<m} X_{i\,\sigma(i)}, \qquad \det\nolimits_n = \sum_{\sigma \in S_n} \mathrm{sgn}(\sigma)\prod_{i<n} X_{i\,\sigma(i)} .$$
--   2. The **padded permanent** $X_{00}^{\,n-m}\,\mathrm{per}_m$, which is a form of degree $n$ whenever $m \le n$. The padding variable is the $(0,0)$ entry of the matrix, as in the source; the choice of padding linear form is known to be immaterial.
--   3. The **linear form** $\sum_{v} a_v X_v$ attached to a vector of coefficients on the $n^2$ matrix positions.
--   4. The predicate "$p$ is a **form of degree $n$**": $p$ is homogeneous of degree $n$ and involves only the $n^2$ variables of the $n \times n$ block. These are the points of $\mathrm{Sym}^n(\mathbb{C}^{n\times n})^*$.
--   5. The predicate "$p$ is a **symbolic determinant of size $n$**": $p = \det L$ for an $n \times n$ matrix $L$ whose entries are affine linear, that is of total degree at most one. Valiant's determinantal complexity of $p$ is the least such $n$.
--   6. The **action by linear substitution**: a matrix $g$ indexed by the $n^2$ matrix positions acts on a polynomial by $X_v \mapsto \sum_w g_{vw} X_w$ inside the block, leaving the variables outside the block untouched. For invertible $g$ this is the substitution $p \mapsto p \circ g$, that is $g^{-1} \cdot p$ for the standard action $(g\cdot p)(v) = p(g^{-1}v)$; as the invertible matrices form a group, the orbit of a form does not depend on this choice.
--   7. The **orbit closure** $\overline{\mathrm{GL}_{n^2}\cdot p_0}$: the set of polynomials $p$ for which there is a sequence of invertible matrices $g_k$ such that every coefficient of $g_k \cdot p_0$ converges to the corresponding coefficient of $p$. On the finite-dimensional space of degree $n$ forms this coefficientwise sequential closure is the Euclidean closure, which for an orbit of an algebraic group action coincides with the Zariski closure.
--
--   Taking $p_0 = \det_n$ gives $\Omega_n$ and taking $p_0 = X_{00}^{\,n-m}\mathrm{per}_m$ gives $Z_{n,m}$; these two sets are the objects compared throughout the mission.
-- source:
--   P. Bürgisser, C. Ikenmeyer, G. Panova, *No occurrence obstructions in geometric complexity theory*, J. Amer. Math. Soc. 32 (2019), 163–193, https://doi.org/10.1090/jams/908, pp. 164–165, §1 and §1(a): the determinant, the padded permanent $X_{11}^{n-m}\mathrm{per}_m$, the orbit closures $\Omega_n$ (1.1) and $Z_{n,m}$ (1.2), and determinantal complexity.

import Mathlib

namespace GCTOcc

open MvPolynomial

/-- The ambient polynomial ring: complex polynomials in variables `X (i, j)` indexed by pairs
of natural numbers.  The `n × n` matrix of variables occupies the indices `i, j < n`, so all
sizes live in one ring and no renaming maps are needed. -/
abbrev PolyR : Type := MvPolynomial (ℕ × ℕ) ℂ

/-- The permanent `per_m = ∑_{σ ∈ S_m} ∏_{i<m} X (i, σ i)` of the `m × m` matrix of
variables. -/
noncomputable def permPoly (m : ℕ) : PolyR :=
  ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, (X ((i : ℕ), ((σ i : Fin m) : ℕ)) : PolyR)

/-- The determinant `det_n = ∑_{σ ∈ S_n} sgn(σ) ∏_{i<n} X (i, σ i)` of the `n × n` matrix of
variables. -/
noncomputable def detPoly (n : ℕ) : PolyR :=
  ∑ σ : Equiv.Perm (Fin n),
    (Equiv.Perm.sign σ : ℤ) • ∏ i : Fin n, (X ((i : ℕ), ((σ i : Fin n) : ℕ)) : PolyR)

/-- The padded permanent `X_{0,0}^{n-m} · per_m`, homogeneous of degree `n` when `m ≤ n`.
The padding variable is the `(0,0)` entry of the matrix of variables. -/
noncomputable def paddedPerm (m n : ℕ) : PolyR :=
  (X (0, 0) : PolyR) ^ (n - m) * permPoly m

/-- The linear form `∑_{v} a_v X_v` in the `n²` variables of an `n × n` matrix. -/
noncomputable def linForm (n : ℕ) (a : Fin n × Fin n → ℂ) : PolyR :=
  ∑ v : Fin n × Fin n, C (a v) * X (((v.1 : ℕ)), ((v.2 : ℕ)))

/-- `p` is a degree `n` form in the `n²` variables `X (i, j)`, `i, j < n`; these are the
points of `Sym^n (ℂ^{n×n})^*`. -/
def IsForm (n : ℕ) (p : PolyR) : Prop :=
  p.IsHomogeneous n ∧ ∀ m ∈ p.support, ∀ v ∈ m.support, v.1 < n ∧ v.2 < n

/-- `p` is the determinant of an `n × n` matrix whose entries are affine linear (total degree
at most one): an affine linear projection of `det_n`. -/
def IsSymbolicDet (p : PolyR) (n : ℕ) : Prop :=
  ∃ L : Matrix (Fin n) (Fin n) PolyR, (∀ i j, (L i j).totalDegree ≤ 1) ∧ L.det = p

/-- The action of `g ∈ ℂ^{(n×n)×(n×n)}` on polynomials by linear substitution of the
variables of the `n × n` block: `X v ↦ ∑_w g v w * X w`.  Variables outside the block are
left untouched (no polynomial considered here uses them).  For invertible `g` this is the
substitution `p ↦ p ∘ g`, i.e. the element `g⁻¹ · p` for the action
`(g · p)(v) = p (g⁻¹ v)`; since the invertible matrices form a group, the orbit of a form is
the same under either convention. -/
noncomputable def substLin (n : ℕ) (g : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (p : PolyR) :
    PolyR :=
  aeval (fun v : ℕ × ℕ =>
    if h : v.1 < n ∧ v.2 < n then
      ∑ w : Fin n × Fin n,
        C (g (⟨v.1, h.1⟩, ⟨v.2, h.2⟩) w) * X (((w.1 : ℕ)), ((w.2 : ℕ)))
    else X v) p

/-- The orbit closure `GL_{n²} · p₀` in the Euclidean topology: `p` lies in it exactly when
`p` is the coefficientwise limit of a sequence of orbit points `g_k · p₀` with every `g_k`
invertible. -/
def orbitClosure (n : ℕ) (p₀ : PolyR) : Set PolyR :=
  {p | ∃ g : ℕ → Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ,
        (∀ k, IsUnit (g k).det) ∧
        ∀ m : (ℕ × ℕ) →₀ ℕ,
          Filter.Tendsto (fun k => coeff m (substLin n (g k) p₀)) Filter.atTop
            (nhds (coeff m p))}

end GCTOcc


