-- Prove2me | Definitions.Def_ImpuritySim_Model
-- name    : ImpuritySim_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:31:21.147203+00:00
-- url     : https://prove2.me/theorems/1ca47743-5560-416c-a099-a7a4b21ad255
-- title:
--   The quantum impurity model $H=H_0+H_{\mathrm{imp}}$ (1.1) and its bath block $h_{\mathrm{bath}}$ (2.12)
-- statement:
--   A **quantum impurity model** on $n$ fermionic modes with impurity size $m\le n$ is
--   $$H=H_0+H_{\mathrm{imp}},\qquad H_0=\alpha I+\frac i4\sum_{j,k=1}^{2n}h_{jk}\gamma_j\gamma_k,\qquad(1.1)$$
--   where $\alpha\in\mathbb R$ is an energy shift, $h$ is a real antisymmetric $2n\times2n$ matrix, and the impurity term is an even Hermitian polynomial in the first $2m$ Majoranas,
--   $$H_{\mathrm{imp}}=\sum_{A\subseteq\{1,\dots,2m\},\ |A|\ \mathrm{even}}c_A\,\Gamma_A,\qquad c_A\in\mathbb R.$$
--   The **bath block** $h_{\mathrm{bath}}$ is the principal submatrix of $h$ on the bath Majoranas $\gamma_{2m+1},\dots,\gamma_{2n}$ (2.12); its spectral norm bounds the bath single-particle energies, $\|h_{\mathrm{bath}}\|\le J$.
--
--   This is the object of the goal theorem (Theorem 5.3).
--
--   **Formalization Note** The page describes $H_{\mathrm{imp}}$ as "a sum of even-degree products" of $\gamma_1,\dots,\gamma_{2m}$, part of a Hermitian Hamiltonian. The Majorana monomials form a basis of the algebra they generate and each $\Gamma_A$ is Hermitian, so every even Hermitian element has exactly one expansion $\sum_{|A|\text{ even}}c_A\Gamma_A$ with real $c_A$; the coefficient function is the input. Antisymmetry of $h$ is a hypothesis of the theorems that use it.
-- source:
--   Jiang–Ju–Parekh–Rayudu–Zhao, Polynomial-time classical and quantum simulation of quantum impurity models, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2), (1.1), p.4; (2.12), p.12; (A.4), p.53

import Mathlib
import Definitions.Def_ImpuritySim_Fermion

open Matrix

namespace ImpuritySim

/-!
# The quantum impurity model (1.1) and its bath block (2.12)

J. Jiang, N. Ju, O. Parekh, C. Rayudu, A. Zhao, *Polynomial-time classical and quantum simulation
of quantum impurity models*, arXiv:2610.02167 (held version, sha256 88d2a4e6…f0fff9b2): (1.1),
p.4; (2.12), p.12.

**Formalization Note.**
* `H0 n α h = αI + (i/4) Σ_{j,k=1}^{2n} h_{jk} γ_j γ_k` (1.1), with `h` a real `2n × 2n` matrix
  (antisymmetry is a hypothesis where it is used) and the Majoranas 0-based.
* `Himp n m hmn c = Σ_{A ⊆ [2m], |A| even} c_A Γ_A`, with `Γ_A` the Hermitian Majorana monomial of
  `γ_1, …, γ_{2m}` (the first `2m` Majoranas, embedded by `Fin.castLE`). Every even Hermitian
  polynomial in `γ_1, …, γ_{2m}` ("a sum of even-degree products of these operators", supported on
  the first `m` modes) has exactly one such expansion with real `c_A`, since the `Γ_A` are a
  basis and `Γ_A` is Hermitian. Coefficients `c_A` with `|A|` odd are ignored.
* `Hmodel = H0 + Himp` (1.1).
* `hBath n m h` is the principal submatrix of `h` on the bath Majoranas `γ_{2m+1}, …, γ_{2n}`
  (0-based indices `2m, …, 2n−1`), of size `(2n − 2m) × (2n − 2m)` (2.12).
-/

/-- The free part `H0 = αI + (i/4) Σ_{j,k} h_{jk} γ_j γ_k` of (1.1). -/
noncomputable def H0 (n : ℕ) (α : ℝ) (h : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : FermiCap.Gaussian.Op n :=
  ((α : ℝ) : ℂ) • (1 : FermiCap.Gaussian.Op n) +
    (Complex.I / 4) • ∑ j, ∑ k, ((h j k : ℝ) : ℂ) • (gamma n j * gamma n k)

/-- The impurity term `H_imp = Σ_{A ⊆ [2m], |A| even} c_A Γ_A`, supported on `γ_1, …, γ_{2m}`. -/
noncomputable def Himp (n m : ℕ) (hmn : m ≤ n) (c : Finset (Fin (2 * m)) → ℝ) :
    FermiCap.Gaussian.Op n :=
  ∑ A ∈ (Finset.univ : Finset (Finset (Fin (2 * m)))).filter (fun A => Even A.card),
    ((c A : ℝ) : ℂ) • majMono n (A.map (Fin.castLEEmb (by omega)))

/-- The quantum impurity model `H = H0 + H_imp` (1.1). -/
noncomputable def Hmodel (n m : ℕ) (hmn : m ≤ n) (α : ℝ) (h : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (c : Finset (Fin (2 * m)) → ℝ) : FermiCap.Gaussian.Op n :=
  H0 n α h + Himp n m hmn c

/-- `h_bath`, the principal submatrix of `h` on the bath Majoranas `γ_{2m+1}, …, γ_{2n}` (2.12). -/
def hBath (n m : ℕ) (h : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) :
    Matrix (Fin (2 * n - 2 * m)) (Fin (2 * n - 2 * m)) ℝ :=
  h.submatrix (fun k => ⟨2 * m + k.val, by omega⟩) (fun k => ⟨2 * m + k.val, by omega⟩)

end ImpuritySim


