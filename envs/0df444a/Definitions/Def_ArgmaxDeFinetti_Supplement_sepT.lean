-- Prove2me | Definitions.Def_ArgmaxDeFinetti_Supplement_sepT
-- name    : ArgmaxDeFinetti_Supplement_sepT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:39:22.446104+00:00
-- url     : https://prove2.me/theorems/f76227e4-9726-41e7-845b-8d64cee140ce
-- title:
--   Tensor powers, Hartree mixtures $\mathrm{SEP}^{(t)}_H$ and tensor-power mixtures $\mathrm{SEP}^{(t)}_P$
-- statement:
--   For a finite site space $\mathbb C^\iota$, a vector $u$ and an operator $X$ on $\mathbb C^\iota$, the tensor powers are $u^{\otimes t}(i_1,\dots,i_t)=u_{i_1}\cdots u_{i_t}$ and $X^{\otimes t}(a,b)=\prod_{k}X(a_k,b_k)$. The two separable families of $t$-site states are
--
--   $$
--   \mathrm{SEP}^{(t)}_H=\mathrm{conv}\{|u\rangle\langle u|^{\otimes t}:\ u\in\mathbb C^\iota,\ \|u\|=1\},\qquad
--   \mathrm{SEP}^{(t)}_P=\mathrm{conv}\{\sigma^{\otimes t}:\ \sigma\in D(\mathbb C^\iota)\},
--   $$
--
--   the **Hartree mixtures** and the **tensor-power mixtures**. With $\iota=\{1,\dots,d\}$ these are $\mathrm{SEP}^{(t)}_H(d)$ and $\mathrm{SEP}^{(t)}_P(d)$; with the composite site $\iota=\{1,\dots,r\}^2$ the first is $\mathrm{SEP}^{(t)}_H(r^2)$.
--
--   They are the approximating sets of the bosonic and exchangeable de Finetti theorems, respectively.
--
--   **Formalization Note** $\mathrm{conv}$ is the real convex hull of finitely many points in the matrix space, $\|u\|$ the Euclidean norm, and $D(\mathbb C^\iota)$ the density operators (positive semidefinite, trace one). For $t=2$, $\iota=\{1,\dots,d\}$ the Hartree set is the base mission's $\mathrm{SEP}^{(2)}_H(d)$.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Separable state families", p.18; (1.1)–(1.2), p.6

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ArgmaxDeFinetti_vnorm

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- The tensor power `u^{⊗t} ∈ (ℂ^ι)^{⊗t}`, `(u^{⊗t})(i₁, …, i_t) = u_{i₁} ⋯ u_{i_t}`, for a site space `ℂ^ι`,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1, p.18.

**Formalization Note** For `ι = Fin d` this is the base mission's `tensorPow`; the site type is general so that
composite sites `ℂ^r ⊗ ℂ^r` (`ι = Fin r × Fin r`) are covered. -/
def tensorPowI {ι : Type} (u : ι → ℂ) (t : ℕ) : (Fin t → ι) → ℂ :=
  fun i => ∏ k, u (i k)

/-- The Kronecker power `X^{⊗t}` of an operator `X` on `ℂ^ι`, an operator on `(ℂ^ι)^{⊗t}` with entries
`X^{⊗t}(a, b) = ∏_k X(a_k, b_k)`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1, p.18 (the states `σ^{⊗t}`) and p.61 (`U^{⊗n}`). -/
def kronPow {ι : Type} (X : Matrix ι ι ℂ) (t : ℕ) : Matrix (Fin t → ι) (Fin t → ι) ℂ :=
  fun a b => ∏ k, X (a k) (b k)

/-- The `t`-site Hartree mixtures `SEP^{(t)}_H = conv{|u⟩⟨u|^{⊗t} : u ∈ ℂ^ι, ∥u∥ = 1}`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1
"Separable state families", p.18 (also (1.1), p.6).

**Formalization Note** `conv` is the real convex hull `convexHull ℝ` (finite convex combinations) in the matrix
space, and `∥u∥` the Euclidean norm `vnorm`. `SEP^{(t)}_H(d)` is `hartreeT (Fin d) t`; for `t = 2` it is the base
mission's `hartree2 d`. `SEP^{(t)}_H(r²)` of Appendix B is `hartreeT (Fin r × Fin r) t` (the site `ℂ^r ⊗ ℂ^r`). -/
def hartreeT (ι : Type) [Fintype ι] (t : ℕ) : Set (Matrix (Fin t → ι) (Fin t → ι) ℂ) :=
  convexHull ℝ {σ | ∃ u : ι → ℂ, vnorm u = 1 ∧ σ = Matrix.vecMulVec (tensorPowI u t) (star (tensorPowI u t))}

/-- The `t`-site tensor-power mixtures `SEP^{(t)}_P = conv{σ^{⊗t} : σ ∈ D(ℂ^ι)}`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), §2.1 "Separable
state families", p.18 (also (1.2), p.6).

**Formalization Note** `conv` is `convexHull ℝ` in the matrix space; `D(ℂ^ι)` is the published
`WildeQIT.IsDensityOperator` (positive semidefinite, trace one). `SEP^{(t)}_P(d)` is `tensorPowMix (Fin d) t`. -/
def tensorPowMix (ι : Type) [Fintype ι] (t : ℕ) : Set (Matrix (Fin t → ι) (Fin t → ι) ℂ) :=
  convexHull ℝ {τ | ∃ σ : Matrix ι ι ℂ, WildeQIT.IsDensityOperator σ ∧ τ = kronPow σ t}

end Supplement

end ArgmaxDeFinetti


