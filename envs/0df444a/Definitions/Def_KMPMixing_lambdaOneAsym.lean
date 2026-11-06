-- Prove2me | Definitions.Def_KMPMixing_lambdaOneAsym
-- name    : KMPMixing_lambdaOneAsym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:27.713953+00:00
-- url     : https://prove2.me/theorems/490872a5-8f0e-4ca5-a13b-8941de803d93
-- title:
--   The two-particle matrix $C$ and $\lambda_1(C|_{\mathcal H_{\mathrm{Asym}}})$
-- statement:
--   For an edge $e=\{a,b\}$ let $C_e$ be the $d\times d$ matrix with $C_e(y,z)=\tfrac12$ if $y,z\in\{a,b\}$, $C_e(y,z)=1$ if $y=z\notin\{a,b\}$, and $0$ otherwise; it is $\mathbb E_p[A_{e,p}]$. Define on functions of $V\times V$
--   $$
--   C=\frac1{|E|}\sum_{e\in E}C_e\otimes C_e,\qquad C\big((y_1,y_2),(z_1,z_2)\big)=\frac1{|E|}\sum_{e\in E}C_e(y_1,z_1)\,C_e(y_2,z_2).
--   $$
--   The antisymmetric subspace is $\mathcal H_{\mathrm{Asym}}=\{f:V\times V\to\mathbb R:\ f(y,z)=-f(z,y)\}$, and $\lambda_1(C|_{\mathcal H_{\mathrm{Asym}}})$ is the largest absolute value of an eigenvalue of $C$ restricted to $\mathcal H_{\mathrm{Asym}}$:
--   $$
--   \lambda_1(C|_{\mathcal H_{\mathrm{Asym}}})=\sup\{|\lambda|:\ Cf=\lambda f\text{ for some }f\in\mathcal H_{\mathrm{Asym}},\ f\neq0\}.
--   $$
--
--   This is the antisymmetric block in the spectral decomposition of the two-particle labeled chain (Proposition A.5).
--
--   **Formalization Note** $V\times V$ is `Fin d × Fin d`; the edge average runs over pairs $(a,b)$ with $a<b$. $\mathcal H_{\mathrm{Asym}}$ is invariant under $C$, so the eigenvalues of the restriction are those with an antisymmetric eigenfunction. The set is finite and, for $d\ge2$, nonempty, so the supremum is a maximum.
-- source:
--   Chen et al., arXiv:2609.38044, §A.1, p.61 (PDF p.63); C_e and C, p.64 (PDF p.66); Lemma A.4, p.65; Proposition A.5, p.66

import Mathlib
import Definitions.Def_KMPMixing_kmpChain

namespace KMPMixing

/-- The matrix `C_e` of Appendix A (arXiv:2609.38044, pp.64–65 (PDF pp.66–67), and Eq. (44),
p.67 (PDF p.69)) for an edge `e = {a, b}`: `C_e(y, z) = 1/2` if `y, z ∈ {a, b}`, `1` if
`y = z ∉ {a, b}`, and `0` otherwise. It is `E_p[A_{e,p}]`, the single-particle step on `e`
averaged over `p ∼ Unif[0, 1]`. -/
noncomputable def edgeAvgMatrix {d : ℕ} (a b : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  fun y z =>
    if (y = a ∨ y = b) ∧ (z = a ∨ z = b) then 1 / 2
    else if y = z ∧ ¬ (y = a ∨ y = b) then 1 else 0

/-- The matrix `C = (1/|E|) Σ_{e ∈ E} C_e ⊗ C_e` on functions of `V × V` (arXiv:2609.38044,
Lemma A.4, pp.64–65 (PDF pp.66–67)):
`C((y₁, y₂), (z₁, z₂)) = (1/|E|) Σ_e C_e(y₁, z₁) · C_e(y₂, z₂)`.

**Formalization Note** `V × V` is `Fin d × Fin d`; the average runs over `edgePairs G`. -/
noncomputable def twoParticleC {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj] :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℝ :=
  fun y z => ((edgePairs G).card : ℝ)⁻¹ *
    ∑ p ∈ edgePairs G, edgeAvgMatrix p.1 p.2 y.1 z.1 * edgeAvgMatrix p.1 p.2 y.2 z.2

/-- `𝓗_Asym = {f : V × V → ℝ : f(y, z) = −f(z, y) ∀ y, z}`, the antisymmetric functions
(arXiv:2609.38044, §A.1, p.61 (PDF p.63)). -/
def IsAntisymmetric {d : ℕ} (f : Fin d × Fin d → ℝ) : Prop :=
  ∀ y z : Fin d, f (y, z) = - f (z, y)

/-- `λ₁(C|_{𝓗_Asym})`, the largest eigenvalue in absolute value of the restriction of `C` to the
antisymmetric subspace (arXiv:2609.38044, Proposition A.5 and the sentence before it, p.66
(PDF p.68)): the supremum of `|λ|` over the eigenvalues `λ` of `C` that have an antisymmetric
eigenfunction.

**Formalization Note** `𝓗_Asym` is invariant under `C` (Lemma A.2), so the eigenvalues of the
restriction are exactly the `λ` with `C f = λ f` for some nonzero antisymmetric `f`. The set is
finite (eigenvalues of a finite matrix), so the real `sSup` is a maximum when the set is
nonempty, which holds for `d ≥ 2`. -/
noncomputable def lambdaOneAsym {d : ℕ} (G : SimpleGraph (Fin d)) [DecidableRel G.Adj] : ℝ :=
  sSup {r : ℝ | ∃ lam : ℝ, ∃ f : Fin d × Fin d → ℝ, f ≠ 0 ∧ IsAntisymmetric f ∧
    (twoParticleC G).mulVec f = lam • f ∧ r = |lam|}

end KMPMixing


