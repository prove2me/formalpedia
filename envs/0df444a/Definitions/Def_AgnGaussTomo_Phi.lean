-- Prove2me | Definitions.Def_AgnGaussTomo_Phi
-- name    : AgnGaussTomo_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:35.461619+00:00
-- url     : https://prove2.me/theorems/9eb3a53a-7b7c-4f70-87c2-4311439d4840
-- title:
--   Unnormalized Bargmann vector $|\Phi(b,A)\rangle=e^{K_\theta}|0\rangle$
-- statement:
--   For $\theta=(b,A)\in\mathcal P_n$ let
--
--   $$
--   |\Phi(b,A)\rangle=\exp\Big(\sum_i b_i\hat a_i^\dagger+\tfrac12\sum_{i,j}A_{ij}\hat a_i^\dagger\hat a_j^\dagger\Big)|0\rangle ,
--   $$
--
--   whose Bargmann function is $f(z)=\exp(b^\top z+\tfrac12z^\top Az)$. Under the identification $|m\rangle\leftrightarrow z^m/\sqrt{m!}$ (Definition 2.3) the Fock coefficients are
--
--   $$
--   \Phi_m(\theta)=\sqrt{m!}\,[z^m]\exp\big(b^\top z+\tfrac12 z^\top Az\big),\qquad m!=\prod_i m_i!,
--   $$
--
--   for instance $\Phi_0=1$, $\Phi_{e_i}=b_i$, $\Phi_{e_i+e_j}=A_{ij}+b_ib_j$ for $i\ne j$, and $\Phi_{2e_i}=(A_{ii}+b_i^2)/\sqrt2$ (Eq. (6)).
--
--   **Formalization Note** The coefficient of $z^m$ is computed in `MvPolynomial (Fin n) ℂ` as $\sum_{k\le|m|}\frac1{k!}[z^m](b^\top z+\tfrac12z^\top Az)^k$ (higher powers do not contribute). The vector is square-summable exactly when $\|A\|_{\mathrm{op}}<1$. The values $\Phi_m(0)=[m=0]$ and, for one mode, $\Phi_{e_1}=b_1$ are checked in the verification file.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Definition 2.3 and Fact 2.4, Eqs. (5)–(6), printed p. 11 (PDF p. 14)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Definitions.Def_AgnGaussTomo_Pspace

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **Fock coefficients of the unnormalized Bargmann vector `|Φ(b, A)⟩ = exp(Σᵢ bᵢ âᵢ† + ½ Σᵢⱼ Aᵢⱼ âᵢ†âⱼ†)|0⟩`.**
Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810
(version of 3 Nov 2026), Definition 2.3 and Fact 2.4, Eqs. (5)–(6), printed p. 11 (PDF p. 14):
the Bargmann function of `|Φ(b, A)⟩` is `f(z) = exp(bᵀz + ½ zᵀAz)` and Fock states correspond to
monomials, "|k₁k₂…kₙ⟩ ↔ z₁^{k₁}…zₙ^{kₙ}/√(k₁!…kₙ!)".

So the coefficient of `|m⟩` is `√(m!) · [z^m] exp(bᵀz + ½ zᵀAz)`, with `m! = Πᵢ mᵢ!`. Since the
exponent has no constant term, only the powers `k ≤ |m| = Σᵢ mᵢ` of it contribute:

  `Φ_m = √(m!) Σ_{k ≤ |m|} (1/k!) [z^m] (Σᵢ bᵢ zᵢ + ½ Σᵢⱼ Aᵢⱼ zᵢ zⱼ)^k`.

For example `Φ₀ = 1`, `Φ_{e_i} = b_i`, `Φ_{e_i+e_j} = A_ij + b_i b_j` (`i ≠ j`) and
`Φ_{2e_i} = (A_ii + b_i²)/√2`, as in Eq. (6).

**Formalization Note.** `(b, A)` are read off `θ : Pspace n` by `Pspace.b`, `Pspace.A`. The
coefficient is taken in `MvPolynomial (Fin n) ℂ`, with the occupation `m : Fin n → ℕ` turned into
the exponent `Finsupp`. Defined for every `θ`; it is a Fock vector (square-summable) iff
`‖A‖_op < 1`. -/
noncomputable def Phi {n : ℕ} (θ : Pspace n) (m : Occupation (Fin n)) : ℂ :=
  (Real.sqrt (∏ i, ((m i).factorial : ℝ)) : ℂ) *
    ∑ k ∈ Finset.range (∑ i, m i + 1), ((k.factorial : ℂ))⁻¹ *
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm m)
        ((∑ i, MvPolynomial.C (Pspace.b θ i) * MvPolynomial.X i +
          MvPolynomial.C (1 / 2 : ℂ) * ∑ i, ∑ j,
            MvPolynomial.C (Pspace.A θ i j) * MvPolynomial.X i * MvPolynomial.X j) ^ k)

end AgnGaussTomo


